# NOTE: YOU CAN NOT USE USER TOKENS. YOU MUST USE APP TOKENS PROVIDED BY THE DISCORD DEVELOPER PORTAL.
from __future__ import annotations

import asyncio
import contextlib
import hashlib
import html
import json
import os
import re
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Awaitable, Callable, Literal, Optional
from urllib.parse import urlsplit

import aiohttp
import discord
import keyring
from keyring.errors import KeyringError, PasswordDeleteError
from PySide6.QtCore import QEvent, Qt
from PySide6.QtGui import QColor, QCloseEvent, QIcon, QPainter, QPainterPath, QPixmap, QTextCursor
from PySide6.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QFileDialog,
    QHBoxLayout,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QTextBrowser,
    QVBoxLayout,
    QWidget,
)
from qasync import QEventLoop, asyncSlot

IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp"}
VIDEO_SUFFIXES = {".mp4", ".mov", ".webm", ".mkv", ".avi", ".m4v"}
AUDIO_SUFFIXES = {".mp3", ".wav", ".ogg", ".m4a", ".flac", ".aac"}
TEXT_SUFFIXES = {
    ".txt",
    ".md",
    ".json",
    ".csv",
    ".log",
    ".py",
    ".js",
    ".ts",
    ".html",
    ".css",
    ".xml",
    ".yml",
    ".yaml",
    ".toml",
    ".ini",
}
DOCUMENT_SUFFIXES = {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".rtf", ".odt", ".ods", ".odp"}
ARCHIVE_SUFFIXES = {".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz"}
DOCUMENT_MIME_TYPES = {
    "application/pdf",
    "application/msword",
    "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
    "application/vnd.ms-excel",
    "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
    "application/vnd.ms-powerpoint",
    "application/vnd.openxmlformats-officedocument.presentationml.presentation",
    "application/rtf",
}
ARCHIVE_MIME_TYPES = {
    "application/zip",
    "application/x-rar-compressed",
    "application/x-7z-compressed",
    "application/x-tar",
    "application/gzip",
    "application/x-bzip2",
    "application/x-xz",
}
MAX_ATTACHMENTS_PER_MESSAGE = 10
AVATAR_SIZE_PX = 28
MENTION_AVATAR_SIZE_PX = 20
MENTION_QUERY_PATTERN = re.compile(r"(^|[\s\(\[\{])@([^\s@<>]{0,64})$")


class SymphonyError(Exception):
    """Base exception for Symphony Alpha."""


class TokenStoreError(SymphonyError):
    """Raised when keychain operations fail."""


class AuthenticationError(SymphonyError):
    """Raised when Discord Application token authentication fails."""


class DiscordServiceError(SymphonyError):
    """Raised for Discord connectivity and API operation issues."""


def env_flag_enabled(name: str) -> bool:
    value = os.getenv(name, "").strip().lower()
    return value in {"1", "true", "yes", "on"}


@dataclass(frozen=True)
class ResolvedUserCandidate:
    user_id: int
    username: str
    display_name: str
    tag: str
    guild_id: Optional[int]
    guild_name: Optional[str]
    source: Literal["cache", "guild_search", "gateway_query"]
    match_quality: int


@dataclass(frozen=True)
class MentionSuggestion:
    mention_text: str
    display_text: str
    search_texts: tuple[str, ...]
    kind: Literal["user", "role"]
    entity_id: int
    avatar_url: Optional[str] = None


@dataclass(frozen=True)
class DMChannelCache:
    """
    Persists known DM channel IDs/labels in JSON.
    Stores channels only (no message content, no token).
    """

    path: Path = Path(__file__).with_name("symphony_alpha_dm_channels.json")

    def _read_payload(self) -> dict:
        if not self.path.exists():
            return {"version": 1, "accounts": {}}

        try:
            payload = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return {"version": 1, "accounts": {}}

        if not isinstance(payload, dict):
            return {"version": 1, "accounts": {}}

        accounts = payload.get("accounts")
        if not isinstance(accounts, dict):
            accounts = {}

        return {"version": 1, "accounts": accounts}

    def _write_payload(self, payload: dict) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp_path = self.path.with_suffix(self.path.suffix + ".tmp")
        tmp_path.write_text(
            json.dumps(payload, indent=2, ensure_ascii=True), encoding="utf-8"
        )
        tmp_path.replace(self.path)

    async def load_channels(self, account_id: int) -> dict[int, str]:
        return await asyncio.to_thread(self._load_channels_sync, account_id)

    def _load_channels_sync(self, account_id: int) -> dict[int, str]:
        payload = self._read_payload()
        accounts = payload["accounts"]
        account_payload = accounts.get(str(account_id))
        if not isinstance(account_payload, dict):
            return {}

        channels = account_payload.get("channels")
        if not isinstance(channels, dict):
            return {}

        parsed: dict[int, str] = {}
        for channel_id_raw, label_raw in channels.items():
            try:
                channel_id = int(channel_id_raw)
            except (TypeError, ValueError):
                continue
            if not isinstance(label_raw, str):
                continue
            label = label_raw.strip()
            if not label:
                continue
            parsed[channel_id] = label
        return parsed

    async def save_channels(self, account_id: int, channels: dict[int, str]) -> None:
        await asyncio.to_thread(self._save_channels_sync, account_id, channels)

    def _save_channels_sync(self, account_id: int, channels: dict[int, str]) -> None:
        payload = self._read_payload()
        accounts = payload["accounts"]

        serialized_channels = {
            str(channel_id): label
            for channel_id, label in channels.items()
            if isinstance(channel_id, int) and isinstance(label, str) and label.strip()
        }

        accounts[str(account_id)] = {"channels": serialized_channels}
        self._write_payload(payload)


@dataclass(frozen=True)
class TokenStore:
    """
    Stores the Discord Application token in the OS keychain.
    The token is never written to disk by this application.
    """

    service_name: str = "Symphony Alpha"
    account_name: str = "discord_application_token"

    async def load_token(self) -> Optional[str]:
        try:
            return await asyncio.to_thread(
                keyring.get_password, self.service_name, self.account_name
            )
        except KeyringError as exc:
            raise TokenStoreError("Unable to read the OS keychain.") from exc

    async def save_token(self, token: str) -> None:
        try:
            await asyncio.to_thread(
                keyring.set_password, self.service_name, self.account_name, token
            )
        except KeyringError as exc:
            raise TokenStoreError("Unable to save token to the OS keychain.") from exc

    async def clear_token(self) -> None:
        try:
            await asyncio.to_thread(
                keyring.delete_password, self.service_name, self.account_name
            )
        except PasswordDeleteError:
            # Token was not present; nothing to clear.
            return
        except KeyringError as exc:
            raise TokenStoreError("Unable to remove token from the OS keychain.") from exc


def normalize_token(raw_token: str) -> str:
    """
    Normalizes token input without logging it.
    Accepts pasted values with optional leading 'Bot ' prefix.
    """

    token = raw_token.strip()
    if len(token) >= 2 and token[0] == token[-1] and token[0] in {"'", '"', "`"}:
        token = token[1:-1].strip()
    if token.lower().startswith("bot "):
        token = token[4:].strip()
    # Remove accidental whitespace/newlines added by copy/paste.
    token = "".join(token.split())
    return token


def token_shape_error(token: str) -> Optional[str]:
    """
    Fast local validation for obvious copy/paste issues.
    """

    lowered = token.lower()
    if "..." in token or "[redacted]" in lowered or "(redacted)" in lowered:
        return "Token appears redacted or truncated. Paste the full Application token."

    parts = token.split(".")
    if len(parts) != 3 or any(not part for part in parts):
        return "Token format looks invalid. Paste the full Application token from Discord."

    return None


class DiscordGatewayClient(discord.Client):
    """
    Discord client that exposes lifecycle and message callbacks to the UI layer.
    """

    def __init__(
        self,
        *,
        message_callback: Optional[Callable[[discord.Message], Awaitable[None]]],
        typing_callback: Optional[
            Callable[[discord.abc.Messageable, discord.abc.User, object], Awaitable[None]]
        ],
        status_callback: Optional[Callable[[str], Awaitable[None]]],
        enable_members_intent: bool = False,
    ) -> None:
        intents = discord.Intents.default()
        intents.guilds = True
        intents.guild_messages = True
        intents.dm_messages = True
        intents.message_content = True
        intents.members = enable_members_intent
        super().__init__(intents=intents)

        self.ready_event = asyncio.Event()
        self.received_dm_channel_ids: set[int] = set()
        self._message_callback = message_callback
        self._typing_callback = typing_callback
        self._status_callback = status_callback

    async def _emit_status(self, text: str) -> None:
        if self._status_callback is not None:
            await self._status_callback(text)

    async def on_ready(self) -> None:
        self.ready_event.set()
        await self._emit_status("Connected")

    async def on_disconnect(self) -> None:
        await self._emit_status("Disconnected. Reconnecting...")

    async def on_resumed(self) -> None:
        await self._emit_status("Connection resumed")

    async def on_message(self, message: discord.Message) -> None:
        if isinstance(message.channel, discord.DMChannel):
            self.received_dm_channel_ids.add(message.channel.id)
        if self._message_callback is not None:
            await self._message_callback(message)

    async def on_typing(
        self,
        channel: discord.abc.Messageable,
        user: discord.abc.User,
        when: object,
    ) -> None:
        if self._typing_callback is not None:
            await self._typing_callback(channel, user, when)


class DiscordService:
    """
    Async wrapper for discord.py client lifecycle and message operations.
    """

    def __init__(
        self,
        *,
        message_callback: Optional[Callable[[discord.Message], Awaitable[None]]] = None,
        typing_callback: Optional[Callable[[int, str, bool], Awaitable[None]]] = None,
        status_callback: Optional[Callable[[str], Awaitable[None]]] = None,
        enable_members_intent: bool = False,
    ) -> None:
        self._ui_message_callback = message_callback
        self._ui_typing_callback = typing_callback
        self._status_callback = status_callback
        self._enable_members_intent = enable_members_intent
        self._client: Optional[DiscordGatewayClient] = None
        self._gateway_task: Optional[asyncio.Task[None]] = None
        self._session_token: Optional[str] = None
        self._session_account_id: Optional[int] = None
        self._known_dm_channel_labels: dict[int, str] = {}
        self._dm_channel_cache = DMChannelCache()

    def _require_client(self) -> DiscordGatewayClient:
        if self._client is None:
            raise DiscordServiceError("Not connected to Discord.")
        return self._client

    async def _emit_status(self, text: str) -> None:
        if self._status_callback is not None:
            await self._status_callback(text)

    def _handle_gateway_task_done(self, task: asyncio.Task[None]) -> None:
        if task.cancelled():
            return
        exception = task.exception()
        if exception is None:
            return
        # Keep task exceptions observed and forward a generic UI status update.
        if self._status_callback is not None:
            try:
                asyncio.create_task(self._status_callback("Gateway stopped unexpectedly."))
            except RuntimeError:
                # Event loop is shutting down.
                return

    def _label_for_user(self, user: discord.abc.User) -> str:
        display_name = getattr(user, "global_name", None) or user.name
        return f"@{display_name}"

    def _user_fields(self, user: discord.User | discord.Member) -> list[str]:
        fields = [user.name.lower(), str(user).lower()]
        global_name = getattr(user, "global_name", None)
        if global_name:
            fields.append(global_name.lower())
        if isinstance(user, discord.Member):
            fields.append(user.display_name.lower())
        return fields

    def _match_quality(self, needle: str, fields: list[str]) -> Optional[int]:
        if any(field == needle for field in fields):
            return 0
        if any(field.startswith(needle) for field in fields):
            return 1
        if any(needle in field for field in fields):
            return 2
        return None

    def _tag_from_parts(self, username: str, discriminator: Optional[str]) -> str:
        if discriminator and discriminator != "0":
            return f"{username}#{discriminator}"
        return username

    def _candidate_from_user(
        self,
        user: discord.User | discord.Member,
        *,
        source: Literal["cache", "guild_search", "gateway_query"],
        match_quality: int,
        guild_id: Optional[int] = None,
        guild_name: Optional[str] = None,
    ) -> ResolvedUserCandidate:
        display_name = getattr(user, "display_name", None) or getattr(user, "global_name", None) or user.name
        if isinstance(user, discord.Member):
            guild_id = user.guild.id
            guild_name = user.guild.name

        return ResolvedUserCandidate(
            user_id=user.id,
            username=user.name,
            display_name=display_name,
            tag=str(user),
            guild_id=guild_id,
            guild_name=guild_name,
            source=source,
            match_quality=match_quality,
        )

    def _candidate_from_member_payload(
        self,
        member_payload: dict,
        *,
        guild_id: int,
        guild_name: str,
        needle: str,
        source: Literal["guild_search", "gateway_query"],
    ) -> Optional[ResolvedUserCandidate]:
        user_payload = member_payload.get("user")
        if not isinstance(user_payload, dict):
            return None

        raw_id = user_payload.get("id")
        username = user_payload.get("username")
        if not isinstance(raw_id, str) or not isinstance(username, str):
            return None

        try:
            user_id = int(raw_id)
        except ValueError:
            return None

        global_name = user_payload.get("global_name")
        nick = member_payload.get("nick")
        display_name = username
        if isinstance(global_name, str) and global_name.strip():
            display_name = global_name
        if isinstance(nick, str) and nick.strip():
            display_name = nick
        discriminator = user_payload.get("discriminator")
        if not isinstance(discriminator, str):
            discriminator = None
        tag = self._tag_from_parts(username, discriminator)

        fields = [username.lower(), tag.lower()]
        if isinstance(global_name, str) and global_name.strip():
            fields.append(global_name.lower())
        if isinstance(nick, str) and nick.strip():
            fields.append(nick.lower())

        match_quality = self._match_quality(needle, fields)
        if match_quality is None:
            return None

        return ResolvedUserCandidate(
            user_id=user_id,
            username=username,
            display_name=display_name,
            tag=tag,
            guild_id=guild_id,
            guild_name=guild_name,
            source=source,
            match_quality=match_quality,
        )

    async def _search_guild_members_rest(
        self,
        session: aiohttp.ClientSession,
        *,
        guild_id: int,
        guild_name: str,
        query: str,
        limit: int,
    ) -> list[ResolvedUserCandidate]:
        token = self._session_token
        if token is None:
            return []

        url = f"https://discord.com/api/v10/guilds/{guild_id}/members/search"
        headers = {
            "Authorization": f"Bot {token}",
            "User-Agent": "DiscordBot (SymphonyAlpha, 1.0)",
        }
        params = {
            "query": query,
            "limit": str(max(1, min(limit, 1000))),
        }
        needle = query.strip().lstrip("@").lower()

        for attempt in range(2):
            try:
                async with session.get(url, headers=headers, params=params) as response:
                    if response.status == 200:
                        payload = await response.json(content_type=None)
                    elif response.status in {403, 404}:
                        return []
                    elif response.status == 429 and attempt == 0:
                        retry_after = 0.0
                        with contextlib.suppress(Exception):
                            rate_payload = await response.json(content_type=None)
                            if isinstance(rate_payload, dict):
                                raw_retry = rate_payload.get("retry_after")
                                if isinstance(raw_retry, (int, float)):
                                    retry_after = float(raw_retry)
                        if retry_after <= 0:
                            with contextlib.suppress(Exception):
                                retry_after = float(response.headers.get("Retry-After", "0"))
                        if retry_after > 0:
                            await asyncio.sleep(retry_after)
                        continue
                    else:
                        return []
            except Exception:
                return []

            if not isinstance(payload, list):
                return []

            candidates: list[ResolvedUserCandidate] = []
            for item in payload:
                if not isinstance(item, dict):
                    continue
                candidate = self._candidate_from_member_payload(
                    item,
                    guild_id=guild_id,
                    guild_name=guild_name,
                    needle=needle,
                    source="guild_search",
                )
                if candidate is not None:
                    candidates.append(candidate)
            return candidates

        return []

    async def _query_guild_members_gateway(
        self,
        *,
        guild_id: int,
        guild_name: str,
        query: str,
        limit: int,
    ) -> list[ResolvedUserCandidate]:
        client = self._require_client()
        guild = client.get_guild(guild_id)
        if guild is None:
            return []

        try:
            members = await guild.query_members(
                query=query,
                limit=max(1, min(limit, 100)),
                cache=True,
            )
        except (
            asyncio.TimeoutError,
            ValueError,
            discord.ClientException,
            discord.Forbidden,
            discord.HTTPException,
        ):
            return []

        needle = query.strip().lstrip("@").lower()
        candidates: list[ResolvedUserCandidate] = []
        for member in members:
            match_quality = self._match_quality(needle, self._user_fields(member))
            if match_quality is None:
                continue
            candidates.append(
                self._candidate_from_user(
                    member,
                    source="gateway_query",
                    match_quality=match_quality,
                    guild_id=guild_id,
                    guild_name=guild_name,
                )
            )
        return candidates

    def _set_known_dm_label(self, channel_id: int, label: str) -> bool:
        clean = label.strip()
        if not clean:
            return False
        if self._known_dm_channel_labels.get(channel_id) == clean:
            return False
        self._known_dm_channel_labels[channel_id] = clean
        return True

    async def _persist_known_dm_channels(self) -> None:
        account_id = self._session_account_id
        if account_id is None:
            return
        try:
            await self._dm_channel_cache.save_channels(account_id, self._known_dm_channel_labels)
        except Exception:
            # Persistence should never block normal chat operations.
            return

    def _schedule_persist_known_dm_channels(self) -> None:
        try:
            loop = asyncio.get_running_loop()
        except RuntimeError:
            return
        loop.create_task(self._persist_known_dm_channels())

    async def _handle_discord_message(self, message: discord.Message) -> None:
        if isinstance(message.channel, discord.DMChannel):
            changed = self._set_known_dm_label(
                message.channel.id, self._label_for_user(message.author)
            )
            if changed:
                await self._persist_known_dm_channels()

        if self._ui_message_callback is not None:
            await self._ui_message_callback(message)

    async def _handle_discord_typing(
        self,
        channel: discord.abc.Messageable,
        user: discord.abc.User,
        when: object,
    ) -> None:
        client = self._client
        if client is None or client.user is None:
            return
        if user.id == client.user.id:
            return
        if self._ui_typing_callback is None:
            return

        channel_id = getattr(channel, "id", None)
        if not isinstance(channel_id, int):
            return

        display_name = getattr(user, "global_name", None) or user.name
        is_dm = isinstance(channel, discord.DMChannel)
        await self._ui_typing_callback(channel_id, display_name, is_dm)

    async def _sync_known_dm_channels(self, token: str) -> None:
        """
        Seeds DM channel IDs from Discord's DM channel listing endpoint.
        Message history stays lazy-loaded when a channel is selected.
        """

        url = "https://discord.com/api/v10/users/@me/channels"
        headers = {
            "Authorization": f"Bot {token}",
            "User-Agent": "DiscordBot (SymphonyAlpha, 1.0)",
        }

        try:
            timeout = aiohttp.ClientTimeout(total=15)
            async with aiohttp.ClientSession(timeout=timeout) as session:
                async with session.get(url, headers=headers) as response:
                    if response.status != 200:
                        return
                    payload = await response.json(content_type=None)
        except Exception:
            # Do not block login on DM sync failures.
            return

        if not isinstance(payload, list):
            return

        for item in payload:
            if not isinstance(item, dict):
                continue
            if item.get("type") != 1:
                # type 1 = direct message channel
                continue

            raw_channel_id = item.get("id")
            try:
                channel_id = int(raw_channel_id)
            except (TypeError, ValueError):
                continue

            label = f"DM {channel_id}"
            recipients = item.get("recipients")
            if isinstance(recipients, list) and recipients:
                recipient = recipients[0]
                if isinstance(recipient, dict):
                    username = recipient.get("global_name") or recipient.get("username")
                    if isinstance(username, str) and username.strip():
                        label = f"@{username.strip()}"

            self._set_known_dm_label(channel_id, label)

    async def login(self, raw_token: str) -> None:
        token = normalize_token(raw_token)
        if not token:
            raise AuthenticationError("Please enter an Application token.")
        shape_error = token_shape_error(token)
        if shape_error is not None:
            raise AuthenticationError(shape_error)

        await self.logout()
        await self._emit_status("Connecting...")

        client = DiscordGatewayClient(
            message_callback=self._handle_discord_message,
            typing_callback=self._handle_discord_typing,
            status_callback=self._status_callback,
            enable_members_intent=self._enable_members_intent,
        )

        try:
            await client.login(token)
        except discord.LoginFailure as exc:
            raise AuthenticationError("Invalid token.") from exc
        except discord.HTTPException as exc:
            if exc.status == 401:
                raise AuthenticationError("Invalid token.") from exc
            raise DiscordServiceError(
                "Discord API request failed while validating the token."
            ) from exc

        if client.user is None:
            with contextlib.suppress(Exception):
                await client.close()
            raise DiscordServiceError(
                "Discord did not return account details. Please try logging in again."
            )

        self._session_account_id = client.user.id
        self._session_token = token
        cached_channels = await self._dm_channel_cache.load_channels(self._session_account_id)
        self._known_dm_channel_labels.update(cached_channels)
        await self._sync_known_dm_channels(token)
        await self._persist_known_dm_channels()

        self._client = client
        self._gateway_task = asyncio.create_task(
            client.connect(reconnect=True), name="discord_gateway"
        )
        self._gateway_task.add_done_callback(self._handle_gateway_task_done)

        ready_task = asyncio.create_task(client.ready_event.wait())
        done, pending = await asyncio.wait(
            {ready_task, self._gateway_task},
            timeout=30,
            return_when=asyncio.FIRST_COMPLETED,
        )

        if ready_task in done and client.ready_event.is_set():
            return

        for task in pending:
            task.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await task

        failure_message = "Timed out connecting to the Discord gateway."
        if self._gateway_task in done:
            gateway_exception = self._gateway_task.exception()
            if gateway_exception is not None:
                code = getattr(gateway_exception, "code", None)
                if isinstance(gateway_exception, discord.PrivilegedIntentsRequired) or code == 4014:
                    if self._enable_members_intent:
                        failure_message = (
                            "Gateway rejected requested intents. Enable Message Content and "
                            "Server Members intents in the Discord Developer Portal, or disable "
                            "SYMPHONY_ENABLE_GUILD_MEMBERS_INTENT."
                        )
                    else:
                        failure_message = (
                            "Gateway rejected requested intents. Enable the Message Content intent "
                            "for your Application in the Discord Developer Portal."
                        )
                else:
                    failure_message = "Failed to connect to the Discord gateway."

        await self.logout()
        raise DiscordServiceError(failure_message)

    async def logout(self) -> None:
        gateway_task = self._gateway_task
        client = self._client
        self._gateway_task = None
        self._client = None
        self._session_token = None
        self._session_account_id = None
        self._known_dm_channel_labels = {}

        if client is not None:
            with contextlib.suppress(Exception):
                await client.close()

        if gateway_task is not None:
            if not gateway_task.done():
                gateway_task.cancel()
            with contextlib.suppress(asyncio.CancelledError, Exception):
                await gateway_task

    def get_guilds(self) -> list[discord.Guild]:
        if self._client is None:
            return []
        return sorted(self._client.guilds, key=lambda guild: guild.name.lower())

    def get_dm_channels(self) -> list[discord.DMChannel]:
        if self._client is None:
            return []

        channels: list[discord.DMChannel] = [
            channel
            for channel in self._client.private_channels
            if isinstance(channel, discord.DMChannel)
        ]
        channels.sort(
            key=lambda channel: (
                (channel.recipient.name.lower() if channel.recipient is not None else ""),
                channel.id,
            )
        )

        for channel in channels:
            if channel.recipient is not None:
                changed = self._set_known_dm_label(
                    channel.id, self._label_for_user(channel.recipient)
                )
            else:
                changed = self._set_known_dm_label(channel.id, f"DM {channel.id}")
            if changed:
                self._schedule_persist_known_dm_channels()

        return channels

    def get_known_dm_channels(self) -> list[tuple[int, str]]:
        # Refresh known labels with any currently cached private channels.
        self.get_dm_channels()
        return sorted(
            self._known_dm_channel_labels.items(), key=lambda item: item[1].lower()
        )

    async def refresh_known_dm_channels(self) -> None:
        token = self._session_token
        if token is None:
            return
        await self._sync_known_dm_channels(token)
        await self._persist_known_dm_channels()

    def get_connection_checks(self) -> dict[str, int]:
        """
        Lightweight account checks for UI diagnostics.
        """

        client = self._client
        if client is None:
            return {"guild_count": 0, "dm_channel_count": 0, "received_dm_count": 0}

        known_dm_ids = {channel_id for channel_id, _ in self.get_known_dm_channels()}
        received_dm_ids = set(client.received_dm_channel_ids)
        for channel in self.get_dm_channels():
            last_message_id = getattr(channel, "last_message_id", None)
            if last_message_id is not None:
                received_dm_ids.add(channel.id)

        return {
            "guild_count": len(client.guilds),
            "dm_channel_count": len(known_dm_ids),
            "received_dm_count": len(received_dm_ids),
        }

    def parse_user_id_input(self, query: str) -> Optional[int]:
        text = query.strip()
        if not text:
            return None

        if text.isdigit():
            return int(text)

        if text.startswith("<@") and text.endswith(">"):
            inner = text[2:-1].strip()
            if inner.startswith("!"):
                inner = inner[1:]
            if inner.isdigit():
                return int(inner)

        return None

    def get_lookup_guilds(self) -> list[tuple[int, str]]:
        return [(guild.id, guild.name) for guild in self.get_guilds()]

    def find_users_by_name(
        self, query: str, *, limit: int = 25
    ) -> list[discord.User | discord.Member]:
        """
        Finds users from the local cache by username/display name/tag.
        """

        client = self._require_client()
        needle = query.strip().lstrip("@").lower()

        candidates: dict[int, discord.User | discord.Member] = {}
        for user in client.users:
            candidates[user.id] = user

        for channel in client.private_channels:
            if isinstance(channel, discord.DMChannel) and channel.recipient is not None:
                candidates[channel.recipient.id] = channel.recipient

        # Guild member caches may be partial without the Members intent.
        for guild in client.guilds:
            for member in guild.members:
                candidates[member.id] = member

        if not needle:
            ordered = sorted(
                candidates.values(),
                key=lambda user: (
                    (
                        getattr(user, "display_name", None)
                        or getattr(user, "global_name", None)
                        or user.name
                    ).lower(),
                    user.id,
                ),
            )
            return ordered[:limit]

        scored: list[tuple[int, str, discord.User | discord.Member]] = []
        for user in candidates.values():
            score = self._match_quality(needle, self._user_fields(user))
            if score is None:
                continue

            display = getattr(user, "display_name", None) or getattr(user, "global_name", None) or user.name
            scored.append((score, display.lower(), user))

        scored.sort(key=lambda item: (item[0], item[1], item[2].id))
        return [item[2] for item in scored[:limit]]

    async def resolve_users_for_dm(
        self,
        query: str,
        *,
        guild_ids: Optional[list[int]] = None,
        limit: int = 50,
        per_guild_limit: int = 25,
    ) -> list[ResolvedUserCandidate]:
        client = self._require_client()
        text_query = query.strip()
        lookup_query = text_query.lstrip("@")
        needle = lookup_query.lower()
        if not needle:
            return []

        total_limit = max(1, min(limit, 200))
        per_guild_limit = max(1, min(per_guild_limit, 1000))
        source_priority = {"cache": 0, "guild_search": 1, "gateway_query": 2}

        guild_map = {guild.id: guild for guild in client.guilds}
        if guild_ids is None:
            target_guild_ids = [guild.id for guild in client.guilds]
            selected_scope_ids: set[int] = set()
        else:
            seen: set[int] = set()
            target_guild_ids = []
            for guild_id in guild_ids:
                if guild_id in guild_map and guild_id not in seen:
                    seen.add(guild_id)
                    target_guild_ids.append(guild_id)
            selected_scope_ids = set(target_guild_ids)

        candidates: list[ResolvedUserCandidate] = []

        cache_matches = self.find_users_by_name(lookup_query, limit=max(total_limit, 50))
        for user in cache_matches:
            match_quality = self._match_quality(needle, self._user_fields(user))
            if match_quality is None:
                continue
            candidates.append(
                self._candidate_from_user(
                    user,
                    source="cache",
                    match_quality=match_quality,
                )
            )

        rest_candidates: list[ResolvedUserCandidate] = []
        if target_guild_ids and self._session_token:
            timeout = aiohttp.ClientTimeout(total=15)
            semaphore = asyncio.Semaphore(4)
            async with aiohttp.ClientSession(timeout=timeout) as session:

                async def run_guild_search(guild_id: int) -> list[ResolvedUserCandidate]:
                    guild = guild_map.get(guild_id)
                    if guild is None:
                        return []
                    async with semaphore:
                        return await self._search_guild_members_rest(
                            session,
                            guild_id=guild.id,
                            guild_name=guild.name,
                            query=lookup_query,
                            limit=per_guild_limit,
                        )

                tasks = [run_guild_search(guild_id) for guild_id in target_guild_ids]
                results = await asyncio.gather(*tasks, return_exceptions=True)

            for result in results:
                if isinstance(result, list):
                    rest_candidates.extend(result)

        candidates.extend(rest_candidates)

        if self._enable_members_intent and target_guild_ids and not rest_candidates:
            gateway_limit = min(per_guild_limit, 100)
            for guild_id in target_guild_ids:
                guild = guild_map.get(guild_id)
                if guild is None:
                    continue
                gateway_candidates = await self._query_guild_members_gateway(
                    guild_id=guild.id,
                    guild_name=guild.name,
                    query=lookup_query,
                    limit=gateway_limit,
                )
                candidates.extend(gateway_candidates)

        def candidate_sort_key(candidate: ResolvedUserCandidate) -> tuple[int, int, int, str, int]:
            selected_scope_rank = (
                0
                if selected_scope_ids and candidate.guild_id in selected_scope_ids
                else 1
            )
            return (
                candidate.match_quality,
                source_priority.get(candidate.source, 99),
                selected_scope_rank,
                candidate.display_name.lower(),
                candidate.user_id,
            )

        best_by_user_id: dict[int, ResolvedUserCandidate] = {}
        for candidate in candidates:
            current = best_by_user_id.get(candidate.user_id)
            if current is None or candidate_sort_key(candidate) < candidate_sort_key(current):
                best_by_user_id[candidate.user_id] = candidate

        ordered = sorted(best_by_user_id.values(), key=candidate_sort_key)
        return ordered[:total_limit]

    async def open_dm_with_user(self, user_id: int) -> discord.DMChannel:
        client = self._require_client()
        user = client.get_user(user_id)
        if user is None:
            try:
                user = await client.fetch_user(user_id)
            except discord.NotFound as exc:
                raise DiscordServiceError("User not found.") from exc
            except discord.Forbidden as exc:
                raise DiscordServiceError("Missing permission to fetch this user.") from exc
            except discord.HTTPException as exc:
                raise DiscordServiceError("Failed to fetch user details from Discord.") from exc

        try:
            channel = user.dm_channel or await user.create_dm()
        except discord.Forbidden as exc:
            raise DiscordServiceError("Cannot open DM with that user.") from exc
        except discord.HTTPException as exc:
            raise DiscordServiceError("Discord API rejected DM channel creation.") from exc

        self._set_known_dm_label(channel.id, self._label_for_user(user))
        await self._persist_known_dm_channels()
        return channel

    async def get_text_channels(self, guild_id: int) -> list[discord.TextChannel]:
        client = self._require_client()
        guild = client.get_guild(guild_id)
        if guild is None:
            return []

        me = guild.me
        channels: list[discord.TextChannel] = []
        for channel in guild.text_channels:
            if me is not None:
                perms = channel.permissions_for(me)
                if not perms.view_channel:
                    continue
            channels.append(channel)

        channels.sort(key=lambda channel: (channel.position, channel.name.lower()))
        return channels

    async def _resolve_message_channel(
        self, channel_id: int
    ) -> discord.TextChannel | discord.DMChannel | discord.Thread:
        client = self._require_client()
        channel = client.get_channel(channel_id)
        if channel is None:
            try:
                channel = await client.fetch_channel(channel_id)
            except discord.NotFound as exc:
                raise DiscordServiceError("Channel was not found.") from exc
            except discord.Forbidden as exc:
                raise DiscordServiceError("Missing permission to access this channel.") from exc
            except discord.HTTPException as exc:
                raise DiscordServiceError("Failed to fetch channel details from Discord.") from exc

        if not isinstance(channel, (discord.TextChannel, discord.DMChannel, discord.Thread)):
            raise DiscordServiceError("Selected channel is not a supported message channel.")
        return channel

    async def fetch_recent_messages(
        self, channel_id: int, limit: int = 50
    ) -> list[discord.Message]:
        channel = await self._resolve_message_channel(channel_id)
        try:
            # Fetch newest first from Discord, then reverse for chronological UI display.
            newest_first = [m async for m in channel.history(limit=limit, oldest_first=False)]
            newest_first.reverse()
            return newest_first
        except discord.Forbidden as exc:
            raise DiscordServiceError("Missing permission to read message history.") from exc
        except discord.HTTPException as exc:
            raise DiscordServiceError("Failed to fetch message history from Discord.") from exc

    async def send_message(
        self,
        channel_id: int,
        content: str = "",
        attachment_paths: Optional[list[Path]] = None,
    ) -> discord.Message:
        text_content = content.strip()
        attachments = attachment_paths or []
        if not text_content and not attachments:
            raise DiscordServiceError("Cannot send an empty message.")
        if len(attachments) > MAX_ATTACHMENTS_PER_MESSAGE:
            raise DiscordServiceError(
                f"Too many attachments selected (max {MAX_ATTACHMENTS_PER_MESSAGE} files per message)."
            )

        channel = await self._resolve_message_channel(channel_id)
        files: list[discord.File] = []
        try:
            for attachment_path in attachments:
                files.append(discord.File(str(attachment_path), filename=attachment_path.name))

            if files and text_content:
                return await channel.send(content=text_content, files=files)
            if files:
                return await channel.send(files=files)
            return await channel.send(text_content)
        except OSError as exc:
            raise DiscordServiceError("Failed to read one or more selected attachment files.") from exc
        except discord.Forbidden as exc:
            raise DiscordServiceError("Missing permission to send messages in this channel.") from exc
        except discord.HTTPException as exc:
            raise DiscordServiceError("Discord API rejected the message send request.") from exc
        finally:
            for file in files:
                with contextlib.suppress(Exception):
                    file.close()

    async def send_typing_indicator(self, channel_id: int) -> None:
        channel = await self._resolve_message_channel(channel_id)
        try:
            trigger_typing = getattr(channel, "trigger_typing", None)
            if callable(trigger_typing):
                await trigger_typing()
            else:
                async with channel.typing():
                    pass
        except discord.Forbidden as exc:
            raise DiscordServiceError("Missing permission to send typing indicator.") from exc
        except discord.HTTPException as exc:
            raise DiscordServiceError("Discord API rejected the typing indicator request.") from exc

    def get_current_user_id(self) -> Optional[int]:
        client = self._client
        if client is None or client.user is None:
            return None
        return client.user.id


class LoginWindow(QWidget):
    """
    Token entry window shown when no valid token is available in keychain.
    """

    def __init__(
        self,
        login_handler: Callable[[str], Awaitable[None]],
        parent: Optional[QWidget] = None,
    ) -> None:
        super().__init__(parent)
        self._login_handler = login_handler

        self.setWindowTitle("Symphony Alpha - Login")
        self.resize(500, 250)

        self.setStyleSheet(
            """
            QWidget {
                background-color: #0F1220;
                color: #E8ECF8;
            }
            QLabel#subtitleLabel {
                color: #AAB1CF;
            }
            QLabel#errorLabel {
                color: #FF6B7A;
                min-height: 20px;
            }
            QLineEdit {
                background-color: #171B2B;
                border: 1px solid #303756;
                border-radius: 8px;
                padding: 8px 10px;
                color: #F3F5FF;
                selection-background-color: #5865F2;
            }
            QLineEdit:focus {
                border-color: #5865F2;
            }
            QPushButton {
                background-color: #5865F2;
                border: 1px solid #6875FF;
                border-radius: 8px;
                padding: 8px 14px;
                color: #FFFFFF;
                font-weight: 600;
            }
            QPushButton:hover {
                background-color: #6472FF;
            }
            QPushButton:pressed {
                background-color: #505CE0;
            }
            QPushButton:disabled {
                background-color: #303756;
                border-color: #303756;
                color: #9AA1C2;
            }
            QProgressBar#authBusyBar {
                border: 1px solid #303756;
                border-radius: 6px;
                background-color: #101426;
                min-height: 12px;
                max-height: 12px;
            }
            QProgressBar#authBusyBar::chunk {
                background-color: #5865F2;
                border-radius: 5px;
                width: 24px;
                margin: 1px;
            }
            """
        )

        root = QVBoxLayout(self)
        root.setContentsMargins(16, 16, 16, 16)
        root.setSpacing(10)

        title = QLabel("Symphony Alpha")
        title.setStyleSheet("font-size: 20px; font-weight: 600;")

        subtitle = QLabel("Enter your Discord Application token.")
        subtitle.setObjectName("subtitleLabel")

        self.status_label = QLabel("")
        self.status_label.setObjectName("errorLabel")

        self.token_input = QLineEdit()
        self.token_input.setEchoMode(QLineEdit.Password)
        self.token_input.setPlaceholderText("Application token")
        self.token_input.returnPressed.connect(self._on_submit_clicked)

        self.login_button = QPushButton("Login")
        self.login_button.clicked.connect(self._on_submit_clicked)

        self.auth_busy_label = QLabel("Authorizing application...")
        self.auth_busy_label.setObjectName("subtitleLabel")
        self.auth_busy_label.hide()

        self.auth_busy_bar = QProgressBar()
        self.auth_busy_bar.setObjectName("authBusyBar")
        self.auth_busy_bar.setRange(0, 0)
        self.auth_busy_bar.setTextVisible(False)
        self.auth_busy_bar.setFixedWidth(260)
        self.auth_busy_bar.hide()

        root.addWidget(title)
        root.addWidget(subtitle)
        root.addWidget(self.token_input)
        root.addWidget(self.login_button)
        root.addWidget(self.auth_busy_label, 0, Qt.AlignHCenter)
        root.addWidget(self.auth_busy_bar, 0, Qt.AlignHCenter)
        root.addWidget(self.status_label)
        root.addStretch(1)

    def set_status(self, text: str) -> None:
        self.status_label.setText(text)

    def _set_busy(self, busy: bool) -> None:
        self.token_input.setEnabled(not busy)
        self.login_button.setEnabled(not busy)
        self.login_button.setText("Authorizing..." if busy else "Login")
        self.auth_busy_label.setVisible(busy)
        self.auth_busy_bar.setVisible(busy)

    def _show_error(self, title: str, text: str) -> None:
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Critical)
        box.setWindowTitle(title)
        box.setText(text)
        box.setStandardButtons(QMessageBox.Ok)
        box.setAttribute(Qt.WA_DeleteOnClose, True)
        box.open()

    @asyncSlot()
    async def _on_submit_clicked(self) -> None:
        raw_token = self.token_input.text()
        if not raw_token.strip():
            self.set_status("Please enter an Application token.")
            return

        self.set_status("")
        self._set_busy(True)
        try:
            await self._login_handler(raw_token)
        except AuthenticationError as exc:
            self._show_error("Login Failed", str(exc))
            self.set_status(str(exc))
        except (DiscordServiceError, TokenStoreError) as exc:
            self._show_error("Login Failed", str(exc))
            self.set_status(str(exc))
        finally:
            if self.isVisible():
                self._set_busy(False)


class MainWindow(QMainWindow):
    """
    Main Symphony Alpha window: guilds, channels, message history, and send box.
    """

    def __init__(
        self,
        discord_service: DiscordService,
        logout_handler: Callable[[], Awaitable[None]],
        parent: Optional[QWidget] = None,
    ) -> None:
        super().__init__(parent)
        self._discord_service = discord_service
        self._logout_handler = logout_handler

        self._displayed_message_ids: set[int] = set()
        self._load_channels_task: Optional[asyncio.Task[None]] = None
        self._load_messages_task: Optional[asyncio.Task[None]] = None
        self._add_dm_task: Optional[asyncio.Task[None]] = None
        self._dm_channel_labels: dict[int, str] = {}
        self._pending_attachment_paths: list[Path] = []
        self._typing_expirations: dict[int, dict[str, float]] = {}
        self._typing_cleanup_task: Optional[asyncio.Task[None]] = None
        self._typing_send_cooldown_until = 0.0
        self._image_cache_dir = Path(tempfile.gettempdir()) / "symphony_alpha_images"
        self._image_cache_dir.mkdir(parents=True, exist_ok=True)
        self._image_fetch_semaphore = asyncio.Semaphore(3)
        self._avatar_cache_dir = Path(tempfile.gettempdir()) / "symphony_alpha_avatars"
        self._avatar_cache_dir.mkdir(parents=True, exist_ok=True)
        self._avatar_fetch_semaphore = asyncio.Semaphore(4)
        self._dm_channel_avatar_urls: dict[int, str] = {}
        self._dm_avatar_tasks: dict[int, asyncio.Task[None]] = {}
        self._guild_recent_authors: dict[int, dict[int, object]] = {}
        self._mention_query_start = -1
        self._mention_avatar_tasks: dict[str, asyncio.Task[None]] = {}
        self._send_in_flight = False
        self._loading_overlay_active = False

        self.setWindowTitle("Symphony Alpha")
        self.resize(1200, 760)
        self.setStyleSheet(
            """
            QMainWindow, QWidget {
                background-color: #0F1220;
                color: #E8ECF8;
            }
            QListWidget, QTextBrowser, QLineEdit {
                background-color: #171B2B;
                border: 1px solid #303756;
                border-radius: 8px;
                padding: 6px 8px;
                color: #EDF0FF;
                selection-background-color: #5865F2;
            }
            QListWidget::item {
                border-radius: 6px;
                padding: 6px 8px;
            }
            QListWidget::item:selected {
                background-color: rgba(88, 101, 242, 0.28);
                border: 1px solid rgba(88, 101, 242, 0.72);
            }
            QTextBrowser {
                padding: 8px;
            }
            QPushButton {
                background-color: #252B3D;
                border: 1px solid #353D59;
                border-radius: 8px;
                color: #F5F6FF;
                padding: 6px 12px;
            }
            QPushButton:hover {
                border-color: #5865F2;
                background-color: #2E3550;
            }
            QPushButton:pressed {
                background-color: #242B42;
            }
            QPushButton:disabled {
                background-color: #1A1F2F;
                border-color: #2B3148;
                color: #8D95B3;
            }
            QLabel#checksLabel {
                color: #A7AFCC;
            }
            QLabel#attachmentLabel {
                color: #A7AFCC;
            }
            QLabel#typingLabel {
                color: #83B7FF;
                font-style: italic;
            }
            QWidget#loadingOverlay {
                background-color: rgba(9, 11, 20, 168);
            }
            QWidget#loadingCard {
                background-color: #171B2B;
                border: 1px solid #303756;
                border-radius: 12px;
            }
            QLabel#loadingTitle {
                color: #E9ECFF;
                font-size: 16px;
                font-weight: 600;
            }
            QLabel#loadingDetail {
                color: #B2BAD8;
            }
            QProgressBar#loadingBusyBar {
                border: 1px solid #303756;
                border-radius: 6px;
                background-color: #111427;
                min-height: 12px;
                max-height: 12px;
            }
            QProgressBar#loadingBusyBar::chunk {
                background-color: #5865F2;
                border-radius: 5px;
                width: 24px;
                margin: 1px;
            }
            """
        )

        root_widget = QWidget()
        self.setCentralWidget(root_widget)
        root_layout = QVBoxLayout(root_widget)
        root_layout.setContentsMargins(10, 10, 10, 10)
        root_layout.setSpacing(8)

        top_bar = QHBoxLayout()
        self.connection_label = QLabel("")
        self.connection_label.setStyleSheet("font-weight: 600; color: #5865F2;")
        self.checks_label = QLabel("Guilds: 0 | DM channels: 0 | DMs received: 0")
        self.checks_label.setObjectName("checksLabel")
        self.add_dm_button = QPushButton("Add DM")
        self.add_dm_button.clicked.connect(self._on_add_dm_clicked)
        self.logout_button = QPushButton("Logout")
        self.logout_button.clicked.connect(self._on_logout_clicked)

        top_bar.addWidget(self.connection_label, 0)
        top_bar.addStretch(1)
        top_bar.addWidget(self.checks_label, 0)
        top_bar.addStretch(1)
        top_bar.addWidget(self.add_dm_button, 0)
        top_bar.addWidget(self.logout_button, 0)

        panel_layout = QHBoxLayout()
        panel_layout.setSpacing(8)

        self.guild_list = QListWidget()
        self.guild_list.setMinimumWidth(240)
        self.guild_list.itemSelectionChanged.connect(self._queue_channel_reload)

        self.channel_list = QListWidget()
        self.channel_list.setMinimumWidth(260)
        self.channel_list.itemSelectionChanged.connect(self._queue_message_reload)

        self.message_view = QTextBrowser()
        self.message_view.setReadOnly(True)
        self.message_view.setOpenExternalLinks(True)

        panel_layout.addWidget(self.guild_list, 1)
        panel_layout.addWidget(self.channel_list, 1)
        panel_layout.addWidget(self.message_view, 2)

        composer_layout = QHBoxLayout()
        composer_layout.setSpacing(8)

        self.message_input = QLineEdit()
        self.message_input.setPlaceholderText("Type a message...")
        self.message_input.returnPressed.connect(self._on_send_clicked)
        self.message_input.textEdited.connect(self._on_message_input_edited)

        self._mention_popup = QListWidget(root_widget)
        self._mention_popup.setFocusPolicy(Qt.NoFocus)
        self._mention_popup.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self._mention_popup.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self._mention_popup.setSelectionMode(QAbstractItemView.SingleSelection)
        self._mention_popup.setUniformItemSizes(True)
        self._mention_popup.hide()
        self._mention_popup.itemClicked.connect(self._on_mention_item_chosen)
        self._mention_popup.itemActivated.connect(self._on_mention_item_chosen)
        self._mention_popup.setStyleSheet(
            """
            QListWidget {
                background-color: #171B2B;
                border: 1px solid #303756;
                border-radius: 8px;
                color: #EDF0FF;
                padding: 4px;
            }
            QListWidget::item {
                border-radius: 6px;
                padding: 6px 8px;
                min-height: 22px;
            }
            QListWidget::item:selected {
                background-color: rgba(88, 101, 242, 0.28);
                border: 1px solid rgba(88, 101, 242, 0.72);
            }
            """
        )
        self.message_input.installEventFilter(self)
        self._mention_popup.installEventFilter(self)

        self.attach_file_button = QPushButton("Attach Files")
        self.attach_file_button.clicked.connect(self._on_attach_files_clicked)

        self.clear_attachments_button = QPushButton("Clear Files")
        self.clear_attachments_button.clicked.connect(self._on_clear_attachments_clicked)
        self.clear_attachments_button.setEnabled(False)

        self.send_button = QPushButton("Send")
        self.send_button.clicked.connect(self._on_send_clicked)

        self.attachment_label = QLabel("No files attached.")
        self.attachment_label.setObjectName("attachmentLabel")
        self.typing_label = QLabel("")
        self.typing_label.setObjectName("typingLabel")
        self.typing_label.hide()

        composer_layout.addWidget(self.message_input, 1)
        composer_layout.addWidget(self.attach_file_button, 0)
        composer_layout.addWidget(self.clear_attachments_button, 0)
        composer_layout.addWidget(self.send_button, 0)

        root_layout.addLayout(top_bar)
        root_layout.addLayout(panel_layout, 1)
        root_layout.addWidget(self.attachment_label, 0)
        root_layout.addWidget(self.typing_label, 0)
        root_layout.addLayout(composer_layout, 0)

        self._loading_overlay = QWidget(root_widget)
        self._loading_overlay.setObjectName("loadingOverlay")
        overlay_layout = QVBoxLayout(self._loading_overlay)
        overlay_layout.setContentsMargins(0, 0, 0, 0)
        overlay_layout.addStretch(1)

        loading_card = QWidget()
        loading_card.setObjectName("loadingCard")
        loading_card_layout = QVBoxLayout(loading_card)
        loading_card_layout.setContentsMargins(20, 20, 20, 20)
        loading_card_layout.setSpacing(10)

        self._loading_title_label = QLabel("Authenticating")
        self._loading_title_label.setObjectName("loadingTitle")
        self._loading_title_label.setAlignment(Qt.AlignCenter)

        self._loading_detail_label = QLabel("Connecting to Discord...")
        self._loading_detail_label.setObjectName("loadingDetail")
        self._loading_detail_label.setAlignment(Qt.AlignCenter)
        self._loading_detail_label.setWordWrap(True)

        self._loading_busy_bar = QProgressBar()
        self._loading_busy_bar.setObjectName("loadingBusyBar")
        self._loading_busy_bar.setRange(0, 0)
        self._loading_busy_bar.setTextVisible(False)
        self._loading_busy_bar.setFixedWidth(280)

        loading_card_layout.addWidget(self._loading_title_label, 0)
        loading_card_layout.addWidget(self._loading_detail_label, 0)
        loading_card_layout.addWidget(self._loading_busy_bar, 0, Qt.AlignHCenter)

        overlay_layout.addWidget(loading_card, 0, Qt.AlignHCenter)
        overlay_layout.addStretch(1)

        self._loading_overlay.hide()
        self._sync_loading_overlay_geometry()
        self._update_composer_enabled_state()

    async def initialize(self) -> None:
        await self.refresh_guilds()

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        self._sync_loading_overlay_geometry()

    def _sync_loading_overlay_geometry(self) -> None:
        central = self.centralWidget()
        if central is None:
            return
        self._loading_overlay.setGeometry(central.rect())

    def _status_requires_loading_overlay(self, status: str) -> bool:
        lowered = status.strip().lower()
        if not lowered:
            return False
        if "connection resumed" in lowered:
            return False
        if "connected" in lowered and "disconnected" not in lowered and "reconnect" not in lowered:
            return False
        return (
            "connecting" in lowered
            or "reconnecting" in lowered
            or "gateway stopped unexpectedly" in lowered
        )

    def _update_composer_enabled_state(self) -> None:
        is_enabled = not self._loading_overlay_active and not self._send_in_flight
        if not is_enabled:
            self._hide_mention_popup()
        self.message_input.setEnabled(is_enabled)
        self.send_button.setEnabled(is_enabled)
        self.attach_file_button.setEnabled(is_enabled)
        self.clear_attachments_button.setEnabled(
            is_enabled and bool(self._pending_attachment_paths)
        )

    def _set_loading_overlay_state(self, visible: bool, detail_text: str = "") -> None:
        self._loading_overlay_active = visible
        if visible:
            detail = detail_text.strip() or "Connecting to Discord..."
            self._loading_detail_label.setText(detail)
            self._sync_loading_overlay_geometry()
            self._loading_overlay.show()
            self._loading_overlay.raise_()
        else:
            self._loading_overlay.hide()
        self._update_composer_enabled_state()

    def set_connection_status(self, status: str) -> None:
        normalized = status.strip()
        lowered = normalized.lower()
        if self._status_requires_loading_overlay(normalized):
            self.connection_label.setText("")
            self._set_loading_overlay_state(True, normalized)
            return

        self._set_loading_overlay_state(False)
        self.connection_label.setText(normalized)
        if "connected" in lowered or "resumed" in lowered:
            self.connection_label.setStyleSheet("font-weight: 600; color: #57F287;")
        elif "disconnected" in lowered or "gateway" in lowered:
            self.connection_label.setStyleSheet("font-weight: 600; color: #FEE75C;")
        else:
            self.connection_label.setStyleSheet("font-weight: 600; color: #5865F2;")

    def closeEvent(self, event: QCloseEvent) -> None:
        for task in (
            self._load_channels_task,
            self._load_messages_task,
            self._add_dm_task,
            self._typing_cleanup_task,
        ):
            if task is not None and not task.done():
                task.cancel()
        for task in list(self._dm_avatar_tasks.values()):
            if not task.done():
                task.cancel()
        self._dm_avatar_tasks.clear()
        self._hide_mention_popup()
        self._cancel_mention_avatar_tasks()
        super().closeEvent(event)

    def eventFilter(self, watched: object, event: QEvent) -> bool:
        if watched is self.message_input:
            if event.type() == QEvent.Type.KeyPress and self._mention_popup.isVisible():
                key = getattr(event, "key", lambda: None)()
                if key in {Qt.Key_Down, Qt.Key_Up, Qt.Key_PageDown, Qt.Key_PageUp}:
                    self._move_mention_popup_selection(key)
                    return True
                if key in {Qt.Key_Return, Qt.Key_Enter, Qt.Key_Tab}:
                    item = self._mention_popup.currentItem()
                    if item is None and self._mention_popup.count() > 0:
                        item = self._mention_popup.item(0)
                    if item is not None:
                        self._insert_mention_candidate(item)
                    return True
                if key == Qt.Key_Escape:
                    self._hide_mention_popup()
                    return True

            if event.type() == QEvent.Type.Hide:
                self._hide_mention_popup()

        if watched is self._mention_popup and event.type() == QEvent.Type.Hide:
            self._hide_mention_popup()
        return super().eventFilter(watched, event)

    def _move_mention_popup_selection(self, key: int) -> None:
        count = self._mention_popup.count()
        if count <= 0:
            return

        row = self._mention_popup.currentRow()
        if row < 0:
            row = 0
        if key == Qt.Key_Down:
            row = min(row + 1, count - 1)
        elif key == Qt.Key_Up:
            row = max(row - 1, 0)
        elif key == Qt.Key_PageDown:
            row = min(row + 5, count - 1)
        elif key == Qt.Key_PageUp:
            row = max(row - 5, 0)
        self._mention_popup.setCurrentRow(row)

    def _cancel_mention_avatar_tasks(self) -> None:
        for task in list(self._mention_avatar_tasks.values()):
            if not task.done():
                task.cancel()
        self._mention_avatar_tasks.clear()

    def _hide_mention_popup(self) -> None:
        if self._mention_popup.isVisible():
            self._mention_popup.hide()
        self._mention_popup.clear()
        self._mention_query_start = -1
        self._cancel_mention_avatar_tasks()

    def _on_mention_avatar_task_done(self, key: str, task: asyncio.Task[None]) -> None:
        current = self._mention_avatar_tasks.get(key)
        if current is task:
            self._mention_avatar_tasks.pop(key, None)
        if task.cancelled():
            return
        with contextlib.suppress(asyncio.CancelledError, Exception):
            task.exception()

    def _queue_mention_avatar_update(
        self,
        item: QListWidgetItem,
        *,
        key: str,
        avatar_url: str,
        preferred_name: str,
    ) -> None:
        existing = self._mention_avatar_tasks.get(key)
        if existing is not None and not existing.done():
            return

        task = self._create_task(
            self._apply_mention_avatar_to_item(
                item,
                key=key,
                avatar_url=avatar_url,
                preferred_name=preferred_name,
            )
        )
        if task is None:
            return

        self._mention_avatar_tasks[key] = task
        task.add_done_callback(
            lambda done_task, avatar_key=key: self._on_mention_avatar_task_done(
                avatar_key, done_task
            )
        )

    async def _apply_mention_avatar_to_item(
        self,
        item: QListWidgetItem,
        *,
        key: str,
        avatar_url: str,
        preferred_name: str,
    ) -> None:
        avatar_path = await self._cached_avatar_path(url=avatar_url, preferred_name=preferred_name)
        if avatar_path is None:
            return

        pixmap = QPixmap(str(avatar_path))
        if pixmap.isNull():
            return

        try:
            if item.listWidget() is not self._mention_popup:
                return
            if item.data(Qt.UserRole + 4) != key:
                return
            item.setIcon(
                QIcon(
                    self._rounded_avatar_pixmap(
                        pixmap,
                        size_px=MENTION_AVATAR_SIZE_PX,
                    )
                )
            )
        except RuntimeError:
            return

    def _mention_match_quality(self, query: str, fields: tuple[str, ...]) -> Optional[int]:
        if not query:
            return 1
        if any(field == query for field in fields):
            return 0
        if any(field.startswith(query) for field in fields):
            return 1
        if any(query in field for field in fields):
            return 2
        return None

    def _selected_guild(self) -> Optional[discord.Guild]:
        scope, guild_id = self._selected_scope_data()
        if scope != "guild" or guild_id is None:
            return None
        for guild in self._discord_service.get_guilds():
            if guild.id == guild_id:
                return guild
        return None

    def _selected_dm_recipient(self) -> Optional[discord.abc.User]:
        scope, _ = self._selected_scope_data()
        if scope != "dm":
            return None
        channel_id = self._selected_channel_id()
        if channel_id is None:
            return None
        for channel in self._discord_service.get_dm_channels():
            if channel.id == channel_id:
                return channel.recipient
        return None

    def _remember_message_author(self, message: discord.Message) -> None:
        guild = message.guild
        if guild is None:
            return
        guild_id = getattr(guild, "id", None)
        author_id = getattr(message.author, "id", None)
        if not isinstance(guild_id, int) or not isinstance(author_id, int):
            return

        bucket = self._guild_recent_authors.setdefault(guild_id, {})
        bucket[author_id] = message.author
        while len(bucket) > 250:
            oldest_user_id = next(iter(bucket))
            bucket.pop(oldest_user_id, None)

    def _current_mention_context(self) -> Optional[tuple[int, str]]:
        text = self.message_input.text()
        cursor = self.message_input.cursorPosition()
        if cursor < 0:
            return None

        prefix = text[:cursor]
        match = MENTION_QUERY_PATTERN.search(prefix)
        if match is None:
            return None

        query = match.group(2)
        mention_start = match.start(2) - 1
        if mention_start < 0:
            return None
        return (mention_start, query)

    def _collect_mention_suggestions(
        self,
        query: str,
        *,
        limit: int = 25,
    ) -> list[MentionSuggestion]:
        normalized_query = query.strip().lower()
        ranked: list[tuple[int, int, int, str, int, MentionSuggestion]] = []
        seen_mentions: set[str] = set()

        def append_user_candidate(user: object, source_rank: int) -> None:
            user_id = getattr(user, "id", None)
            user_name = getattr(user, "name", None)
            if not isinstance(user_id, int) or not isinstance(user_name, str):
                return

            display_name = (
                getattr(user, "display_name", None)
                or getattr(user, "global_name", None)
                or user_name
            )
            if not isinstance(display_name, str) or not display_name:
                display_name = user_name

            display_text = f"@{display_name}"
            if display_name.lower() != user_name.lower():
                display_text += f" ({user_name})"
            if getattr(user, "bot", False):
                display_text += " [bot]"

            search_texts = (
                user_name.lower(),
                str(user).lower(),
                display_name.lower(),
            )
            match_quality = self._mention_match_quality(normalized_query, search_texts)
            if match_quality is None:
                return

            mention_text = f"<@{user_id}>"
            if mention_text in seen_mentions:
                return
            seen_mentions.add(mention_text)
            ranked.append(
                (
                    0,
                    source_rank,
                    match_quality,
                    display_name.lower(),
                    user_id,
                    MentionSuggestion(
                        mention_text=mention_text,
                        display_text=display_text,
                        search_texts=search_texts,
                        kind="user",
                        entity_id=user_id,
                        avatar_url=self._avatar_url_for_user(user),
                    ),
                )
            )

        guild = self._selected_guild()
        if guild is not None:
            unique_members: dict[int, discord.Member] = {}
            for member in guild.members:
                unique_members[member.id] = member

            for member in unique_members.values():
                append_user_candidate(member, source_rank=0)

            for recent_user in self._guild_recent_authors.get(guild.id, {}).values():
                append_user_candidate(recent_user, source_rank=1)

            cached_users = self._discord_service.find_users_by_name(
                query, limit=max(limit * 3, 80)
            )
            for user in cached_users:
                append_user_candidate(user, source_rank=2)

            for role in guild.roles:
                if role.is_default():
                    continue
                if role.managed:
                    continue
                search_texts = (role.name.lower(),)
                match_quality = self._mention_match_quality(normalized_query, search_texts)
                if match_quality is None:
                    continue
                mention_text = f"<@&{role.id}>"
                if mention_text in seen_mentions:
                    continue
                seen_mentions.add(mention_text)
                suggestion = MentionSuggestion(
                    mention_text=mention_text,
                    display_text=f"@{role.name} (role)",
                    search_texts=search_texts,
                    kind="role",
                    entity_id=role.id,
                    avatar_url=None,
                )
                ranked.append((1, 0, match_quality, role.name.lower(), role.id, suggestion))
        else:
            recipient = self._selected_dm_recipient()
            if recipient is not None:
                append_user_candidate(recipient, source_rank=0)

            for user in self._discord_service.find_users_by_name(
                query, limit=max(limit * 2, 50)
            ):
                append_user_candidate(user, source_rank=1)

        ranked.sort(key=lambda item: (item[0], item[1], item[2], item[3], item[4]))
        return [entry[5] for entry in ranked[:limit]]

    def _populate_mention_popup(self, suggestions: list[MentionSuggestion]) -> None:
        self._cancel_mention_avatar_tasks()
        self._mention_popup.clear()

        for suggestion in suggestions:
            item = QListWidgetItem(suggestion.display_text)
            item.setData(Qt.UserRole, suggestion.mention_text)
            item.setData(Qt.UserRole + 1, suggestion.kind)
            avatar_key = (
                f"{suggestion.kind}:{suggestion.entity_id}:{suggestion.avatar_url or 'none'}"
            )
            item.setData(Qt.UserRole + 4, avatar_key)
            self._mention_popup.addItem(item)

            if suggestion.kind != "user":
                continue

            item.setIcon(
                QIcon(
                    self._fallback_avatar_pixmap(
                        suggestion.display_text,
                        size_px=MENTION_AVATAR_SIZE_PX,
                    )
                )
            )
            if not suggestion.avatar_url:
                continue

            self._queue_mention_avatar_update(
                item,
                key=avatar_key,
                avatar_url=suggestion.avatar_url,
                preferred_name=f"mention_{suggestion.entity_id}.png",
            )

        if self._mention_popup.count() > 0:
            self._mention_popup.setCurrentRow(0)

    def _show_mention_popup_near_cursor(self) -> None:
        if self._mention_popup.count() <= 0:
            return

        parent_widget = self.centralWidget()
        if parent_widget is None:
            return

        cursor_rect = self.message_input.cursorRect()
        parent_bottom = self.message_input.mapTo(parent_widget, cursor_rect.bottomLeft())
        parent_top = self.message_input.mapTo(parent_widget, cursor_rect.topLeft())

        row_height = self._mention_popup.sizeHintForRow(0)
        if row_height <= 0:
            row_height = 30

        visible_rows = min(8, self._mention_popup.count())
        popup_height = visible_rows * row_height + 10
        popup_width = max(320, min(540, self.message_input.width() + 80))
        available = parent_widget.rect().adjusted(4, 4, -4, -4)

        width = min(popup_width, max(220, available.width()))
        height = min(popup_height, max(80, available.height()))
        self._mention_popup.resize(width, height)

        x = max(available.left(), min(parent_bottom.x(), available.right() - width + 1))
        above_y = parent_top.y() - height - 2
        y = max(available.top(), min(above_y, available.bottom() - height + 1))

        self._mention_popup.move(x, y)
        self._mention_popup.show()
        self._mention_popup.raise_()

    def _refresh_mention_popup(self) -> None:
        context = self._current_mention_context()
        if context is None:
            self._hide_mention_popup()
            return

        mention_start, query = context
        suggestions = self._collect_mention_suggestions(query, limit=25)
        if not suggestions:
            self._hide_mention_popup()
            return

        self._mention_query_start = mention_start
        self._populate_mention_popup(suggestions)
        self._show_mention_popup_near_cursor()

    def _on_mention_item_chosen(self, item: QListWidgetItem) -> None:
        self._insert_mention_candidate(item)

    def _insert_mention_candidate(self, item: QListWidgetItem) -> None:
        mention_text = item.data(Qt.UserRole)
        if not isinstance(mention_text, str) or not mention_text:
            self._hide_mention_popup()
            return

        cursor = self.message_input.cursorPosition()
        context = self._current_mention_context()
        if context is None:
            mention_start = self._mention_query_start
        else:
            mention_start = context[0]

        if mention_start < 0 or mention_start > cursor:
            mention_start = cursor

        original = self.message_input.text()
        replacement = f"{mention_text} "
        updated = original[:mention_start] + replacement + original[cursor:]
        new_cursor = mention_start + len(replacement)

        self.message_input.blockSignals(True)
        self.message_input.setText(updated)
        self.message_input.setCursorPosition(new_cursor)
        self.message_input.blockSignals(False)

        self._hide_mention_popup()
        self._on_message_input_edited(self.message_input.text())

    def _avatar_initial(self, label: str) -> str:
        text = label.strip()
        if text.startswith("@"):
            text = text[1:]
        for character in text:
            if character.isalnum():
                return character.upper()
        return "?"

    def _avatar_color_for_seed(self, seed: str) -> QColor:
        palette = [
            "#5865F2",
            "#4F9CF7",
            "#3AA7B4",
            "#7D68F8",
            "#F78C6C",
            "#6EC56B",
        ]
        digest = hashlib.sha256(seed.encode("utf-8")).digest()
        return QColor(palette[digest[0] % len(palette)])

    def _fallback_avatar_html(self, label: str) -> str:
        initial = html.escape(self._avatar_initial(label))
        radius = AVATAR_SIZE_PX // 2
        return (
            "<span "
            f"style=\"display:inline-block; width:{AVATAR_SIZE_PX}px; height:{AVATAR_SIZE_PX}px; "
            f"line-height:{AVATAR_SIZE_PX}px; "
            f"text-align:center; border-radius:{radius}px; background:#303756; color:#F2F4FF; "
            "font-size:12px; font-weight:700;\">"
            f"{initial}</span>"
        )

    def _avatar_url_for_user(self, user: object) -> Optional[str]:
        avatar = getattr(user, "display_avatar", None)
        if avatar is None:
            return None

        with contextlib.suppress(Exception):
            avatar = avatar.replace(size=64, static_format="png")

        url = getattr(avatar, "url", None)
        if isinstance(url, str) and url:
            return url
        as_text = str(avatar)
        return as_text if as_text else None

    def _record_dm_channel_avatar_url(self, channel_id: int, user: object) -> bool:
        avatar_url = self._avatar_url_for_user(user)
        if not avatar_url:
            return False
        if self._dm_channel_avatar_urls.get(channel_id) == avatar_url:
            return False
        self._dm_channel_avatar_urls[channel_id] = avatar_url
        return True

    def _find_dm_channel_item(self, channel_id: int) -> Optional[QListWidgetItem]:
        for index in range(self.channel_list.count()):
            item = self.channel_list.item(index)
            if item.data(Qt.UserRole) == channel_id:
                return item
        return None

    def _rounded_avatar_pixmap(self, pixmap: QPixmap, size_px: int = AVATAR_SIZE_PX) -> QPixmap:
        scaled = pixmap.scaled(
            size_px,
            size_px,
            Qt.KeepAspectRatioByExpanding,
            Qt.SmoothTransformation,
        )
        rounded = QPixmap(size_px, size_px)
        rounded.fill(Qt.transparent)

        painter = QPainter(rounded)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        clip_path = QPainterPath()
        clip_path.addEllipse(0, 0, size_px, size_px)
        painter.setClipPath(clip_path)
        painter.drawPixmap(0, 0, scaled)
        painter.end()
        return rounded

    def _fallback_avatar_pixmap(self, label: str, size_px: int = AVATAR_SIZE_PX) -> QPixmap:
        pixmap = QPixmap(size_px, size_px)
        pixmap.fill(Qt.transparent)

        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(self._avatar_color_for_seed(label))
        painter.drawEllipse(0, 0, size_px, size_px)

        painter.setPen(QColor("#F2F4FF"))
        font = painter.font()
        font.setBold(True)
        font.setPointSize(max(8, size_px // 3))
        painter.setFont(font)
        painter.drawText(pixmap.rect(), Qt.AlignCenter, self._avatar_initial(label))
        painter.end()
        return pixmap

    def _dm_avatar_fallback_seed(self, channel_id: int, label: str) -> str:
        text = label.strip()
        if text:
            return text
        return f"dm-{channel_id}"

    def _set_dm_channel_item_fallback_icon(
        self, channel_id: int, label: str, item: Optional[QListWidgetItem] = None
    ) -> None:
        target_item = item or self._find_dm_channel_item(channel_id)
        if target_item is None:
            return
        seed = self._dm_avatar_fallback_seed(channel_id, label)
        target_item.setIcon(QIcon(self._fallback_avatar_pixmap(seed)))

    async def _cached_avatar_path(self, *, url: str, preferred_name: str) -> Optional[Path]:
        suffix = self._guess_image_suffix(preferred_name=preferred_name, url=url)
        digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:24]
        file_path = self._avatar_cache_dir / f"{digest}{suffix}"

        if file_path.exists():
            return file_path

        async with self._avatar_fetch_semaphore:
            if file_path.exists():
                return file_path

            try:
                timeout = aiohttp.ClientTimeout(total=20)
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    async with session.get(
                        url, headers={"User-Agent": "DiscordBot (SymphonyAlpha, 1.0)"}
                    ) as response:
                        if response.status != 200:
                            return None
                        body = await response.read()
            except Exception:
                return None

            if not body:
                return None

            try:
                await asyncio.to_thread(file_path.write_bytes, body)
            except OSError:
                return None
            return file_path

    async def _cached_avatar_source(self, *, url: str, preferred_name: str) -> Optional[str]:
        file_path = await self._cached_avatar_path(url=url, preferred_name=preferred_name)
        if file_path is None:
            return None
        return file_path.resolve().as_uri()

    async def _message_avatar_html(self, message: discord.Message, author_label: str) -> str:
        avatar_url = self._avatar_url_for_user(message.author)
        if avatar_url:
            local_source = await self._cached_avatar_source(
                url=avatar_url, preferred_name=f"author_{message.author.id}.png"
            )
            if local_source:
                safe_source = html.escape(local_source, quote=True)
                radius = AVATAR_SIZE_PX // 2
                return (
                    f"<img src=\"{safe_source}\" width=\"{AVATAR_SIZE_PX}\" "
                    f"height=\"{AVATAR_SIZE_PX}\" "
                    f"style=\"border-radius:{radius}px;\" />"
                )
        return self._fallback_avatar_html(author_label)

    def _on_dm_avatar_task_done(self, channel_id: int, task: asyncio.Task[None]) -> None:
        current = self._dm_avatar_tasks.get(channel_id)
        if current is task:
            self._dm_avatar_tasks.pop(channel_id, None)
        with contextlib.suppress(Exception):
            task.exception()

    def _queue_dm_avatar_update(self, channel_id: int) -> None:
        existing = self._dm_avatar_tasks.get(channel_id)
        if existing is not None and not existing.done():
            return
        task = self._create_task(self._apply_dm_channel_avatar(channel_id))
        if task is None:
            return
        self._dm_avatar_tasks[channel_id] = task
        task.add_done_callback(
            lambda done_task, cid=channel_id: self._on_dm_avatar_task_done(cid, done_task)
        )

    async def _apply_dm_channel_avatar(self, channel_id: int) -> None:
        item = self._find_dm_channel_item(channel_id)
        label = self._dm_channel_labels.get(channel_id, f"DM {channel_id}")
        if item is None:
            return

        avatar_url = self._dm_channel_avatar_urls.get(channel_id)
        if not avatar_url:
            self._set_dm_channel_item_fallback_icon(channel_id, label, item)
            return

        avatar_path = await self._cached_avatar_path(
            url=avatar_url, preferred_name=f"dm_{channel_id}.png"
        )
        if avatar_path is None:
            self._set_dm_channel_item_fallback_icon(channel_id, label, item)
            return

        pixmap = QPixmap(str(avatar_path))
        if pixmap.isNull():
            self._set_dm_channel_item_fallback_icon(channel_id, label, item)
            return
        item.setIcon(QIcon(self._rounded_avatar_pixmap(pixmap)))

    def _selected_scope_data(self) -> tuple[str, Optional[int]]:
        item = self.guild_list.currentItem()
        if item is None:
            return ("guild", None)

        return self._scope_from_item(item)

    def _selected_channel_id(self) -> Optional[int]:
        item = self.channel_list.currentItem()
        if item is None:
            return None
        return item.data(Qt.UserRole)

    def _format_user_choice(self, candidate: ResolvedUserCandidate) -> str:
        source_labels = {
            "cache": "cache",
            "guild_search": "guild search",
            "gateway_query": "gateway query",
        }
        guild_label = candidate.guild_name or "No guild context"
        source_label = source_labels.get(candidate.source, candidate.source)
        return (
            f"{candidate.display_name} (@{candidate.username}) [id:{candidate.user_id}] - "
            f"{guild_label} - {source_label}"
        )

    def _prompt_dm_lookup_scope(self, *, allow_all: bool) -> Optional[list[int]]:
        guilds = self._discord_service.get_lookup_guilds()
        if not guilds and not allow_all:
            self._show_info(
                "Add DM",
                "No joined guilds are available for guild-filtered lookup.",
            )
            return None

        if allow_all and not guilds:
            return []

        options: list[str] = []
        values: list[Optional[int]] = []
        if allow_all:
            options.append("All joined guilds")
            values.append(None)
        for guild_id, guild_name in guilds:
            options.append(f"{guild_name} [id:{guild_id}]")
            values.append(guild_id)

        title = "Lookup Scope"
        prompt = "Choose lookup scope for this username:"
        choice, picked = QInputDialog.getItem(self, title, prompt, options, 0, False)
        if not picked:
            return None

        selected_index = options.index(choice)
        selected_guild_id = values[selected_index]
        if selected_guild_id is None:
            return []
        return [selected_guild_id]

    def _prompt_no_match_action(self) -> str:
        options = [
            "Retry with guild filter",
            "Enter numeric user ID",
            "Cancel",
        ]
        choice, picked = QInputDialog.getItem(
            self,
            "Add DM",
            "No matching user found. Choose next action:",
            options,
            0,
            False,
        )
        if not picked:
            return "cancel"
        if choice == options[0]:
            return "retry"
        if choice == options[1]:
            return "id"
        return "cancel"

    def _start_add_dm_task(self, coro: Awaitable[None]) -> None:
        self.add_dm_button.setEnabled(False)
        task = self._create_task(coro)
        if task is None:
            self.add_dm_button.setEnabled(True)
            self._show_error("Add DM Failed", "Event loop is not available.")
            return
        task.add_done_callback(lambda done: self._observe_background_task(done, "Add DM Failed"))
        self._add_dm_task = task

    async def _resolve_query_and_open_dm(
        self,
        query: str,
        lookup_guild_ids: Optional[list[int]],
    ) -> None:
        try:
            candidates = await self._discord_service.resolve_users_for_dm(
                query,
                guild_ids=(lookup_guild_ids or None),
            )

            if not candidates:
                action = self._prompt_no_match_action()
                if action == "retry":
                    retry_scope = self._prompt_dm_lookup_scope(allow_all=False)
                    if retry_scope is None:
                        return
                    candidates = await self._discord_service.resolve_users_for_dm(
                        query,
                        guild_ids=retry_scope,
                    )
                    if not candidates:
                        self._show_info(
                            "Add DM",
                            "No matching user found in the selected guild.\n"
                            "Try a numeric user ID or ensure the user shares a guild with this application.",
                        )
                        return
                elif action == "id":
                    raw_id, ok = QInputDialog.getText(
                        self,
                        "Add DM",
                        "Enter numeric user ID or mention (<@...>):",
                    )
                    if not ok:
                        return
                    user_id = self._discord_service.parse_user_id_input(raw_id)
                    if user_id is None:
                        self._show_warning(
                            "Add DM",
                            "Please enter a numeric user ID or a valid mention.",
                        )
                        return
                    await self._open_dm_by_user_id(user_id)
                    return
                else:
                    return

            selected_candidate = candidates[0]
            if len(candidates) > 1:
                labels = [self._format_user_choice(candidate) for candidate in candidates]
                choice, picked = QInputDialog.getItem(
                    self,
                    "Select User",
                    "Multiple users matched. Select one:",
                    labels,
                    0,
                    False,
                )
                if not picked:
                    return
                selected_candidate = candidates[labels.index(choice)]

            await self._open_dm_by_user_id(selected_candidate.user_id)
        except DiscordServiceError as exc:
            self._show_error("Add DM Failed", str(exc))
        except Exception as exc:
            self._show_error("Add DM Failed", str(exc))
        finally:
            current_task = asyncio.current_task()
            if self._add_dm_task is current_task:
                self.add_dm_button.setEnabled(True)
                self._add_dm_task = None

    def _show_message(self, icon: QMessageBox.Icon, title: str, text: str) -> None:
        box = QMessageBox(self)
        box.setIcon(icon)
        box.setWindowTitle(title)
        box.setText(text)
        box.setStandardButtons(QMessageBox.Ok)
        box.setAttribute(Qt.WA_DeleteOnClose, True)
        box.open()

    def _show_error(self, title: str, text: str) -> None:
        self._show_message(QMessageBox.Critical, title, text)

    def _show_warning(self, title: str, text: str) -> None:
        self._show_message(QMessageBox.Warning, title, text)

    def _show_info(self, title: str, text: str) -> None:
        self._show_message(QMessageBox.Information, title, text)

    def _create_task(self, coro: Awaitable[None]) -> Optional[asyncio.Task[None]]:
        try:
            loop = asyncio.get_running_loop()
        except RuntimeError:
            return None
        return loop.create_task(coro)

    def _observe_background_task(self, task: asyncio.Task[None], title: str) -> None:
        if task.cancelled():
            return
        exc = task.exception()
        if exc is None:
            return
        self._show_error(title, str(exc))

    def _refresh_typing_label(self) -> None:
        channel_id = self._selected_channel_id()
        if channel_id is None:
            self.typing_label.hide()
            self.typing_label.setText("")
            return

        now = time.monotonic()
        channel_state = self._typing_expirations.get(channel_id, {})
        active_users = [name for name, expiry in channel_state.items() if expiry > now]

        if not active_users:
            self.typing_label.hide()
            self.typing_label.setText("")
            return

        if len(active_users) == 1:
            text = f"{active_users[0]} is typing..."
        elif len(active_users) == 2:
            text = f"{active_users[0]} and {active_users[1]} are typing..."
        else:
            text = f"{active_users[0]} and {len(active_users) - 1} others are typing..."

        self.typing_label.setText(text)
        self.typing_label.show()

    def _set_typing_user(self, channel_id: int, user_name: str, ttl_seconds: float) -> None:
        expires_at = time.monotonic() + ttl_seconds
        channel_state = self._typing_expirations.setdefault(channel_id, {})
        channel_state[user_name] = expires_at
        self._refresh_typing_label()
        self._ensure_typing_cleanup_task()

    def _clear_typing_user(self, channel_id: int, user_name: str) -> None:
        channel_state = self._typing_expirations.get(channel_id)
        if not channel_state:
            return
        if user_name in channel_state:
            channel_state.pop(user_name, None)
        if not channel_state:
            self._typing_expirations.pop(channel_id, None)
        self._refresh_typing_label()

    def _prune_typing_expirations(self) -> None:
        now = time.monotonic()
        empty_channels: list[int] = []
        for channel_id, users in self._typing_expirations.items():
            expired = [name for name, expiry in users.items() if expiry <= now]
            for name in expired:
                users.pop(name, None)
            if not users:
                empty_channels.append(channel_id)

        for channel_id in empty_channels:
            self._typing_expirations.pop(channel_id, None)

    def _ensure_typing_cleanup_task(self) -> None:
        if self._typing_cleanup_task is not None and not self._typing_cleanup_task.done():
            return
        task = self._create_task(self._typing_cleanup_loop())
        if task is not None:
            self._typing_cleanup_task = task

    async def _typing_cleanup_loop(self) -> None:
        try:
            while self._typing_expirations:
                await asyncio.sleep(0.8)
                self._prune_typing_expirations()
                self._refresh_typing_label()
        finally:
            self._typing_cleanup_task = None

    def _on_message_input_edited(self, text: str) -> None:
        self._refresh_mention_popup()

        channel_id = self._selected_channel_id()
        if channel_id is None:
            return

        if not text.strip():
            self._clear_typing_user(channel_id, "You")
            return

        self._set_typing_user(channel_id, "You", ttl_seconds=2.5)

        now = time.monotonic()
        if now < self._typing_send_cooldown_until:
            return

        self._typing_send_cooldown_until = now + 8.0
        self._create_task(self._send_typing_indicator(channel_id))

    async def _send_typing_indicator(self, channel_id: int) -> None:
        with contextlib.suppress(DiscordServiceError):
            await self._discord_service.send_typing_indicator(channel_id)

    def _attachment_kind(self, *, filename: str, content_type: Optional[str]) -> str:
        suffix = Path(filename).suffix.lower()
        mime = (content_type or "").lower().strip()

        if mime.startswith("image/") or suffix in IMAGE_SUFFIXES:
            return "image"
        if mime.startswith("video/") or suffix in VIDEO_SUFFIXES:
            return "video"
        if mime.startswith("audio/") or suffix in AUDIO_SUFFIXES:
            return "audio"
        if mime.startswith("text/") or suffix in TEXT_SUFFIXES:
            return "text"
        if mime in DOCUMENT_MIME_TYPES or suffix in DOCUMENT_SUFFIXES:
            return "document"
        if mime in ARCHIVE_MIME_TYPES or suffix in ARCHIVE_SUFFIXES:
            return "archive"
        return "file"

    def _attachment_kind_label(self, kind: str) -> str:
        labels = {
            "image": "Image",
            "video": "Video",
            "audio": "Audio",
            "text": "Text",
            "document": "Document",
            "archive": "Archive",
            "file": "File",
        }
        return labels.get(kind, "File")

    def _format_attachment_size(self, size_bytes: Optional[int]) -> str:
        if not isinstance(size_bytes, int) or size_bytes < 0:
            return "unknown size"

        value = float(size_bytes)
        for unit in ("B", "KB", "MB", "GB", "TB"):
            if value < 1024.0 or unit == "TB":
                if unit == "B":
                    return f"{int(value)} {unit}"
                return f"{value:.1f} {unit}"
            value /= 1024.0
        return f"{size_bytes} B"

    async def _render_attachment_html(self, attachment: discord.Attachment) -> str:
        safe_filename = html.escape(attachment.filename)
        safe_url = html.escape(attachment.url, quote=True)
        kind = self._attachment_kind(
            filename=attachment.filename,
            content_type=getattr(attachment, "content_type", None),
        )
        kind_label = self._attachment_kind_label(kind)
        size_label = self._format_attachment_size(getattr(attachment, "size", None))
        header = f"[{kind_label} | {size_label}] <a href=\"{safe_url}\">{safe_filename}</a>"

        if kind == "image":
            local_src = await self._cached_image_source(
                url=attachment.url, preferred_name=attachment.filename
            )
            image_src = html.escape(local_src or attachment.url, quote=True)
            return (
                f"{header}<br>"
                f"<img src=\"{image_src}\" style=\"max-width: 520px; border-radius: 6px;\" />"
            )

        if kind == "video":
            return (
                f"{header}<br>"
                f"<video src=\"{safe_url}\" controls style=\"max-width: 520px;\"></video>"
            )

        if kind == "audio":
            return (
                f"{header}<br>"
                f"<audio src=\"{safe_url}\" controls style=\"width: 520px; max-width: 100%;\"></audio>"
            )

        return header

    def _guess_image_suffix(self, *, preferred_name: str, url: str) -> str:
        suffix = Path(preferred_name).suffix.lower()
        if suffix in IMAGE_SUFFIXES:
            return suffix

        url_suffix = Path(urlsplit(url).path).suffix.lower()
        if url_suffix in IMAGE_SUFFIXES:
            return url_suffix
        return ".img"

    async def _cached_image_source(self, *, url: str, preferred_name: str) -> Optional[str]:
        """
        Downloads image URL to a local cache path and returns a file URI for rendering.
        """

        suffix = self._guess_image_suffix(preferred_name=preferred_name, url=url)
        digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:24]
        file_path = self._image_cache_dir / f"{digest}{suffix}"

        if file_path.exists():
            return file_path.resolve().as_uri()

        async with self._image_fetch_semaphore:
            if file_path.exists():
                return file_path.resolve().as_uri()

            try:
                timeout = aiohttp.ClientTimeout(total=20)
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    async with session.get(
                        url, headers={"User-Agent": "DiscordBot (SymphonyAlpha, 1.0)"}
                    ) as response:
                        if response.status != 200:
                            return None
                        body = await response.read()
            except Exception:
                return None

            if not body:
                return None

            try:
                await asyncio.to_thread(file_path.write_bytes, body)
            except OSError:
                return None

            return file_path.resolve().as_uri()

    def _refresh_attachment_label(self) -> None:
        count = len(self._pending_attachment_paths)
        if count == 0:
            self.attachment_label.setText("No files attached.")
            self._update_composer_enabled_state()
            return

        if count == 1:
            self.attachment_label.setText(f"Attached file: {self._pending_attachment_paths[0].name}")
        else:
            preview_names = ", ".join(path.name for path in self._pending_attachment_paths[:3])
            if count > 3:
                preview_names += ", ..."
            self.attachment_label.setText(f"Attached files ({count}): {preview_names}")

        self._update_composer_enabled_state()

    def _on_attach_files_clicked(self) -> None:
        image_globs = " ".join(f"*{suffix}" for suffix in sorted(IMAGE_SUFFIXES))
        video_globs = " ".join(f"*{suffix}" for suffix in sorted(VIDEO_SUFFIXES))
        audio_globs = " ".join(f"*{suffix}" for suffix in sorted(AUDIO_SUFFIXES))
        text_globs = " ".join(f"*{suffix}" for suffix in sorted(TEXT_SUFFIXES))
        doc_globs = " ".join(f"*{suffix}" for suffix in sorted(DOCUMENT_SUFFIXES))
        archive_globs = " ".join(f"*{suffix}" for suffix in sorted(ARCHIVE_SUFFIXES))
        supported_globs = " ".join(
            f"*{suffix}"
            for suffix in sorted(
                IMAGE_SUFFIXES
                | VIDEO_SUFFIXES
                | AUDIO_SUFFIXES
                | TEXT_SUFFIXES
                | DOCUMENT_SUFFIXES
                | ARCHIVE_SUFFIXES
            )
        )
        paths, _ = QFileDialog.getOpenFileNames(
            self,
            "Attach File(s)",
            "",
            ";;".join(
                [
                    "All Files (*.*)",
                    f"Common Supported Files ({supported_globs})",
                    f"Images ({image_globs})",
                    f"Videos ({video_globs})",
                    f"Audio ({audio_globs})",
                    f"Text ({text_globs})",
                    f"Documents ({doc_globs})",
                    f"Archives ({archive_globs})",
                ]
            ),
        )
        if not paths:
            return

        added_count = 0
        for raw_path in paths:
            path = Path(raw_path).expanduser()
            if not path.exists() or not path.is_file():
                continue
            with contextlib.suppress(Exception):
                path = path.resolve()
            if path in self._pending_attachment_paths:
                continue
            self._pending_attachment_paths.append(path)
            added_count += 1

        if added_count == 0:
            self._show_warning(
                "Attach Files",
                "No valid files were selected.",
            )
            return

        self._refresh_attachment_label()

    def _on_clear_attachments_clicked(self) -> None:
        self._pending_attachment_paths = []
        self._refresh_attachment_label()

    def _refresh_checks_label(self) -> None:
        checks = self._discord_service.get_connection_checks()
        self.checks_label.setText(
            "Guilds: "
            f"{checks['guild_count']} | "
            f"DM channels: {checks['dm_channel_count']} | "
            f"DMs received: {checks['received_dm_count']}"
        )

    def _dm_channel_label(self, channel: discord.DMChannel) -> str:
        recipient = channel.recipient
        if recipient is None:
            return f"DM {channel.id}"
        display_name = recipient.global_name or recipient.name
        return f"@{display_name}"

    def _channel_list_has_channel(self, channel_id: int) -> bool:
        for index in range(self.channel_list.count()):
            item = self.channel_list.item(index)
            if item.data(Qt.UserRole) == channel_id:
                return True
        return False

    def _select_dm_scope(self) -> None:
        for index in range(self.guild_list.count()):
            item = self.guild_list.item(index)
            scope, _ = self._scope_from_item(item)
            if scope == "dm":
                self.guild_list.setCurrentItem(item)
                return

    def _scope_from_item(self, item: QListWidgetItem) -> tuple[str, Optional[int]]:
        data = item.data(Qt.UserRole)
        if isinstance(data, (tuple, list)) and len(data) == 2:
            scope = data[0]
            raw_id = data[1]
            if isinstance(scope, str) and scope in {"guild", "dm"}:
                if isinstance(raw_id, int) or raw_id is None:
                    return (scope, raw_id)
        return ("guild", None)

    def _queue_channel_reload(self) -> None:
        self._hide_mention_popup()
        if self._load_channels_task is not None and not self._load_channels_task.done():
            self._load_channels_task.cancel()
        task = self._create_task(self._load_channels_for_selection())
        if task is not None:
            self._load_channels_task = task

    def _queue_message_reload(self) -> None:
        self._hide_mention_popup()
        if self._load_messages_task is not None and not self._load_messages_task.done():
            self._load_messages_task.cancel()
        task = self._create_task(self._load_messages_for_selection())
        if task is not None:
            self._load_messages_task = task
        self._refresh_typing_label()

    async def refresh_guilds(self) -> None:
        self.guild_list.clear()
        self.channel_list.clear()
        self.message_view.clear()
        self._displayed_message_ids.clear()

        dm_item = QListWidgetItem("Direct Messages")
        dm_item.setData(Qt.UserRole, ("dm", None))
        self.guild_list.addItem(dm_item)

        guilds = self._discord_service.get_guilds()
        for guild in guilds:
            item = QListWidgetItem(guild.name)
            item.setData(Qt.UserRole, ("guild", guild.id))
            self.guild_list.addItem(item)

        # Keep original behavior (guild-first when available), but allow DM-only usage.
        self.guild_list.blockSignals(True)
        if self.guild_list.count() > 1:
            self.guild_list.setCurrentRow(1)
        else:
            self.guild_list.setCurrentRow(0)
        self.guild_list.blockSignals(False)
        await self._load_channels_for_selection()
        self._refresh_checks_label()

    async def _load_channels_for_selection(self) -> None:
        self._hide_mention_popup()
        scope, guild_id = self._selected_scope_data()
        for  task in list(self._dm_avatar_tasks.values()):
            if not task.done():
                task.cancel()
        self._dm_avatar_tasks.clear()
        self.channel_list.clear()
        self.message_view.clear()
        self._displayed_message_ids.clear()
        self._refresh_typing_label()

        if scope == "dm":
            await self._discord_service.refresh_known_dm_channels()
            live_dm_channels = {channel.id: channel for channel in self._discord_service.get_dm_channels()}
            for dm_channel_id, label in self._discord_service.get_known_dm_channels():
                self._dm_channel_labels[dm_channel_id] = label

            for dm_channel_id, label in sorted(
                self._dm_channel_labels.items(), key=lambda pair: pair[1].lower()
            ):
                item = QListWidgetItem(label)
                item.setData(Qt.UserRole, dm_channel_id)
                self.channel_list.addItem(item)
                self._set_dm_channel_item_fallback_icon(dm_channel_id, label, item)

                live_dm_channel = live_dm_channels.get(dm_channel_id)
                if live_dm_channel is not None and live_dm_channel.recipient is not None:
                    self._record_dm_channel_avatar_url(dm_channel_id, live_dm_channel.recipient)
                self._queue_dm_avatar_update(dm_channel_id)

            if self.channel_list.count() > 0:
                self.channel_list.setCurrentRow(0)
            else:
                self.message_view.setHtml(
                    "<p><b>No direct messages found.</b><br>"
                    "Open or receive a DM with this Application, then reselect Direct Messages."
                    "</p>"
                )
            self._refresh_checks_label()
            return

        if guild_id is None:
            self._refresh_checks_label()
            return

        try:
            channels = await self._discord_service.get_text_channels(guild_id)
        except DiscordServiceError as exc:
            self._show_error("Channel Load Failed", str(exc))
            return
        except asyncio.CancelledError:
            return

        for channel in channels:
            item = QListWidgetItem(f"#{channel.name}")
            item.setData(Qt.UserRole, channel.id)
            self.channel_list.addItem(item)

        if self.channel_list.count() > 0:
            self.channel_list.setCurrentRow(0)
        else:
            self.message_view.setHtml(
                "<p><b>No text channels found.</b><br>"
                "This Application cannot view any text channels in the selected guild."
                "</p>"
            )
        self._refresh_checks_label()

    async def _load_messages_for_selection(self) -> None:
        channel_id = self._selected_channel_id()
        self.message_view.clear()
        self._displayed_message_ids.clear()
        self._refresh_typing_label()
        if channel_id is None:
            return

        try:
            messages = await self._discord_service.fetch_recent_messages(channel_id, limit=50)
        except DiscordServiceError as exc:
            self._show_error("Message Load Failed", str(exc))
            return
        except asyncio.CancelledError:
            return

        for message in messages:
            await self._append_message(message)
        self._refresh_typing_label()

    async def handle_incoming_message(self, message: discord.Message) -> None:
        self._refresh_checks_label()
        self._remember_message_author(message)
        self._clear_typing_user(message.channel.id, message.author.name)
        global_name = getattr(message.author, "global_name", None)
        if global_name:
            self._clear_typing_user(message.channel.id, global_name)

        if message.guild is None:
            display_name = message.author.global_name or message.author.name
            label = f"@{display_name}"
            self._dm_channel_labels[message.channel.id] = label
            avatar_changed = self._record_dm_channel_avatar_url(message.channel.id, message.author)

            scope, _ = self._selected_scope_data()
            if scope == "dm":
                item = self._find_dm_channel_item(message.channel.id)
                if item is None:
                    item = QListWidgetItem(label)
                    item.setData(Qt.UserRole, message.channel.id)
                    self.channel_list.addItem(item)
                else:
                    item.setText(label)
                if message.channel.id not in self._dm_channel_avatar_urls:
                    self._set_dm_channel_item_fallback_icon(message.channel.id, label, item)
                if avatar_changed or message.channel.id in self._dm_channel_avatar_urls:
                    self._queue_dm_avatar_update(message.channel.id)

        selected_channel_id = self._selected_channel_id()
        if selected_channel_id is None:
            return
        if message.channel.id != selected_channel_id:
            return
        await self._append_message(message)
        self._refresh_typing_label()

    async def handle_typing_event(
        self, channel_id: int, user_display_name: str, is_dm: bool
    ) -> None:
        # Keep DM UX focused as requested, but allow typing events for selected guild channels too.
        if not user_display_name.strip():
            return
        self._set_typing_user(channel_id, user_display_name, ttl_seconds=8.0)

    async def _append_message(self, message: discord.Message) -> None:
        if message.id in self._displayed_message_ids:
            return
        self._displayed_message_ids.add(message.id)
        self._remember_message_author(message)

        author_label = (
            getattr(message.author, "display_name", None)
            or getattr(message.author, "global_name", None)
            or message.author.name
        )
        author_name = html.escape(author_label)
        timestamp = message.created_at.astimezone().strftime("%Y-%m-%d %H:%M:%S")
        avatar_html = await self._message_avatar_html(message, author_label)

        content_parts: list[str] = []
        if message.content:
            content_parts.append(html.escape(message.content).replace("\n", "<br>"))
        for attachment in message.attachments:
            content_parts.append(await self._render_attachment_html(attachment))

        # Some images arrive as embeds instead of attachment objects.
        for embed in message.embeds:
            image = getattr(embed, "image", None)
            image_url = getattr(image, "url", None)
            if isinstance(image_url, str) and image_url:
                safe_url = html.escape(image_url, quote=True)
                local_src = await self._cached_image_source(
                    url=image_url, preferred_name=f"{message.id}_embed"
                )
                image_src = html.escape(local_src or image_url, quote=True)
                content_parts.append(
                    f"<a href=\"{safe_url}\">[Embedded image]</a><br>"
                    f"<img src=\"{image_src}\" style=\"max-width: 520px; border-radius: 6px;\" />"
                )

            video = getattr(embed, "video", None)
            video_url = getattr(video, "url", None)
            if isinstance(video_url, str) and video_url:
                safe_video_url = html.escape(video_url, quote=True)
                content_parts.append(
                    f"[Embedded video] <a href=\"{safe_video_url}\">{safe_video_url}</a>"
                )
        if not content_parts:
            content_parts.append("<i>[No text content]</i>")

        body = "<br>".join(content_parts)
        line = (
            "<table cellspacing='0' cellpadding='0' style='margin:0 0 10px 0; width:100%;'>"
            "<tr>"
            f"<td style='width:34px; vertical-align:top; padding:2px 8px 0 0;'>{avatar_html}</td>"
            f"<td style='vertical-align:top;'><b>{author_name}</b> "
            f"<span style='color:#7F88A9;'>[{timestamp}]</span><br>{body}</td>"
            "</tr>"
            "</table>"
        )
        self.message_view.append(line)

        cursor = self.message_view.textCursor()
        cursor.movePosition(QTextCursor.End)
        self.message_view.setTextCursor(cursor)

    @asyncSlot()
    async def _on_send_clicked(self) -> None:
        self._hide_mention_popup()
        channel_id = self._selected_channel_id()
        if channel_id is None:
            self._show_warning("No Channel Selected", "Please select a channel first.")
            return

        content = self.message_input.text().strip()
        attachment_paths = list(self._pending_attachment_paths)
        if not content and not attachment_paths:
            return

        self._send_in_flight = True
        self._update_composer_enabled_state()
        try:
            message = await self._discord_service.send_message(
                channel_id,
                content=content,
                attachment_paths=attachment_paths,
            )
        except DiscordServiceError as exc:
            self._show_error("Send Failed", str(exc))
            return
        finally:
            self._send_in_flight = False
            self._update_composer_enabled_state()

        self.message_input.clear()
        self._pending_attachment_paths = []
        self._refresh_attachment_label()
        self._clear_typing_user(channel_id, "You")
        await self._append_message(message)

    def _on_add_dm_clicked(self) -> None:
        prompt = "Enter username/display name (or numeric user ID / mention):"
        query, ok = QInputDialog.getText(self, "Add DM", prompt)
        if not ok:
            return

        query = query.strip()
        if not query:
            self._show_warning("Add DM", "Please enter a username or user ID.")
            return

        selected_user_id = self._discord_service.parse_user_id_input(query)
        if selected_user_id is not None:
            self._start_add_dm_task(self._open_dm_by_user_id(selected_user_id))
            return

        lookup_scope = self._prompt_dm_lookup_scope(allow_all=True)
        if lookup_scope is None:
            return

        self._start_add_dm_task(self._resolve_query_and_open_dm(query, lookup_scope))

    async def _open_dm_by_user_id(self, user_id: int) -> None:
        try:
            dm_channel = await self._discord_service.open_dm_with_user(user_id)
            label = self._dm_channel_label(dm_channel)
            self._dm_channel_labels[dm_channel.id] = label
            if dm_channel.recipient is not None:
                self._record_dm_channel_avatar_url(dm_channel.id, dm_channel.recipient)
            self._select_dm_scope()

            if self._load_channels_task is not None:
                with contextlib.suppress(asyncio.CancelledError, Exception):
                    await self._load_channels_task
            else:
                await self._load_channels_for_selection()

            if not self._channel_list_has_channel(dm_channel.id):
                dm_item = QListWidgetItem(label)
                dm_item.setData(Qt.UserRole, dm_channel.id)
                self.channel_list.addItem(dm_item)
                if dm_channel.id not in self._dm_channel_avatar_urls:
                    self._set_dm_channel_item_fallback_icon(dm_channel.id, label, dm_item)

            for index in range(self.channel_list.count()):
                item = self.channel_list.item(index)
                if item.data(Qt.UserRole) == dm_channel.id:
                    item.setText(label)
                    if dm_channel.id not in self._dm_channel_avatar_urls:
                        self._set_dm_channel_item_fallback_icon(dm_channel.id, label, item)
                    self.channel_list.setCurrentItem(item)
                    break

            self._queue_dm_avatar_update(dm_channel.id)
            self._refresh_checks_label()
        except DiscordServiceError as exc:
            self._show_error("Add DM Failed", str(exc))
        except Exception as exc:
            self._show_error("Add DM Failed", str(exc))
        finally:
            self.add_dm_button.setEnabled(True)
            self._add_dm_task = None

    @asyncSlot()
    async def _on_logout_clicked(self) -> None:
        self.logout_button.setEnabled(False)
        try:
            await self._logout_handler()
        except SymphonyError as exc:
            self._show_error("Logout Failed", str(exc))
            self.logout_button.setEnabled(True)


class SymphonyController:
    """
    Coordinates startup flow, authentication, keychain persistence, and windows.
    """

    def __init__(self, app: QApplication) -> None:
        self._app = app
        self._token_store = TokenStore()
        enable_members_intent = env_flag_enabled("SYMPHONY_ENABLE_GUILD_MEMBERS_INTENT")
        self._discord_service = DiscordService(
            message_callback=self._on_discord_message,
            typing_callback=self._on_discord_typing,
            status_callback=self._on_discord_status,
            enable_members_intent=enable_members_intent,
        )
        self._last_status = "Connecting..."

        self._login_window: Optional[LoginWindow] = None
        self._main_window: Optional[MainWindow] = None

    async def bootstrap(self) -> None:
        try:
            stored_token = await self._token_store.load_token()
        except TokenStoreError as exc:
            self._show_login_window(str(exc))
            return

        if stored_token:
            try:
                await self._discord_service.login(stored_token)
            except (AuthenticationError, DiscordServiceError):
                # Required flow: remove invalid stored token and show login.
                with contextlib.suppress(TokenStoreError):
                    await self._token_store.clear_token()
                self._show_login_window(
                    "Stored token was invalid or expired. Please log in again."
                )
                return
            await self._show_main_window()
            return

        self._show_login_window()

    def _show_login_window(self, status_text: str = "") -> None:
        if self._main_window is not None:
            self._main_window.close()
            self._main_window = None

        if self._login_window is None:
            self._login_window = LoginWindow(self._handle_login_submission)
        if status_text:
            self._login_window.set_status(status_text)
        self._login_window.show()
        self._login_window.raise_()
        self._login_window.activateWindow()

    async def _show_main_window(self) -> None:
        if self._login_window is not None:
            self._login_window.close()
            self._login_window = None

        self._main_window = MainWindow(self._discord_service, self._handle_logout)
        self._main_window.set_connection_status(self._last_status)
        self._main_window.show()
        await self._main_window.initialize()

    async def _handle_login_submission(self, raw_token: str) -> None:
        token = normalize_token(raw_token)
        await self._discord_service.login(token)

        try:
            await self._token_store.save_token(token)
        except TokenStoreError as exc:
            await self._discord_service.logout()
            raise TokenStoreError(
                "Login succeeded but saving token to the OS keychain failed."
            ) from exc

        await self._show_main_window()

    async def _handle_logout(self) -> None:
        await self._discord_service.logout()
        await self._token_store.clear_token()

        if self._main_window is not None:
            self._main_window.close()
            self._main_window = None

        self._show_login_window("Logged out. Token removed from OS keychain.")

    async def _on_discord_message(self, message: discord.Message) -> None:
        if self._main_window is None:
            return
        await self._main_window.handle_incoming_message(message)

    async def _on_discord_typing(
        self, channel_id: int, user_display_name: str, is_dm: bool
    ) -> None:
        if self._main_window is None:
            return
        await self._main_window.handle_typing_event(channel_id, user_display_name, is_dm)

    async def _on_discord_status(self, text: str) -> None:
        self._last_status = text
        if self._main_window is None:
            return
        self._main_window.set_connection_status(text)

    async def shutdown(self) -> None:
        await self._discord_service.logout()


def main() -> None:
    app = QApplication(sys.argv)
    app.setApplicationName("Symphony Alpha")

    loop = QEventLoop(app)
    asyncio.set_event_loop(loop)

    controller = SymphonyController(app)
    quit_event = asyncio.Event()
    app.aboutToQuit.connect(quit_event.set)

    with loop:
        startup_task = loop.create_task(controller.bootstrap())

        def _observe_startup(task: asyncio.Task[None]) -> None:
            if task.cancelled():
                return
            error = task.exception()
            if error is None:
                return
            QMessageBox.critical(None, "Startup Error", str(error))
            app.quit()

        startup_task.add_done_callback(_observe_startup)

        loop.run_until_complete(quit_event.wait())
        loop.run_until_complete(controller.shutdown())


if __name__ == "__main__":
    main()
