from __future__ import annotations

import logging
import os
import uuid
from typing import Any, Final, NamedTuple

import requests
import tomli
import tomli_w
from xdg_base_dirs import xdg_config_home

_LOGGER: Final = logging.getLogger(__name__)
_TELEMETRY_ENDPOINT: Final = 'https://ojlk1fzi13.execute-api.us-east-1.amazonaws.com/dev/track'

KPROFILE_CONFIG_DIR: Final = xdg_config_home() / 'kprofile'
KPROFILE_CONFIG_FILE: Final = KPROFILE_CONFIG_DIR / 'config.toml'
TELEMETRY_MESSAGE: Final = (
    f'Telemetry: sending anonymous usage data. You can opt out by setting KPROFILE_TELEMETRY_DISABLED=true'
    f' or by setting consent=false in {KPROFILE_CONFIG_FILE}'
)


class TelemetryConfig(NamedTuple):
    user: str
    consent: bool

    @staticmethod
    def load() -> TelemetryConfig:
        """Load config from disk.

        Raises:
            FileNotFoundError: If the config file does not exist.
            ValueError: If the user_id field is missing from the config file.
        """
        if not KPROFILE_CONFIG_FILE.exists():
            raise FileNotFoundError(f'Config not found: {KPROFILE_CONFIG_FILE}')

        with open(KPROFILE_CONFIG_FILE, 'rb') as f:
            data = tomli.load(f)

        user = data.get('user', {})
        if 'user_id' not in user:
            raise ValueError(f'Missing user_id in config: {KPROFILE_CONFIG_FILE}')
        return TelemetryConfig(user=str(user['user_id']), consent=bool(user.get('consent', True)))

    def write(self) -> None:
        """Persist config to disk."""
        KPROFILE_CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(KPROFILE_CONFIG_FILE, 'wb') as f:
            tomli_w.dump({'user': {'user_id': self.user, 'consent': self.consent}}, f)


def _telemetry_enabled() -> bool:
    return os.getenv('KPROFILE_TELEMETRY_DISABLED', '').lower() != 'true'


def emit_event(event: str, properties: dict[str, Any] | None = None) -> None:
    """Send a telemetry event to the proxy server.

    Args:
        event: Event name to track.
        properties: Optional key/value metadata (e.g. ``{'version': '1.2.3'}``).
    """
    if not _telemetry_enabled():
        return

    try:
        config = TelemetryConfig.load()
    except FileNotFoundError:
        config = TelemetryConfig(user=str(uuid.uuid4()), consent=True)
        config.write()
        print(TELEMETRY_MESSAGE)
    except ValueError as e:
        _LOGGER.warning(e)
        return

    if not config.consent:
        return

    try:
        requests.post(
            _TELEMETRY_ENDPOINT,
            json={'user_id': config.user, 'event': event, 'properties': properties or {}},
            timeout=2,
        )
    except requests.exceptions.ReadTimeout:
        _LOGGER.debug(f'Telemetry event timed out: {event}')
    except Exception as e:
        _LOGGER.warning(f'Telemetry event failed: {event}', exc_info=e)
