from __future__ import annotations

import logging
import os
import uuid
from pathlib import Path
from typing import Final

import requests
import tomli
import tomli_w

_LOGGER: Final = logging.getLogger(__name__)

KPROFILE_CONFIG_DIR: Final = Path.home() / '.config' / 'kprofile'
KPROFILE_CONFIG_FILE: Final = KPROFILE_CONFIG_DIR / 'config.toml'
TELEMETRY_MESSAGE: Final = (
    f'Telemetry: sending anonymous usage data. You can opt out by setting KPROFILE_TELEMETRY_DISABLED=true'
    f' or by setting consent=false in {KPROFILE_CONFIG_FILE}'
)


def _load_config() -> tuple[str, bool]:
    """Load or create the kprofile config, returning (user_id, consent)."""
    if not KPROFILE_CONFIG_FILE.exists():
        KPROFILE_CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
        config = {'user': {'user_id': str(uuid.uuid4()), 'consent': True}}
        with open(KPROFILE_CONFIG_FILE, 'wb') as f:
            tomli_w.dump(config, f)
        print(TELEMETRY_MESSAGE)
        return str(config['user']['user_id']), True

    with open(KPROFILE_CONFIG_FILE, 'rb') as f:
        config = tomli.load(f)

    user = config.get('user', {})
    return str(user['user_id']), bool(user.get('consent', True))


def emit_event(event: str, properties: dict | None = None) -> None:
    """Send a telemetry event to the proxy server.

    Args:
        event: Event name to track.
        properties: Optional key/value metadata (e.g. ``{'version': '1.2.3'}``).
    """
    if os.getenv('KPROFILE_TELEMETRY_DISABLED', '').lower() == 'true':
        return

    user_id, consent = _load_config()
    if not consent:
        return

    try:
        requests.post(
            'https://ojlk1fzi13.execute-api.us-east-1.amazonaws.com/dev/track',
            json={'user_id': user_id, 'event': event, 'properties': properties or {}},
            timeout=2,
        )
    except requests.exceptions.ReadTimeout:
        _LOGGER.debug(f'Telemetry event timed out: {event}')
    except Exception as e:
        _LOGGER.warning(f'Telemetry event failed: {event}', exc_info=e)
