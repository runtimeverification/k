from __future__ import annotations

import logging
import re
from collections import defaultdict
from enum import Enum
from typing import TYPE_CHECKING

from ..kast import Atts

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from ..kast.outer import KDefinition, KRule


_LOG_FORMAT: Final = '%(levelname)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)

_HASKELL_LOG_ENTRY_REGEXP: Final = re.compile(r'(kore-exec|kore-rpc): \[\d*\] Debug \(([a-zA-Z]*)\):(.*)')


class HaskellLogEntry(Enum):
    DEBUG_APPLY_EQUATION = 'DebugApplyEquation'
    DEBUG_APPLIED_REWRITE_RULES = 'DebugAppliedRewriteRules'


def parse_rule_applications(haskell_backend_oneline_log_file: Path) -> dict[HaskellLogEntry, dict[str, int]]:
    """Process a one-line log file produced by K's Haskell backend.

    Extracts information about:

    - Applied rewrites (DebugAppliedRewriteRules).
    - Applied simplifications (DEBUG_APPLY_EQUATION).

    Note:
        Haskell backend logs often contain rule applications with empty locations.
        It seems likely that those are generated projection rules.
        We report their applications in bulk with UNKNOWN location.
    """
    rewrites: dict[str, int] = defaultdict(int)
    simplifications: dict[str, int] = defaultdict(int)

    log_entries = haskell_backend_oneline_log_file.read_text().splitlines()
    for log_entry in log_entries:
        parsed = _parse_haskell_oneline_log(log_entry)
        if parsed:
            entry_type, location_str = parsed
        else:
            _LOGGER.warning(f'Skipping log entry, failed to parse: {log_entry}')
            continue
        if location_str == '':
            location_str = 'UNKNOWN'
        if entry_type == HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES:
            rewrites[location_str] += 1
        else:
            assert entry_type == HaskellLogEntry.DEBUG_APPLY_EQUATION
            simplifications[location_str] += 1
    return {
        HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES: rewrites,
        HaskellLogEntry.DEBUG_APPLY_EQUATION: simplifications,
    }


def _parse_haskell_oneline_log(log_entry: str) -> tuple[HaskellLogEntry, str] | None:
    """Attempt to parse a one-line log string emmitted by K's Haskell backend."""
    matches = _HASKELL_LOG_ENTRY_REGEXP.match(log_entry)
    try:
        assert matches
        entry = matches.groups()[1]
        location_str = matches.groups()[2].strip()
        return HaskellLogEntry(entry), location_str
    except (AssertionError, KeyError, ValueError):
        return None


def build_rule_dict(
    definition: KDefinition, *, skip_projections: bool = True, skip_initializers: bool = True
) -> dict[str, KRule]:
    """Traverse the kompiled definition and build a dictionary mapping str(file:location) to KRule."""
    rule_dict: dict[str, KRule] = {}

    for rule in definition.rules:
        if skip_projections and Atts.PROJECTION in rule.att:
            continue
        if skip_initializers and Atts.INITIALIZER in rule.att:
            continue
        try:
            rule_source = rule.att[Atts.SOURCE]
            rule_location = rule.att[Atts.LOCATION]
        except KeyError:
            _LOGGER.warning(f'Skipping rule with no location information {str(rule.body):.100}...<truncated>')
            rule_source = None
            rule_location = None
            continue
        if rule_source and rule_location:
            rule_dict[f'{rule_source}:{_location_tuple_to_str(rule_location)}'] = rule
        else:
            raise ValueError(str(rule.body))

    return rule_dict


def _location_tuple_to_str(location: tuple[int, int, int, int]) -> str:
    start_line, start_col, end_line, end_col = location
    return f'{start_line}:{start_col}-{end_line}:{end_col}'
