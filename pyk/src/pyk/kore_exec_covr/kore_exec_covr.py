import logging
import re
from collections import defaultdict
from enum import Enum
from pathlib import Path
from typing import Dict, Final, Optional, Tuple

from pyk.kast.kast import KAtt
from pyk.kast.outer import KDefinition, KRule

_LOG_FORMAT: Final = '%(levelname)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)

_HASKELL_LOG_ENTRY_REGEXP: Final = re.compile(r'kore-exec: \[\d*\] Debug \(([a-zA-Z]*)\):(.*)')


class HaskellLogEntry(Enum):
    DEBUG_APPLY_EQUATION = 'DebugApplyEquation'
    DEBUG_APPLIED_REWRITE_RULES = 'DebugAppliedRewriteRules'


def parse_rule_applications(haskell_backend_oneline_log_file: Path) -> Dict[HaskellLogEntry, Dict[str, int]]:
    """
    Traverse a one-line log file produced by K's Haskell backend and extract information about:
    * applied rewrites (DebugAppliedRewriteRules)
    * applied simplifications (DEBUG_APPLY_EQUATION)

    Note: Haskell backend logs often contain rule applications with empty locations.
          It seems likely that those are generated projection rules.
          We report their applications in bulk with UNKNOWN location.
    """
    rewrites: Dict[str, int] = defaultdict(int)
    simplifications: Dict[str, int] = defaultdict(int)

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


def _parse_haskell_oneline_log(log_entry: str) -> Optional[Tuple[HaskellLogEntry, str]]:
    """Attempt to parse a one-line log string emmitted by K's Haskell backend"""
    matches = _HASKELL_LOG_ENTRY_REGEXP.match(log_entry)
    try:
        assert matches
        entry = matches.groups()[0]
        location_str = matches.groups()[1].strip()
        return HaskellLogEntry(entry), location_str
    except (AssertionError, KeyError, ValueError):
        return None


def build_rule_dict(
    definition: KDefinition, *, skip_projections: bool = True, skip_initializers: bool = True
) -> Dict[str, KRule]:
    """
    Traverse the kompiled definition and build a dictionary mapping str(file:location) to KRule
    """
    rule_dict: Dict[str, KRule] = {}

    for rule in definition.rules:
        if skip_projections and 'projection' in rule.att.atts:
            continue
        if skip_initializers and 'initializer' in rule.att.atts:
            continue
        try:
            rule_source = rule.att.atts[KAtt.SOURCE]
            rule_location = rule.att.atts[KAtt.LOCATION]
        except KeyError:
            _LOGGER.warning(
                'Skipping rule with no location information {msg:.100}...<truncated>'.format(msg=str(rule.body))
            )
            rule_source = None
            rule_location = None
            continue
        if rule_source and rule_location:
            rule_dict[f'{rule_source}:{_location_tuple_to_str(rule_location)}'] = rule
        else:
            raise ValueError(str(rule.body))

    return rule_dict


def _location_tuple_to_str(location: Tuple[int, int, int, int]) -> str:
    start_line, start_col, end_line, end_col = location
    return f'{start_line}:{start_col}-{end_line}:{end_col}'
