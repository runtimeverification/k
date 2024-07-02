from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore_exec_covr.kore_exec_covr import HaskellLogEntry, _parse_haskell_oneline_log, parse_rule_applications

if TYPE_CHECKING:
    from pytest import TempPathFactory


PARSE_HASKELL_ONELINE_LOG_TEST_DATA = [
    (
        'DebugApplyEquation-empty',
        'kore-exec: [1] Debug (DebugApplyEquation):',
        (HaskellLogEntry.DEBUG_APPLY_EQUATION, ''),
    ),
    (
        'DebugApplyEquation-location',
        r'kore-exec: [2] Debug (DebugApplyEquation): /some/path\ with \ spaces/domains.md:1:2-3:4',
        (HaskellLogEntry.DEBUG_APPLY_EQUATION, r'/some/path\ with \ spaces/domains.md:1:2-3:4'),
    ),
    (
        'DebugAppliedRewriteRules-empty',
        'kore-exec: [3] Debug (DebugAppliedRewriteRules):',
        (HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES, ''),
    ),
    (
        'DebugAppliedRewriteRules-location',
        r'kore-exec: [4] Debug (DebugAppliedRewriteRules): /some/path\ with \ spaces/domains.md:1:2-3:4',
        (HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES, r'/some/path\ with \ spaces/domains.md:1:2-3:4'),
    ),
    (
        'DebugAppliedRewriteRules-multilocation',
        r'kore-exec: [5] Debug (DebugAppliedRewriteRules): /some/path\ with \ spaces/domains.md:1:2-3:4 /some/other/path\ with \ spaces/domains.md:5:6-7:8',
        (
            HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES,
            r'/some/path\ with \ spaces/domains.md:1:2-3:4 /some/other/path\ with \ spaces/domains.md:5:6-7:8',
        ),
    ),
]


@pytest.mark.parametrize(
    'test_id,log_line,expected',
    PARSE_HASKELL_ONELINE_LOG_TEST_DATA,
    ids=[test_id for test_id, *_ in PARSE_HASKELL_ONELINE_LOG_TEST_DATA],
)
def test_parse_haskell_oneline_log(test_id: str, log_line: str, expected: tuple[HaskellLogEntry, str]) -> None:
    # When
    actual = _parse_haskell_oneline_log(log_line)

    # Then
    assert actual == expected


PARSE_RULE_APPLICATIONS_TEST_DATA = [
    ('empty', '', {HaskellLogEntry.DEBUG_APPLY_EQUATION: {}, HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES: {}}),
    (
        'rewrites-and-simplifications',
        '\n'.join(
            [
                'kore-exec: [3] Debug (DebugAppliedRewriteRules):',
                r'kore-exec: [2] Debug (DebugAppliedRewriteRules): /some/path\ with \ spaces/domains.md:1:2-3:4',
                r'kore-exec: [2] Debug (DebugApplyEquation): /some/path\ with \ spaces/domains.md:1:2-3:4',
                'kore-exec: [1] Debug (DebugApplyEquation):',
            ]
        ),
        {
            HaskellLogEntry.DEBUG_APPLY_EQUATION: {'UNKNOWN': 1, r'/some/path\ with \ spaces/domains.md:1:2-3:4': 1},
            HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES: {
                'UNKNOWN': 1,
                r'/some/path\ with \ spaces/domains.md:1:2-3:4': 1,
            },
        },
    ),
]


@pytest.mark.parametrize(
    'test_id,haskell_rule_log,expected',
    PARSE_RULE_APPLICATIONS_TEST_DATA,
    ids=[test_id for test_id, *_ in PARSE_RULE_APPLICATIONS_TEST_DATA],
)
def test_parse_rule_applications(
    test_id: str,
    haskell_rule_log: str,
    expected: dict[HaskellLogEntry, dict[str, int]],
    tmp_path_factory: TempPathFactory,
) -> None:
    # Given
    applied_log_file = tmp_path_factory.mktemp('data') / 'applied.log'
    applied_log_file.write_text(haskell_rule_log)

    # When
    actual = parse_rule_applications(applied_log_file)

    # Then
    assert actual == expected
