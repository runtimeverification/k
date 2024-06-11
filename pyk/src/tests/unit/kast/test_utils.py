from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import KDefinition
from pyk.kast.utils import parse_outer

from ..utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final


PARSE_OUTER_TEST_DIR: Final = TEST_DATA_DIR / 'parse-outer'
PARSE_OUTER_TEST_FILES: Final = (*PARSE_OUTER_TEST_DIR.glob('*.k'), *PARSE_OUTER_TEST_DIR.glob('*.md'))


@pytest.mark.parametrize('test_file', PARSE_OUTER_TEST_FILES, ids=[id for id, _ in enumerate(PARSE_OUTER_TEST_FILES)])
def test_parse_outer(test_file: Path) -> None:
    # Given
    expected_file = test_file.with_suffix(test_file.suffix + '.expected.json')
    expected = KDefinition.from_dict(json.loads(expected_file.read_text()))
    main_module = test_file.stem.upper()

    # When
    actual = parse_outer(
        test_file,
        main_module,
        include_dirs=[test_file.parent / 'include'],
        include_source=False,
    )

    # Then
    assert actual == expected
