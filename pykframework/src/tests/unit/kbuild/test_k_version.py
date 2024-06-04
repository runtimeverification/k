import pytest

from pykframework.kbuild.utils import KVersion

VALID_TEST_DATA = (
    ('v5.4.7', KVersion(5, 4, 7, None)),
    ('v5.4.7-0-g0b0189cc60', KVersion(5, 4, 7, KVersion.Git(0, '0b0189cc60', False))),
    ('v5.4.7-0-g0b0189cc60-dirty', KVersion(5, 4, 7, KVersion.Git(0, '0b0189cc60', True))),
)


@pytest.mark.parametrize('version,expected', VALID_TEST_DATA, ids=[version for version, _ in VALID_TEST_DATA])
def test_parse_valid(version: str, expected: KVersion) -> None:
    # When
    actual = KVersion.parse(version)

    # Then
    assert actual == expected
    assert actual.text == version


INVALID_TEST_DATA = (
    '',
    'a',
    '1',
    '1.2',
    '1.2',
    '1.2.3',
    'v1.2.3-dirty',
    'v1.2.3-10',
    'v1.2.3-10-dirty',
    'v1.2.3-10-0123',
    'v1.2.3-a-0123456789',
    'v1.2.3-10-0123456789',
)


@pytest.mark.parametrize('version', INVALID_TEST_DATA)
def test_parse_invalid(version: str) -> None:
    with pytest.raises(ValueError) as excinfo:
        # When
        KVersion.parse(version)

    # Then
    assert str(excinfo.value) == f'Invalid K version string: {version}'
