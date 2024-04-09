from pyk.kbuild.utils import KVersion, k_version


def test_k_version() -> None:
    # When
    version1 = k_version()
    version2 = KVersion.parse(version1.text)

    # Then
    assert version1 == version2
