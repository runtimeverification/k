from pyk.ktool import KompileBackend

from .kompiled_test import KompiledTest


class SimpleKompileTest(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_EMIT_JSON = True

    def test(self) -> None:
        pass
