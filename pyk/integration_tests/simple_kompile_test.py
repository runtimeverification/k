from kompiled_test import KompiledTest

from pyk.ktool import KompileBackend


class SimpleKompileTest(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp/haskell'
    KOMPILE_EMIT_JSON = True

    def test(self):
        pass
