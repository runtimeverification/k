from .kompiled_test import KompiledTest


class SimpleKompileTest(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'

    def test(self) -> None:
        pass
