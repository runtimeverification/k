from pathlib import Path
from pyk.kcfg import KCFG, KCFGViewer
from pyk.ktool.kprint import KPrint

TEST_DATA_DIR = Path('/Users/steven/Desktop/projs/cse/k/pyk/src/tests/unit/test-data')
if __name__ == '__main__':
    kcfg = KCFG.read_cfg_data(TEST_DATA_DIR / 'proof-files' / 'cse_f' / 'expected_kcfg')
    printer = KPrint(TEST_DATA_DIR / 'proof-files' / 'cse_f' / 'kdef' / 'kompiled')
    viewer = KCFGViewer(kcfg, printer)
    viewer.run()

