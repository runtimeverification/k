from argparse import ArgumentParser

from ..cli_utils import file_path
from .app import KcfgViewer


def main() -> None:
    args = argument_parser().parse_args()
    viewer = KcfgViewer(args.kcfg_file)
    viewer.run()


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='KCFG Viewer')
    parser.add_argument('kcfg_file', type=file_path, metavar='FILE', help='KCFG JSON file')
    return parser


if __name__ == '__main__':
    main()
