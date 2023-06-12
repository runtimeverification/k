from argparse import ArgumentParser

from ..cli.utils import dir_path
from .repl import KRepl


def main() -> None:
    args = argument_parser().parse_args()
    repl = KRepl(args.definition_dir)
    repl.cmdloop()


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Shell')
    parser.add_argument('definition_dir', type=dir_path, metavar='DEFINITION')
    return parser


if __name__ == '__main__':
    main()
