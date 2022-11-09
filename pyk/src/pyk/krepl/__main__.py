from argparse import ArgumentParser

from ..cli_utils import dir_path
from .repl import KDebugger, KRepl


def main() -> None:
    args = argument_parser().parse_args()
    debugger = KDebugger(args.definition_dir)
    repl = KRepl(debugger)
    repl.cmdloop()


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Shell')
    parser.add_argument('definition_dir', type=dir_path, metavar='DEFINITION')
    return parser


if __name__ == '__main__':
    main()
