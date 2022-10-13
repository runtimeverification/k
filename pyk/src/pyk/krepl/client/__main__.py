from argparse import ArgumentParser

from . import DEFAULT_PORT, Repl


def main() -> None:
    args = argument_parser().parse_args()
    try:
        Repl(args.port).cmdloop()
    except KeyboardInterrupt:
        ...


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Client')
    parser.add_argument('-p', '--port', type=int, default=DEFAULT_PORT, help='server port')
    return parser


if __name__ == '__main__':
    main()
