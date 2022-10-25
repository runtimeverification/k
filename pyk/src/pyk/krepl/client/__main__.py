from argparse import ArgumentParser

from . import DEFAULT_PORT, Repl


def main() -> None:
    args = argument_parser().parse_args()
    try:
        Repl(args.host, args.port).cmdloop()
    except KeyboardInterrupt:
        ...


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Client')
    parser.add_argument('-s', '--host', type=str, default='localhost', help='server host (default: localhost)')
    parser.add_argument('-p', '--port', type=int, default=DEFAULT_PORT, help=f'server port (default: {DEFAULT_PORT})')
    return parser


if __name__ == '__main__':
    main()
