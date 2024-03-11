from __future__ import annotations

from abc import ABC, abstractmethod
from argparse import ArgumentParser
from collections.abc import Iterable
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from argparse import _SubParsersAction


class CLI:
    commands: list[type[Command]]
    top_level_args: Iterable[type[Options]]

    # Input a list of all Command types to be used
    def __init__(self, commands: Iterable[type[Command]], top_level_args: Iterable[type[Options]] = ()):
        self.commands = list(commands)
        self.top_level_args = top_level_args

    # Return an instance of the correct Options subclass by matching its name with the requested command
    def generate_command(self, args: dict[str, Any]) -> Command:
        command = args['command'].lower()
        for cmd_type in self.commands:
            if cmd_type.name() == command:
                if issubclass(cmd_type, Options):
                    return cmd_type(args)
                else:
                    return cmd_type()
        raise ValueError(f'Unrecognized command: {command}')

    # Generate the parsers for all commands
    def add_parsers(self, base: _SubParsersAction) -> _SubParsersAction:
        for cmd_type in self.commands:
            base = cmd_type.parser(base)
        return base

    def create_argument_parser(self) -> ArgumentParser:
        pyk_args = ArgumentParser(parents=[tla.all_args() for tla in self.top_level_args])
        pyk_args_command = pyk_args.add_subparsers(dest='command', required=True)

        pyk_args_command = self.add_parsers(pyk_args_command)

        return pyk_args

    def get_command(self) -> Command:
        parser = self.create_argument_parser()
        args = parser.parse_args()
        stripped_args = {
            key: val
            for (key, val) in vars(args).items()
            if val is not None and not (isinstance(val, Iterable) and not val)
        }
        return self.generate_command(stripped_args)

    def get_and_exec_command(self) -> None:
        cmd = self.get_command()
        cmd.exec()


class Command(ABC):
    @staticmethod
    @abstractmethod
    def name() -> str:
        ...

    @staticmethod
    @abstractmethod
    def help_str() -> str:
        ...

    @abstractmethod
    def exec(self) -> None:
        ...

    @classmethod
    def parser(cls, base: _SubParsersAction) -> _SubParsersAction:
        all_args = [cls.all_args()] if issubclass(cls, Options) else []
        base.add_parser(
            name=cls.name(),
            help=cls.help_str(),
            parents=all_args,
        )
        return base


class Options:
    def __init__(self, args: dict[str, Any]) -> None:
        # Get defaults from this and all superclasses that define them, preferring the most specific class
        defaults: dict[str, Any] = {}
        for cl in reversed(type(self).mro()):
            if hasattr(cl, 'default'):
                defaults = defaults | cl.default()

        # Overwrite defaults with args from command line
        _args = defaults | args

        for attr, val in _args.items():
            self.__setattr__(attr, val)

    @classmethod
    def all_args(cls: type[Options]) -> ArgumentParser:
        # Collect args from this and all superclasses
        parser = ArgumentParser(add_help=False)
        mro = cls.mro()
        mro.reverse()
        for cl in mro:
            if hasattr(cl, 'update_args') and 'update_args' in cl.__dict__:
                cl.update_args(parser)
        return parser
