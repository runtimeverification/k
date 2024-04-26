from __future__ import annotations

from enum import Enum
from typing import Any, Generic, Iterable
from abc import ABC, abstractmethod
from argparse import ArgumentParser

T = TypeVar('T')
O = TypeVar('O', bound=Options)

class CLI:
    _commands: list[Command]

    def __init__(self, commands: Iterable[Command] = ()) -> None:
        self._commands = list(commands)

    def add_command(self, command: Command) -> None:
        self._commands.append(command)

    def create_argument_parser(self) -> ArgumentParser:
        args = ArgumentParser()
        subparsers = args.add_subparsers(dest='command', required=True)
        for command in self._commands:
            command_args = subparsers.add_parser(name=command.name, help=command.help_str)
            for option in command.options:

                if option.type is bool and option.is_optional:
                    command_args.add_argument(
                        option.cmd_line_name,
                        **(option.aliases),
                        default='NoDefault', 
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=options.metavar,
                        action='store_false' if option.default else 'store_true',
                        dest=option.name,
                    )
                elif isinstance(option.type, Enum) and option.is_optional:
                    command_args.add_argument(
                        option.cmd_line_name,
                        **(option.aliases),
                        default='NoDefault',
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=options.metavar,
                        dest=option.name,
                        choices=list(options.type),
                    )
                elif isinstance(option.type, Iterable) and option.is_optional:
                    command_args.add_argument(
                        option.cmd_line_name,
                        **(option.aliases),
                        default='NoDefault',
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=options.metavar,
                        action='append',
                        dest=option.name,
                    )
                else:
                    command_args.add_argument(
                        option.cmd_line_name,
                        **(option.aliases),
                        default='NoDefault',
                        required=(not options.is_optional),
                        type=option.type,
                        help=option.help_str,
                        metavar=options.metavar,
                        dest=option.name,
                    )
        return args

    def generate_command(self, args: dict[str, Any]) -> Command

    def get_command(self) -> Command:
        parser = self.create_argument_parser()
        args = parser.parse_args()
        stripped_args = {
            key: val
            for (key, val) in vars(args).items()
            if val != 'NoDefault'
        }
        return self.generate_command(stripped_args)


    def get_and_exec_command(self) -> None:
        cmd = self.get_command()
        cmd.exec()


class Option(Generic[T]):
    _name: str
    _aliases: list[str]
    _cmd_line_name: str
    _toml_name: str
    _optional: bool
    _help_str: str | None
    _metavar: str | None
    _default: T

    def __init__(
        self,
        name: str,
        aliases: Iterable[str] = (),
        cmd_line_name: str | None = None,
        toml_name: str | None = None,
        optional: bool = False,
        help_str: str | None = None,
        metavar: str | None = None,
        default: T | str = 'NoDefault',
    ) -> None:
        self._name = name,
        self._aliases = list(aliases)
        self._cmd_line_name = cmd_line_name or name
        self._toml_name = cmd_line_name or name
        self._optional = optional
        self._help_str = help_str
        self._metavar = metavar

        if default == 'NoDefault' and optional:
            raise ValueError(f'Optional option {name} must define a default value.')
        if default != 'NoDefault' and not optional:
            raise ValueError(f'Required option {name} cannot take a default value.')

        self._default = default

    @property
    def is_optional(self) -> bool:
        return self._optional

    @property
    def name(self) -> str:
        return self._name

    @property
    def aliases(self) -> list[str]:
        return self._aliases

    @property
    def cmd_line_name(self) -> str:
        return self._cmd_line_name

    @property
    def toml_name(self) -> str:
        return self._toml_name

    @property
    def help_str(self) -> str:
        return self._help_str

    @property
    def metavar(self) -> str:
        return self._metavar

    @property
    def type(self) -> str:
        return T

class Command:
    _options: Options
    _name: str
    _help_str: str

    @property
    def name(self) -> str:
        return self._name

    @property
    def help_str(self) -> str:
        return self._help_str

    @property
    def options(self) -> Options:
        return self._options

    @abstractmethod
    def exec(self) -> None:
        ...

class Options:
    _options: dict[str, Option]

    def add_option(self, option: Option) -> dict[str, Any]:
        self._options[option.name] = option

    def override_default(self, option_name: str, value: T) -> None:
        if not self._options[option_name].is_optional:
            raise ValueError(f'Cannot provide a default value for a required parameter: {option_name}')
