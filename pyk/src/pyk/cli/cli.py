from __future__ import annotations

from abc import abstractmethod
from argparse import ArgumentParser
from enum import Enum
from typing import Any, Generic, Iterable, TypeVar

T = TypeVar('T')


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
                        *(option.aliases),
                        default='NoDefault',
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=option.metavar,
                        action='store_false' if option.default else 'store_true',
                        dest=option.name,
                    )
                elif issubclass(option.type, Enum) and option.is_optional:
                    command_args.add_argument(
                        option.cmd_line_name,
                        *(option.aliases),
                        default='NoDefault',
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=option.metavar,
                        dest=option.name,
                        choices=list(option.type),
                    )
                elif isinstance(option.type, Iterable) and option.is_optional:
                    command_args.add_argument(
                        option.cmd_line_name,
                        *(option.aliases),
                        default='NoDefault',
                        required=False,
                        type=option.type,
                        help=option.help_str,
                        metavar=option.metavar,
                        action='append',
                        dest=option.name,
                    )
                else:
                    command_args.add_argument(
                        option.cmd_line_name,
                        *(option.aliases),
                        default='NoDefault',
                        required=(not option.is_optional),
                        type=option.type,
                        help=option.help_str,
                        metavar=option.metavar,
                        dest=option.name,
                    )
        return args

    def get_command(self, args: dict[str, Any]) -> Command:
        command_name = args['command'].lower()
        for command in self._commands:
            if command.name.lower() == command_name:
                return command
        raise ValueError(f'Commmand {command_name} not found.')

    def get_and_exec_command(self) -> None:
        parser = self.create_argument_parser()
        args = parser.parse_args()
        stripped_args = {key: val for (key, val) in vars(args).items() if val != 'NoDefault'}
        cmd = self.get_command(stripped_args)
        cmd.extract(stripped_args)
        cmd.exec()


class Option(Generic[T]):
    _name: str
    _aliases: list[str]
    _cmd_line_name: str
    _toml_name: str
    _optional: bool
    _help_str: str | None
    _metavar: str | None
    _default: T | str
    _type: type[Any]

    def __init__(
        self,
        name: str,
        type: type[Any],
        aliases: Iterable[str] = (),
        cmd_line_name: str | None = None,
        toml_name: str | None = None,
        optional: bool = False,
        help_str: str | None = None,
        metavar: str | None = None,
        default: T | str = 'NoDefault',
    ) -> None:
        self._name = name
        self._aliases = list(aliases)
        self._cmd_line_name = cmd_line_name or name
        self._toml_name = cmd_line_name or name
        self._optional = optional
        self._help_str = help_str
        self._metavar = metavar
        self._type = type

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
    def help_str(self) -> str | None:
        return self._help_str

    @property
    def metavar(self) -> str | None:
        return self._metavar

    @property
    def default(self) -> T | str:
        return self._default

    @property
    def type(self) -> type:
        return self._type


class Command:
    _options_group: OptionsGroup
    _name: str
    _help_str: str

    def extract(self, args: dict[str, Any]) -> None:
        for option in self._options_group.options:
            if option.name in args:
                assert isinstance(args[option.name], option.type)
                self.__setattr__(option.name, args[option.name])
            # TODO elif option exists in TOML file, set it to the value from there
            else:
                self.__setattr__(option.name, option.default)

    @property
    def name(self) -> str:
        return self._name

    @property
    def help_str(self) -> str:
        return self._help_str

    @property
    def options(self) -> list[Option]:
        return self._options_group.options

    @abstractmethod
    def exec(self) -> None: ...


class OptionsGroup:
    _options: dict[str, Option]

    def add_option(self, option: Option) -> None:
        self._options[option.name] = option

    def override_default(self, option_name: str, value: T) -> None:
        if not self._options[option_name].is_optional:
            raise ValueError(f'Cannot provide a default value for a required parameter: {option_name}')

    @property
    def options(self) -> list[Option]:
        return list(self._options.values())


# TODO remove once all implementing semantics use `CLI` system
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

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {}
