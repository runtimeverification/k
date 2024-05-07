from __future__ import annotations

import logging
from abc import abstractmethod
from argparse import ArgumentParser
from pathlib import Path

#  from enum import Enum
from typing import TYPE_CHECKING, Any, Final, Generic, TypeVar

import tomli

from ..cli.utils import file_path

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

T = TypeVar('T')
OG = TypeVar('OG', bound='OptionsGroup')

_LOGGER: Final = logging.getLogger(__name__)

NO_DEFAULT: Final = object()


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
            for option in command._options_group.options:
                option.add_arg(command_args)
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
        stripped_args = {key: val for (key, val) in vars(args).items() if val != NO_DEFAULT}
        cmd = self.get_command(stripped_args)
        cmd._options_group.extract(stripped_args, cmd.name)
        cmd.exec()


class Option:
    _name: str
    _aliases: list[str]
    _dest: str
    _toml_name: str
    _action: str | None
    _choices: list[str] | None
    _const: Any | None
    _default: Any | None
    _help_str: str | None
    _metavar: str | None
    _nargs: int | str | None
    _required: bool
    _type: Callable[[str], Any]

    def __init__(
        self,
        name: str,
        arg_type: Callable[[str], Any],
        dest: str | None = None,
        help_str: str | None = None,
        action: str | None = None,
        choices: list[str] | None = None,
        const: Any | None = None,
        aliases: Iterable[str] = (),
        default: Any | str = NO_DEFAULT,
        metavar: str | None = None,
        nargs: int | str | None = None,
        required: bool = False,
        toml_name: str | None = None,
    ) -> None:
        self._name = name
        self._aliases = list(aliases)
        self._dest = dest or name
        self._toml_name = (toml_name or dest) or name
        self._action = action
        self._choices = choices
        self._const = const
        self._default = default
        self._help_str = help_str
        self._metavar = metavar
        self._nargs = nargs
        self._required = required
        self._type = arg_type

        self.set_default(default)

    def add_arg(self, args: ArgumentParser) -> None:

        params: dict[str, Any] = {}
        params['dest'] = self._dest
        params['type'] = self._type
        if self._action is not None:
            params['action'] = self._action
        if self._choices is not None:
            params['choices'] = self._choices
        if self._const is not None:
            params['const'] = self._const
        if self._default is not None:
            params['default'] = self._default
        if self._help_str is not None:
            params['help'] = self._help_str
        if self._metavar is not None:
            params['metavar'] = self._metavar
        if self._nargs is not None:
            params['nargs'] = self._nargs
        if self._required is not None:
            params['required'] = self._required

        args.add_argument(self._name, *(self._aliases), **params)

    def set_default(self, default: Any) -> None:
        self._default = default

    @property
    def name(self) -> str:
        return self._name

    @property
    def toml_name(self) -> str:
        return self._toml_name

    @property
    def default(self) -> Any:
        return self._default

    @property
    def is_optional(self) -> bool:
        return not self._required


class Command(Generic[OG]):
    _options_group: OG
    _name: str
    _help_str: str

    def __init__(self, name: str, help_str: str, options_group: OG) -> None:
        self._name = name
        self._help_str = help_str
        self._options_group = options_group

    @property
    def name(self) -> str:
        return self._name

    @property
    def help_str(self) -> str:
        return self._help_str

    @property
    def options(self) -> OG:
        return self._options_group

    @abstractmethod
    def exec(self) -> None: ...


def parse_toml_args(args: OptionsGroup, command: str) -> dict[str, Any]:
    def get_profile(toml_profile: dict[str, Any], profile_list: list[str]) -> dict[str, Any]:
        if len(profile_list) == 0 or profile_list[0] not in toml_profile:
            return {k: v for k, v in toml_profile.items() if type(v) is not dict}
        elif len(profile_list) == 1:
            return {k: v for k, v in toml_profile[profile_list[0]].items() if type(v) is not dict}
        return get_profile(toml_profile[profile_list[0]], profile_list[1:])

    toml_args = {}
    if args.config_file.is_file():
        with open(args.config_file, 'rb') as config_file:
            try:
                toml_args = tomli.load(config_file)
            except tomli.TOMLDecodeError:
                _LOGGER.error(
                    'Input config file is not in TOML format, ignoring the file and carrying on with the provided command line agruments'
                )

    toml_args = get_profile(toml_args[command], args.config_profile.split('.')) if command in toml_args else {}
    toml_args = {args.get_toml_name_destination(k): v for k, v in toml_args.items()}
    for k, v in toml_args.items():
        if k[:3] == 'no-' and (v == 'true' or v == 'false'):
            del toml_args[k]
            toml_args[k[3:]] = 'false' if v == 'true' else 'true'
        if k == 'optimization-level':
            level = toml_args[k] if toml_args[k] >= 0 else 0
            level = level if toml_args[k] <= 3 else 3
            del toml_args[k]
            toml_args['-o' + str(level)] = 'true'

    return toml_args


class OptionsGroup:
    _options: dict[str, Option]
    config_file: Path
    config_profile: str

    def __init__(self) -> None:
        self.add_option(
            Option('--config-file', file_path, 'config_file', 'Path to Pyk config file.', default=Path('./pyk.toml'))
        )
        self.add_option(
            Option('--config-profile', str, 'config_profile', 'Config profile to be used.', default='default')
        )

    def extract(self, args: dict[str, Any], command: str) -> None:

        toml_args = parse_toml_args(self, command)

        for option in self.options:
            if option.name in args:
                self.__setattr__(option.name, args[option.name])
            # TODO elif option exists in TOML file, set it to the value from there
            elif option.name in toml_args:
                self.__setattr__(option.name, toml_args[option.name])
            else:
                self.__setattr__(option.name, option.default)

    def add_option(self, option: Option) -> None:
        self._options[option.name] = option

    def override_default(self, option_name: str, value: T) -> None:
        if not self._options[option_name].is_optional:
            raise ValueError(f'Cannot provide a default value for a required parameter: {option_name}')
        if option_name not in self._options:
            raise ValueError(f'Cannot find option with name: {option_name}')
        self._options[option_name].set_default(value)

    @property
    def options(self) -> list[Option]:
        return list(self._options.values())

    def get_toml_name_destination(self, option_string: str) -> str:
        for option in self.options:
            if option.toml_name == option_string:
                return option.name
        raise ValueError(f'Cannot find option with toml_name {option_string}.')


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
