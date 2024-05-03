from __future__ import annotations

from abc import abstractmethod
from argparse import ArgumentParser

#  from enum import Enum
from typing import Any, Callable, Generic, Iterable, TypeVar

T = TypeVar('T')
OG = TypeVar('OG', bound='OptionsGroup')


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
        stripped_args = {key: val for (key, val) in vars(args).items() if val != 'NoDefault'}
        cmd = self.get_command(stripped_args)
        cmd._options_group.extract(stripped_args)
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
        default: Any | str = 'NoDefault',
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


class OptionsGroup:
    _options: dict[str, Option]

    def extract(self, args: dict[str, Any]) -> None:
        for option in self.options:
            if option.name in args:
                self.__setattr__(option.name, args[option.name])
            # TODO elif option exists in TOML file, set it to the value from there
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
