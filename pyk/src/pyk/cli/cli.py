from __future__ import annotations

from typing import Any, Generic, Iterable
from abc import ABC, abstractmethod

T = TypeVar('T')
O = TypeVar('O', bound=Options)

class CLI:
    _command_handlers: list[OptionsHandler]

    def __init__(self, command_handlers: Iterable[OptionsHandler] = ()) -> None:
        self._command_handlers = list(command_handlers)

    def add_command(self, command_handler: OptionsHandler) -> None:
        self._command_handlers.append(command_handler)


class Option(Generic[T]):
    _name: str
    _cmd_line_name: str
    _toml_name: str
    _optional: bool
    _help_str: str | None
    _default: T

    def __init__(
        self,
        name: str,
        cmd_line_name: str | None = None,
        toml_name: str | None = None,
        optional: bool = False,
        help_str: str | None = None,
        default: T | str = 'NoDefault',
    ) -> None:
        self._name = name,
        self._cmd_line_name = cmd_line_name or name
        self._toml_name = cmd_line_name or name
        self._optional = optional
        self._help_str = help_str

        if default == 'NoDefault' and optional:
            raise ValueError(f'Optional option {name} must define a default value.')
        if default != 'NoDefault' and not optional:
            raise ValueError(f'Required option {name} cannot take a default value.')

        self._default = default


class OptionsHandler(Generic[O], ABC):

    def add_option(self, ) -> dict[str, Any]:
        ...

    @abstractmethod
    def default(self) -> dict[str, Any]:
        ...


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
