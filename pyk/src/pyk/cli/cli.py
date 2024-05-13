from __future__ import annotations

from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from collections.abc import Callable


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

    @staticmethod
    def get_argument_type() -> dict[str, Callable]:
        return {}
