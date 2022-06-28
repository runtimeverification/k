from typing import Final

KEYWORDS: Final = {
    "module",
    "endmodule",
    "import",
    "sort",
    "hooked-sort",
    "symbol",
    "hooked-symbol",
    "axiom",
    "claim",
    "alias",
    "where",
}


_A_TO_Z_LC: Final = 'abcdefghijklmnopqrstuvwxyz'
_A_TO_Z_UC: Final = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
_0_TO_9: Final = '0123456789'

_ID_FST_CHR = set(_A_TO_Z_LC + _A_TO_Z_UC)
_ID_CHR = set(_0_TO_9 + "'-").union(_ID_FST_CHR)


def _has_id_syntax(s: str) -> bool:
    return len(s) > 0 and s[0] in _ID_FST_CHR and all(c in _ID_CHR for c in s[1:])


def is_id(s: str) -> bool:
    return _has_id_syntax(s) and s not in KEYWORDS


def is_symbol_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] == '\\':
        return _has_id_syntax(s[1:])

    return is_id(s)


def is_set_variable_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] != '@':
        return False

    return _has_id_syntax(s[1:])
