from __future__ import annotations

import re
from collections.abc import Iterator
from enum import Enum, auto
from typing import TYPE_CHECKING, NamedTuple

if TYPE_CHECKING:
    from collections.abc import Collection, Generator, Iterable
    from typing import Final


class TokenType(Enum):
    EOF = 0
    COMMA = auto()
    LPAREN = auto()
    RPAREN = auto()
    LBRACE = auto()
    RBRACE = auto()
    LBRACK = auto()
    RBRACK = auto()
    VBAR = auto()
    EQ = auto()
    GT = auto()
    PLUS = auto()
    TIMES = auto()
    QUESTION = auto()
    TILDE = auto()
    COLON = auto()
    DCOLONEQ = auto()
    KW_ALIAS = auto()
    KW_CLAIM = auto()
    KW_CONFIG = auto()
    KW_CONTEXT = auto()
    KW_ENDMODULE = auto()
    KW_IMPORTS = auto()
    KW_LEFT = auto()
    KW_LEXICAL = auto()
    KW_MODULE = auto()
    KW_NONASSOC = auto()
    KW_PRIORITY = auto()
    KW_PRIVATE = auto()
    KW_PUBLIC = auto()
    KW_REQUIRES = auto()
    KW_RIGHT = auto()
    KW_RULE = auto()
    KW_SYNTAX = auto()
    NAT = auto()
    STRING = auto()
    REGEX = auto()
    ID_LOWER = auto()
    ID_UPPER = auto()
    MODNAME = auto()
    KLABEL = auto()
    RULE_LABEL = auto()
    ATTR_KEY = auto()
    ATTR_CONTENT = auto()
    BUBBLE = auto()


class Loc(NamedTuple):
    line: int
    col: int

    def __add__(self, other: object) -> Loc:
        if isinstance(other, str):
            """Return the line,column after the additional text"""
            line, col = self.line, self.col
            for c in other:
                if c == '\n':
                    line += 1
                    col = 0
                col += 1
            return Loc(line, col)
        return NotImplemented


INIT_LOC: Final = Loc(1, 0)


class Token(NamedTuple):
    text: str
    type: TokenType
    loc: Loc

    def let(self, *, text: str | None = None, type: TokenType | None = None, loc: Loc | None = None) -> Token:
        text = text if text else self.text
        type = type if type else self.type
        loc = loc if loc else self.loc
        return Token(text=text, type=type, loc=loc)


_EOF_TOKEN: Final = Token('', TokenType.EOF, INIT_LOC)

_SIMPLE_CHARS: Final = {
    ',': TokenType.COMMA,
    '(': TokenType.LPAREN,
    ')': TokenType.RPAREN,
    '[': TokenType.LBRACK,
    ']': TokenType.RBRACK,
    '>': TokenType.GT,
    '{': TokenType.LBRACE,
    '}': TokenType.RBRACE,
    '|': TokenType.VBAR,
    '=': TokenType.EQ,
    '+': TokenType.PLUS,
    '*': TokenType.TIMES,
    '?': TokenType.QUESTION,
    '~': TokenType.TILDE,
}

_KEYWORDS: Final = {
    'alias': TokenType.KW_ALIAS,
    'claim': TokenType.KW_CLAIM,
    'configuration': TokenType.KW_CONFIG,
    'context': TokenType.KW_CONTEXT,
    'endmodule': TokenType.KW_ENDMODULE,
    'imports': TokenType.KW_IMPORTS,
    'left': TokenType.KW_LEFT,
    'lexical': TokenType.KW_LEXICAL,
    'module': TokenType.KW_MODULE,
    'non-assoc': TokenType.KW_NONASSOC,
    'priority': TokenType.KW_PRIORITY,
    'private': TokenType.KW_PRIVATE,
    'public': TokenType.KW_PUBLIC,
    'requires': TokenType.KW_REQUIRES,
    'right': TokenType.KW_RIGHT,
    'rule': TokenType.KW_RULE,
    'syntax': TokenType.KW_SYNTAX,
}

_WHITESPACE: Final = {' ', '\t', '\n', '\r'}
_DIGIT: Final = set('0123456789')
_LOWER: Final = set('abcdefghijklmnopqrstuvwxyz')
_UPPER: Final = set('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
_ALPHA: Final = _LOWER.union(_UPPER)
_ALNUM: Final = _ALPHA.union(_DIGIT)
_WORD: Final = {'_'}.union(_ALNUM)


class State(Enum):
    DEFAULT = auto()
    SYNTAX = auto()
    KLABEL = auto()
    BUBBLE = auto()
    CONTEXT = auto()
    ATTR = auto()
    MODNAME = auto()


_NEXT_STATE: Final = {
    # (state, token_type): state'
    (State.BUBBLE, TokenType.KW_CLAIM): State.BUBBLE,
    (State.BUBBLE, TokenType.KW_CONFIG): State.BUBBLE,
    (State.BUBBLE, TokenType.KW_CONTEXT): State.CONTEXT,
    (State.BUBBLE, TokenType.KW_ENDMODULE): State.DEFAULT,
    (State.BUBBLE, TokenType.KW_RULE): State.BUBBLE,
    (State.BUBBLE, TokenType.KW_SYNTAX): State.SYNTAX,
    (State.CONTEXT, TokenType.KW_ALIAS): State.BUBBLE,
    (State.CONTEXT, TokenType.KW_CLAIM): State.BUBBLE,
    (State.CONTEXT, TokenType.KW_CONFIG): State.BUBBLE,
    (State.CONTEXT, TokenType.KW_CONTEXT): State.CONTEXT,
    (State.CONTEXT, TokenType.KW_ENDMODULE): State.DEFAULT,
    (State.CONTEXT, TokenType.KW_RULE): State.BUBBLE,
    (State.CONTEXT, TokenType.KW_SYNTAX): State.SYNTAX,
    (State.DEFAULT, TokenType.KW_CLAIM): State.BUBBLE,
    (State.DEFAULT, TokenType.KW_CONFIG): State.BUBBLE,
    (State.DEFAULT, TokenType.KW_CONTEXT): State.CONTEXT,
    (State.DEFAULT, TokenType.KW_IMPORTS): State.MODNAME,
    (State.DEFAULT, TokenType.KW_MODULE): State.MODNAME,
    (State.DEFAULT, TokenType.KW_RULE): State.BUBBLE,
    (State.DEFAULT, TokenType.KW_SYNTAX): State.SYNTAX,
    (State.DEFAULT, TokenType.LBRACK): State.ATTR,
    (State.KLABEL, TokenType.KW_CLAIM): State.BUBBLE,
    (State.KLABEL, TokenType.KW_CONFIG): State.BUBBLE,
    (State.KLABEL, TokenType.KW_CONTEXT): State.CONTEXT,
    (State.KLABEL, TokenType.KW_ENDMODULE): State.DEFAULT,
    (State.KLABEL, TokenType.KW_RULE): State.BUBBLE,
    (State.KLABEL, TokenType.KW_SYNTAX): State.SYNTAX,
    (State.MODNAME, TokenType.MODNAME): State.DEFAULT,
    (State.SYNTAX, TokenType.ID_UPPER): State.DEFAULT,
    (State.SYNTAX, TokenType.KW_LEFT): State.KLABEL,
    (State.SYNTAX, TokenType.KW_LEXICAL): State.DEFAULT,
    (State.SYNTAX, TokenType.KW_NONASSOC): State.KLABEL,
    (State.SYNTAX, TokenType.KW_PRIORITY): State.KLABEL,
    (State.SYNTAX, TokenType.KW_RIGHT): State.KLABEL,
    (State.SYNTAX, TokenType.LBRACE): State.DEFAULT,
}

_BUBBLY_STATES: Final = {State.BUBBLE, State.CONTEXT}


class LocationIterator(Iterator[str]):
    """A string iterator which tracks the line and column information of the characters in the string."""

    _line: int
    _col: int
    _iter: Iterator[str]
    _nextline: bool

    def __init__(self, text: Iterable[str], line: int = 1, col: int = 0) -> None:
        self._iter = iter(text)
        self._line = line
        self._col = col
        self._nextline = False

    def __next__(self) -> str:
        la = next(self._iter)
        self._col += 1
        if self._nextline:
            self._line += 1
            self._col = 1
        self._nextline = la == '\n'
        return la

    @property
    def loc(self) -> Loc:
        """Return the ``(line, column)`` of the last character returned by the iterator.

        If no character has been returned yet, it will be the location that this
        iterator was initialized with. The default is (1,0), which is the only
        time the column will be 0.
        """
        return Loc(self._line, self._col)


def outer_lexer(it: Iterable[str]) -> Iterator[Token]:
    it = LocationIterator(it)
    la = next(it, '')
    state = State.DEFAULT

    while True:
        if state in _SIMPLE_STATES:
            token, la = _SIMPLE_STATES[state](la, it)
            yield token
            last_token = token

        elif state in _BUBBLY_STATES:
            tokens, la = _bubble_or_context(la, it, context=state is State.CONTEXT)
            yield from tokens
            last_token = tokens[-1]

        elif state is State.ATTR:
            la = yield from _attr(la, it)
            state = State.DEFAULT
            continue

        else:
            raise AssertionError()

        if last_token.type is TokenType.EOF:
            return
        state = _NEXT_STATE.get((state, last_token.type), state)


_DEFAULT_KEYWORDS: Final = {
    'claim',
    'configuration',
    'context',
    'endmodule',
    'import',
    'imports',
    'left',
    'module',
    'non-assoc',
    'require',
    'requires',
    'right',
    'rule',
    'syntax',
}


def _default(la: str, it: LocationIterator) -> tuple[Token, str]:
    la = _skip_ws_and_comments(la, it)

    if not la:
        return Token('', TokenType.EOF, it.loc), la

    elif la in _SIMPLE_CHARS:
        token_func = _simple_char

    elif la == '"':
        token_func = _string

    elif la == 'r':
        token_func = _regex_or_lower_id_or_keyword

    elif la in _DIGIT:
        token_func = _nat

    elif la in _ALNUM:
        token_func = _id_or_keyword

    elif la == '#':
        token_func = _hash_id

    elif la == ':':
        token_func = _colon_or_dcoloneq

    else:
        raise _unexpected_character(la)

    loc = it.loc
    text, token_type, la = token_func(la, it)
    return Token(text, token_type, loc), la


def _skip_ws_and_comments(la: str, it: Iterator[str]) -> str:
    # Only use in states where "/" can only be lexed as comment
    while True:
        if la in _WHITESPACE:
            la = next(it, '')
        elif la == '/':
            is_comment, consumed, la = _maybe_comment(la, it)
            if not is_comment:
                raise _unexpected_character(la)
            la = next(it, '')
        else:
            break
    return la


def _simple_char(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la in _SIMPLE_CHARS

    text = la
    token_type = _SIMPLE_CHARS[la]
    la = next(it, '')
    return text, token_type, la


def _nat(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la in _DIGIT

    consumed = []
    while la in _DIGIT:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return text, TokenType.NAT, la


def _id_or_keyword(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la in _ALPHA

    if la in _LOWER:
        token_type = TokenType.ID_LOWER
    else:
        token_type = TokenType.ID_UPPER

    consumed = []
    while la in _ALNUM or la == '-':
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    if text in _DEFAULT_KEYWORDS:
        return text, _KEYWORDS[text], la
    return text, token_type, la


def _hash_id(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la == '#'

    consumed = [la]
    la = next(it, '')

    if la in _LOWER:
        token_type = TokenType.ID_LOWER
    elif la in _UPPER:
        token_type = TokenType.ID_UPPER
    else:
        raise _unexpected_character(la)

    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return text, token_type, la


def _colon_or_dcoloneq(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la == ':'

    la = next(it, '')
    if la != ':':
        return ':', TokenType.COLON, la
    la = next(it, '')
    if la != '=':
        raise _unexpected_character(la)  # Could return [":", ":"], but that never parses
    la = next(it, '')
    return '::=', TokenType.DCOLONEQ, la


def _string(la: str, it: Iterator) -> tuple[str, TokenType, str]:
    # assert la == '"'
    consumed: list[str] = []
    la = _consume_string(consumed, la, it)
    return ''.join(consumed), TokenType.STRING, la


def _regex_or_lower_id_or_keyword(la: str, it: Iterator) -> tuple[str, TokenType, str]:
    # assert la == 'r'
    consumed = [la]
    la = next(it, '')

    if la == '"':
        la = _consume_string(consumed, la, it)
        return ''.join(consumed), TokenType.REGEX, la

    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    if text in _DEFAULT_KEYWORDS:
        return text, _KEYWORDS[text], la
    return text, TokenType.ID_LOWER, la


def _consume_string(consumed: list[str], la: str, it: Iterator[str]) -> str:
    # assert la == '"'
    consumed.append(la)  # ['"']

    la = next(it, '')
    while la not in {'"', '\n', ''}:
        consumed.append(la)  # ['"', ..., X]
        if la == '\\':
            la = next(it, '')
            if not la or la not in {'\\', '"', 'n', 'r', 't'}:
                raise _unexpected_character(la)
            consumed.append(la)  # ['"', ..., '//', X]
        la = next(it, '')

    if not la or la == '\n':
        raise _unexpected_character(la)

    consumed.append(la)  # ['"', ..., '"']
    la = next(it, '')
    return la


_SYNTAX_KEYWORDS: Final = {
    'left',
    'lexical',
    'non-assoc',
    'priorities',
    'priority',
    'right',
}


def _syntax(la: str, it: LocationIterator) -> tuple[Token, str]:
    la = _skip_ws_and_comments(la, it)

    if not la:
        return Token('', TokenType.EOF, it.loc), la

    elif la == '{':
        token_func = _simple_char

    elif la in _LOWER:
        token_func = _syntax_keyword

    elif la in _UPPER:
        token_func = _upper_id

    elif la == '#':
        token_func = _hash_upper_id

    else:
        raise _unexpected_character(la)

    loc = it.loc
    text, token_type, la = token_func(la, it)
    return Token(text, token_type, loc), la


def _syntax_keyword(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    if la not in _LOWER:
        raise _unexpected_character(la)

    consumed = []
    while la in _ALNUM or la == '-':
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)

    if text not in _SYNTAX_KEYWORDS:
        raise ValueError(f'Unexpected token: {text}')

    return text, _KEYWORDS[text], la


def _upper_id(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    if la not in _UPPER:
        raise _unexpected_character(la)

    consumed = []
    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return text, TokenType.ID_UPPER, la


def _hash_upper_id(la: str, it: Iterator[str]) -> tuple[str, TokenType, str]:
    # assert la == '#'

    consumed = [la]
    la = next(it, '')

    if la not in _UPPER:
        raise _unexpected_character(la)

    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return text, TokenType.ID_UPPER, la


_MODNAME_KEYWORDS: Final = {'private', 'public'}


def _modname(la: str, it: LocationIterator) -> tuple[Token, str]:
    r"""Match a module name.

    Corresponds to regex: [a-zA-Z]\w*(-\w+)*
    """
    la = _skip_ws_and_comments(la, it)

    consumed = []
    loc = it.loc

    if la not in _ALPHA:
        raise _unexpected_character(la)

    consumed.append(la)
    la = next(it, '')

    while la in _WORD:
        consumed.append(la)
        la = next(it, '')

    while True:
        if la != '-':
            break

        consumed.append(la)
        la = next(it, '')

        if la not in _WORD:
            raise _unexpected_character(la)

        consumed.append(la)
        la = next(it, '')

        while la in _WORD:
            consumed.append(la)
            la = next(it, '')

    text = ''.join(consumed)
    if text in _MODNAME_KEYWORDS:
        return Token(text, _KEYWORDS[text], loc), la
    return Token(text, TokenType.MODNAME, loc), la


_KLABEL_KEYWORDS: Final = {'syntax', 'endmodule', 'rule', 'claim', 'configuration', 'context'}


def _klabel(la: str, it: LocationIterator) -> tuple[Token, str]:
    loc: Loc
    consumed: list[str]
    while True:
        while la in _WHITESPACE:
            la = next(it, '')

        if not la:
            return Token('', TokenType.EOF, it.loc), la

        if la == '/':
            loc = it.loc
            is_comment, consumed, la = _maybe_comment(la, it)

            if not is_comment and len(consumed) > 1:
                # Differs from K Frontend
                raise ValueError('Unterminated block comment')

            if is_comment and (not la or la in _WHITESPACE):
                continue

            break

        loc = it.loc
        consumed = []
        break

    if la == '>' and not consumed:
        consumed.append(la)
        la = next(it, '')
        if not la or la in _WHITESPACE:
            return Token('>', TokenType.GT, loc), la

    while la and la not in _WHITESPACE:
        consumed.append(la)
        la = next(it, '')

    text = ''.join(consumed)
    if text in _KLABEL_KEYWORDS:
        token_type = _KEYWORDS[text]
    else:
        token_type = TokenType.KLABEL
    return Token(text, token_type, loc), la


_SIMPLE_STATES: Final = {
    State.DEFAULT: _default,
    State.SYNTAX: _syntax,
    State.MODNAME: _modname,
    State.KLABEL: _klabel,
}


_BUBBLE_KEYWORDS: Final = {'syntax', 'endmodule', 'rule', 'claim', 'configuration', 'context'}
_CONTEXT_KEYWORDS: Final = {'alias'}.union(_BUBBLE_KEYWORDS)


def _bubble_or_context(la: str, it: LocationIterator, *, context: bool = False) -> tuple[list[Token], str]:
    keywords = _CONTEXT_KEYWORDS if context else _BUBBLE_KEYWORDS

    tokens: list[Token] = []

    bubble, final_token, la, bubble_loc = _raw_bubble(la, it, keywords)
    if bubble is not None:
        label_tokens, bubble, bubble_loc = _strip_bubble_label(bubble, bubble_loc)
        bubble, attr_tokens = _strip_bubble_attr(bubble, bubble_loc)

        tokens = label_tokens
        if bubble:
            bubble_token = Token(bubble, TokenType.BUBBLE, bubble_loc)
            tokens += [bubble_token]
        tokens += attr_tokens

    tokens += [final_token]
    return tokens, la


def _raw_bubble(la: str, it: LocationIterator, keywords: Collection[str]) -> tuple[str | None, Token, str, Loc]:
    bubble: list[str] = []  # text that belongs to the bubble
    special: list[str] = []  # text that belongs to the bubble iff preceded and followed by bubble text
    current: list[str] = []  # text that might belong to the bubble or terminate the bubble if keyword
    bubble_loc: Loc = it.loc
    current_loc: Loc = it.loc
    while True:
        if not la or la in _WHITESPACE:
            if current:
                current_str = ''.join(current)
                if current_str in keywords:  # <special><keyword><ws>
                    return (
                        ''.join(bubble) if bubble else None,
                        Token(current_str, _KEYWORDS[current_str], current_loc),
                        la,
                        bubble_loc,
                    )
                else:  # <special><current><ws>
                    bubble_loc += '' if bubble else ''.join(special)
                    bubble += special if bubble else []
                    bubble += current
                    special = []
                    current = []
                    current_loc = it.loc

            else:  # <special><ws>
                pass

            while la in _WHITESPACE:
                special.append(la)
                la = next(it, '')
                current_loc = it.loc

            if not la:
                return ''.join(bubble) if bubble else None, Token('', TokenType.EOF, it.loc), la, bubble_loc

        elif la == '/':
            is_comment, consumed, la = _maybe_comment(la, it)
            if is_comment:
                if current:
                    current_str = ''.join(current)
                    if current_str in keywords:  # <special><keyword><comment>
                        # Differs from K Frontend behavior, see: https://github.com/runtimeverification/k/issues/3501
                        return (
                            ''.join(bubble) if bubble else None,
                            Token(current_str, _KEYWORDS[current_str], current_loc),
                            la,
                            bubble_loc,
                        )
                    else:  # <special><current><comment>
                        bubble_loc += '' if bubble else ''.join(special)
                        bubble += special if bubble else []
                        bubble += current
                        special = consumed
                        current = []
                        current_loc = it.loc

                else:  # <special><comment>
                    special += consumed

            else:
                if len(consumed) > 1:  # Unterminated block comment
                    # Differs from K Frontend behavior
                    raise ValueError('Unterminated block comment')
                current += consumed

        else:  # <special><current>
            while la and la not in _WHITESPACE and la != '/':
                current.append(la)
                la = next(it, '')


RULE_LABEL_PATTERN: Final = re.compile(
    r'(?s)\s*(?P<lbrack>\[)\s*(?P<label>[^\[\]\_\n\r\t ]+)\s*(?P<rbrack>\])\s*(?P<colon>:)\s*(?P<rest>.*)'
)


def _strip_bubble_label(bubble: str, loc: Loc) -> tuple[list[Token], str, Loc]:
    match = RULE_LABEL_PATTERN.fullmatch(bubble)
    if not match:
        return [], bubble, loc

    lbrack_loc = loc + bubble[: match.start('lbrack')]
    label_loc = lbrack_loc + bubble[match.start('lbrack') : match.start('label')]
    rbrack_loc = label_loc + bubble[match.start('label') : match.start('rbrack')]
    colon_loc = rbrack_loc + bubble[match.start('rbrack') : match.start('colon')]
    return (
        [
            Token('[', TokenType.LBRACK, lbrack_loc),
            Token(match['label'], TokenType.RULE_LABEL, label_loc),
            Token(']', TokenType.RBRACK, rbrack_loc),
            Token(':', TokenType.COLON, colon_loc),
        ],
        match['rest'],
        colon_loc + bubble[match.start('colon') : match.start('rest')],
    )


def _strip_bubble_attr(bubble: str, loc: Loc) -> tuple[str, list[Token]]:
    for i in range(len(bubble) - 1, -1, -1):
        if bubble[i] != '[':
            continue

        prefix = bubble[:i]
        suffix = bubble[i + 1 :]
        start_loc = loc + prefix

        it = LocationIterator(suffix, *start_loc)
        la = next(it, '')

        tokens = [Token('[', TokenType.LBRACK, start_loc)]
        attr_tokens = _attr(la, it)
        try:
            while True:
                tokens.append(next(attr_tokens))
        except ValueError:
            continue
        except StopIteration as err:
            la = err.value

        if la:
            continue

        return prefix.rstrip(' \t\n\r'), tokens

    return bubble, []


def _attr(la: str, it: LocationIterator) -> Generator[Token, None, str]:
    la = _skip_ws_and_comments(la, it)
    if not la:
        raise _unexpected_character(la)

    while True:
        key, la = _attr_key(la, it)
        yield key

        la = _skip_ws_and_comments(la, it)

        if la == '(':  # TAG_STATE
            yield Token('(', TokenType.LPAREN, it.loc)
            la = next(it, '')
            loc = it.loc

            if la == '"':
                text, token_type, la = _string(la, it)
                yield Token(text, token_type, loc)
            else:
                content, la = _attr_content(la, it)
                if content:
                    # allows 'key()'
                    yield Token(content, TokenType.ATTR_CONTENT, loc)

            if la != ')':
                raise _unexpected_character(la)

            yield Token(')', TokenType.RPAREN, it.loc)

            la = next(it, '')
            la = _skip_ws_and_comments(la, it)

        if la != ',':
            break

        yield Token(',', TokenType.COMMA, it.loc)
        la = next(it, '')
        la = _skip_ws_and_comments(la, it)

    if la != ']':
        raise _unexpected_character(la)

    yield Token(']', TokenType.RBRACK, it.loc)
    la = next(it, '')

    return la  # noqa: B901


def _attr_key(la: str, it: LocationIterator) -> tuple[Token, str]:
    # ["a"-"z","1"-"9"](["A"-"Z", "a"-"z", "-", "0"-"9", "."])*("<" (["A"-"Z", "a"-"z", "-", "0"-"9"])+ ">")?

    consumed: list[str] = []
    loc = it.loc
    if la not in _LOWER and la not in _DIGIT:
        raise _unexpected_character(la)

    consumed.append(la)
    la = next(it, '')

    while la in _ALNUM or la == '-' or la == '.':
        consumed.append(la)
        la = next(it, '')

    if la == '<':
        consumed.append(la)
        la = next(it, '')

        if not la in _ALNUM and la != '-' and la != '.':
            raise _unexpected_character(la)

        consumed.append(la)
        la = next(it, '')

        while la in _ALNUM or la == '-' or la == '.':
            consumed.append(la)
            la = next(it, '')

        if la != '>':
            raise _unexpected_character(la)

        consumed.append(la)
        la = next(it, '')

    attr_key = ''.join(consumed)
    return Token(attr_key, TokenType.ATTR_KEY, loc), la


_ATTR_CONTENT_FORBIDDEN: Final = {'', '\n', '\r', '"'}


def _attr_content(la: str, it: Iterator[str]) -> tuple[str, str]:
    consumed: list[str] = []
    open_parens = 0

    while la not in _ATTR_CONTENT_FORBIDDEN:
        if la == ')':
            if not open_parens:
                break
            open_parens -= 1

        elif la == '(':
            open_parens += 1

        consumed.append(la)
        la = next(it, '')

    if la in _ATTR_CONTENT_FORBIDDEN:
        raise _unexpected_character(la)

    # assert la == ')'

    attr_content = ''.join(consumed)
    return attr_content, la


def _maybe_comment(la: str, it: Iterator[str]) -> tuple[bool, list[str], str]:
    """Attempt to consume a line or block comment from the iterator.

    Expects la to be ``'/'``.

    Args:
        la: The current lookahead.
        it: The iterator.

    Returns:
        A tuple ``(success, consumed, la)`` where

        - ``success``: Indicates whether `consumed` is a comment.
        - ``consumed``: The list of consumed characters.
        - ``la``: The current lookahead.
    """
    assert la == '/'
    consumed = [la]  # ['/']

    la = next(it, '')
    if la == '':
        return False, consumed, la

    elif la == '/':
        consumed.append(la)  # ['/', '/']
        la = next(it, '')
        while la and la != '\n':
            consumed.append(la)  # ['/', '/', ..., X]
            la = next(it, '')
        return True, consumed, la

    elif la == '*':
        consumed.append(la)  # ['/', '*']

        la = next(it, '')
        while True:
            if la == '':
                return False, consumed, la

            elif la == '*':
                consumed.append(la)  # ['/', '*', ..., '*']

                la = next(it, '')
                if la == '':
                    return False, consumed, la
                elif la == '/':
                    consumed.append(la)  # ['/', '*', ..., '*', '/']
                    la = next(it, '')
                    return True, consumed, la
                else:
                    consumed.append(la)  # ['/', '*', ..., '*', X]
                    la = next(it, '')
                    continue

            else:
                consumed.append(la)  # ['/', '*', ..., X]
                la = next(it, '')
                continue

    else:
        return False, consumed, la


def _unexpected_character(la: str) -> ValueError:
    if la:
        return ValueError(f'Unexpected character: {la!r}')

    return ValueError('Unexpected end of file')
