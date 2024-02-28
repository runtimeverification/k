from __future__ import annotations

import re
from enum import Enum, auto
from typing import TYPE_CHECKING, NamedTuple

if TYPE_CHECKING:
    from collections.abc import Collection, Generator, Iterable, Iterator
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


class Token(NamedTuple):
    text: str
    type: TokenType


_EOF_TOKEN: Final = Token('', TokenType.EOF)
_COLON_TOKEN: Final = Token(':', TokenType.COLON)
_DCOLONEQ_TOKEN: Final = Token('::=', TokenType.DCOLONEQ)
_COMMA_TOKEN: Final = Token(',', TokenType.COMMA)
_LPAREN_TOKEN: Final = Token('(', TokenType.LPAREN)
_RPAREN_TOKEN: Final = Token(')', TokenType.RPAREN)
_LBRACK_TOKEN: Final = Token('[', TokenType.LBRACK)
_RBRACK_TOKEN: Final = Token(']', TokenType.RBRACK)
_GT_TOKEN: Final = Token('>', TokenType.GT)

_SIMPLE_CHARS: Final = {
    ',': _COMMA_TOKEN,
    '(': _LPAREN_TOKEN,
    ')': _RPAREN_TOKEN,
    '[': _LBRACK_TOKEN,
    ']': _RBRACK_TOKEN,
    '>': _GT_TOKEN,
    '{': Token('{', TokenType.LBRACE),
    '}': Token('}', TokenType.RBRACE),
    '|': Token('|', TokenType.VBAR),
    '=': Token('=', TokenType.EQ),
    '+': Token('+', TokenType.PLUS),
    '*': Token('*', TokenType.TIMES),
    '?': Token('?', TokenType.QUESTION),
    '~': Token('~', TokenType.TILDE),
}

_KEYWORDS: Final = {
    'alias': Token('alias', TokenType.KW_ALIAS),
    'claim': Token('claim', TokenType.KW_CLAIM),
    'configuration': Token('configuration', TokenType.KW_CONFIG),
    'context': Token('context', TokenType.KW_CONTEXT),
    'endmodule': Token('endmodule', TokenType.KW_ENDMODULE),
    'imports': Token('imports', TokenType.KW_IMPORTS),
    'left': Token('left', TokenType.KW_LEFT),
    'lexical': Token('lexical', TokenType.KW_LEXICAL),
    'module': Token('module', TokenType.KW_MODULE),
    'non-assoc': Token('non-assoc', TokenType.KW_NONASSOC),
    'priority': Token('priority', TokenType.KW_PRIORITY),
    'private': Token('private', TokenType.KW_PRIVATE),
    'public': Token('public', TokenType.KW_PUBLIC),
    'requires': Token('requires', TokenType.KW_REQUIRES),
    'right': Token('right', TokenType.KW_RIGHT),
    'rule': Token('rule', TokenType.KW_RULE),
    'syntax': Token('syntax', TokenType.KW_SYNTAX),
}

_WHITESPACE: Final = {' ', '\t', '\n', '\r'}
_DIGIT: Final = set('0123456789')
_LOWER: Final = set('abcdefghijklmnopqrstuvwxyz')
_UPPER: Final = set('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
_ALPHA: Final = set().union(_LOWER).union(_UPPER)
_ALNUM: Final = set(_ALPHA).union(_DIGIT)


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


def outer_lexer(it: Iterable[str]) -> Iterator[Token]:
    it = iter(it)
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


def _default(la: str, it: Iterator[str]) -> tuple[Token, str]:
    la = _skip_ws_and_comments(la, it)

    if not la:
        return _EOF_TOKEN, la

    elif la in _SIMPLE_CHARS:
        return _simple_char(la, it)

    elif la == '"':
        return _string(la, it)

    elif la == 'r':
        return _regex_or_lower_id_or_keyword(la, it)

    elif la in _DIGIT:
        return _nat(la, it)

    elif la in _ALNUM:
        return _id_or_keyword(la, it)

    elif la == '#':
        return _hash_id(la, it)

    elif la == ':':
        return _colon_or_dcoloneq(la, it)

    else:
        raise _unexpected_character(la)


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


def _simple_char(la: str, it: Iterator[str]) -> tuple[Token, str]:
    # assert la in _SIMPLE_CHARS

    token = _SIMPLE_CHARS[la]
    la = next(it, '')
    return token, la


def _nat(la: str, it: Iterator[str]) -> tuple[Token, str]:
    # assert la in _DIGIT

    consumed = []
    while la in _DIGIT:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return Token(text, TokenType.NAT), la


def _id_or_keyword(la: str, it: Iterator[str]) -> tuple[Token, str]:
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
        return _KEYWORDS[text], la
    return Token(text, token_type), la


def _hash_id(la: str, it: Iterator[str]) -> tuple[Token, str]:
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
    return Token(text, token_type), la


def _colon_or_dcoloneq(la: str, it: Iterator[str]) -> tuple[Token, str]:
    # assert la == ':'

    la = next(it, '')
    if la != ':':
        return _COLON_TOKEN, la
    la = next(it, '')
    if la != '=':
        raise _unexpected_character(la)  # Could return [":", ":"], but that never parses
    la = next(it, '')
    return _DCOLONEQ_TOKEN, la


def _string(la: str, it: Iterator) -> tuple[Token, str]:
    # assert la == '"'
    consumed: list[str] = []
    la = _consume_string(consumed, la, it)
    return Token(''.join(consumed), TokenType.STRING), la


def _regex_or_lower_id_or_keyword(la: str, it: Iterator) -> tuple[Token, str]:
    # assert la == 'r'
    consumed = [la]
    la = next(it, '')

    if la == '"':
        la = _consume_string(consumed, la, it)
        return Token(''.join(consumed), TokenType.REGEX), la

    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    if text in _DEFAULT_KEYWORDS:
        return _KEYWORDS[text], la
    return Token(text, TokenType.ID_LOWER), la


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


def _syntax(la: str, it: Iterator[str]) -> tuple[Token, str]:
    la = _skip_ws_and_comments(la, it)

    if not la:
        return _EOF_TOKEN, la

    elif la == '{':
        return _simple_char(la, it)

    elif la in _LOWER:
        return _syntax_keyword(la, it)

    elif la in _UPPER:
        return _upper_id(la, it)

    elif la == '#':
        return _hash_upper_id(la, it)

    else:
        raise _unexpected_character(la)


def _syntax_keyword(la: str, it: Iterator[str]) -> tuple[Token, str]:
    if la not in _LOWER:
        raise _unexpected_character(la)

    consumed = []
    while la in _ALNUM or la == '-':
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)

    if text not in _SYNTAX_KEYWORDS:
        raise ValueError(f'Unexpected token: {text}')

    return _KEYWORDS[text], la


def _upper_id(la: str, it: Iterator[str]) -> tuple[Token, str]:
    if la not in _UPPER:
        raise _unexpected_character(la)

    consumed = []
    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return Token(text, TokenType.ID_UPPER), la


def _hash_upper_id(la: str, it: Iterator[str]) -> tuple[Token, str]:
    # assert la == '#'

    consumed = [la]
    la = next(it, '')

    if la not in _UPPER:
        raise _unexpected_character(la)

    while la in _ALNUM:
        consumed.append(la)
        la = next(it, '')
    text = ''.join(consumed)
    return Token(text, TokenType.ID_UPPER), la


_MODNAME_KEYWORDS: Final = {'private', 'public'}
_MODNAME_CHARS: Final = {'-', '_'}.union(_ALNUM)


def _modname(la: str, it: Iterator) -> tuple[Token, str]:
    la = _skip_ws_and_comments(la, it)

    consumed = []

    if la == '#':
        consumed.append(la)
        la = next(it, '')

    if not la:
        raise _unexpected_character(la)

    allow_dash = False
    while la in _MODNAME_CHARS:
        if la == '-' and not allow_dash:
            raise _unexpected_character(la)
        allow_dash = la != '-'
        consumed.append(la)
        la = next(it, '')

    text = ''.join(consumed)
    if text in _MODNAME_KEYWORDS:
        return _KEYWORDS[text], la
    return Token(text, TokenType.MODNAME), la


_KLABEL_KEYWORDS: Final = {'syntax', 'endmodule', 'rule', 'claim', 'configuration', 'context'}


def _klabel(la: str, it: Iterator[str]) -> tuple[Token, str]:
    consumed: list[str]
    while True:
        while la in _WHITESPACE:
            la = next(it, '')

        if not la:
            return _EOF_TOKEN, la

        if la == '/':
            is_comment, consumed, la = _maybe_comment(la, it)

            if not is_comment and len(consumed) > 1:
                # Differs from K Frontend
                raise ValueError('Unterminated block comment')

            if is_comment and (not la or la in _WHITESPACE):
                continue

            break

        consumed = []
        break

    if la == '>' and not consumed:
        consumed.append(la)
        la = next(it, '')
        if not la or la in _WHITESPACE:
            return _GT_TOKEN, la

    while la and la not in _WHITESPACE:
        consumed.append(la)
        la = next(it, '')

    text = ''.join(consumed)
    if text in _KLABEL_KEYWORDS:
        token = _KEYWORDS[text]
    else:
        token = Token(text, TokenType.KLABEL)
    return token, la


_SIMPLE_STATES: Final = {
    State.DEFAULT: _default,
    State.SYNTAX: _syntax,
    State.MODNAME: _modname,
    State.KLABEL: _klabel,
}


_BUBBLE_KEYWORDS: Final = {'syntax', 'endmodule', 'rule', 'claim', 'configuration', 'context'}
_CONTEXT_KEYWORDS: Final = {'alias'}.union(_BUBBLE_KEYWORDS)


def _bubble_or_context(la: str, it: Iterator, *, context: bool = False) -> tuple[list[Token], str]:
    keywords = _CONTEXT_KEYWORDS if context else _BUBBLE_KEYWORDS

    tokens: list[Token] = []

    bubble, final_token, la = _raw_bubble(la, it, keywords)
    if bubble is not None:
        label_tokens, bubble = _strip_bubble_label(bubble)
        bubble, attr_tokens = _strip_bubble_attr(bubble)

        tokens = label_tokens
        if bubble:
            bubble_token = Token(bubble, TokenType.BUBBLE)
            tokens += [bubble_token]
        tokens += attr_tokens

    tokens += [final_token]
    return tokens, la


def _raw_bubble(la: str, it: Iterator[str], keywords: Collection[str]) -> tuple[str | None, Token, str]:
    bubble: list[str] = []  # text that belongs to the bubble
    special: list[str] = []  # text that belongs to the bubble iff preceded and followed by bubble text
    current: list[str] = []  # text that might belong to the bubble or terminate the bubble if keyword
    while True:
        if not la or la in _WHITESPACE:
            if current:
                current_str = ''.join(current)
                if current_str in keywords:  # <special><keyword><ws>
                    return ''.join(bubble) if bubble else None, _KEYWORDS[current_str], la
                else:  # <special><current><ws>
                    bubble += special if bubble else []
                    bubble += current
                    special = []
                    current = []

            else:  # <special><ws>
                pass

            while la in _WHITESPACE:
                special.append(la)
                la = next(it, '')

            if not la:
                return ''.join(bubble) if bubble else None, _EOF_TOKEN, la

        elif la == '/':
            is_comment, consumed, la = _maybe_comment(la, it)
            if is_comment:
                if current:
                    current_str = ''.join(current)
                    if current_str in keywords:  # <special><keyword><comment>
                        # Differs from K Frontend behavior, see: https://github.com/runtimeverification/k/issues/3501
                        return ''.join(bubble) if bubble else None, _KEYWORDS[current_str], la
                    else:  # <special><current><comment>
                        bubble += special if bubble else []
                        bubble += current
                        special = consumed
                        current = []

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


RULE_LABEL_PATTERN: Final = re.compile(r'(?s)\s*\[\s*(?P<label>[^\[\]\_\n\r\t ]+)\s*\]\s*:\s*(?P<rest>.*)')


def _strip_bubble_label(bubble: str) -> tuple[list[Token], str]:
    match = RULE_LABEL_PATTERN.fullmatch(bubble)
    if not match:
        return [], bubble

    return (
        [
            _LBRACK_TOKEN,
            Token(match['label'], TokenType.RULE_LABEL),
            _RBRACK_TOKEN,
            _COLON_TOKEN,
        ],
        match['rest'],
    )


def _strip_bubble_attr(bubble: str) -> tuple[str, list[Token]]:
    for i in range(len(bubble) - 1, -1, -1):
        if bubble[i] != '[':
            continue

        prefix = bubble[:i]
        suffix = bubble[i:]

        it = iter(suffix)
        next(it)  # skip "["
        la = next(it, '')

        tokens = [_LBRACK_TOKEN]
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


def _attr(la: str, it: Iterator[str]) -> Generator[Token, None, str]:
    la = _skip_ws_and_comments(la, it)
    if not la:
        raise _unexpected_character(la)

    while True:
        key, la = _attr_key(la, it)
        yield key

        la = _skip_ws_and_comments(la, it)

        if la == '(':  # TAG_STATE
            yield _LPAREN_TOKEN
            la = next(it, '')

            if la == '"':
                token, la = _string(la, it)
                yield token
            else:
                content, la = _attr_content(la, it)
                if content:
                    # allows 'key()'
                    yield Token(content, TokenType.ATTR_CONTENT)

            if la != ')':
                raise _unexpected_character(la)

            yield _RPAREN_TOKEN

            la = next(it, '')
            la = _skip_ws_and_comments(la, it)

        if la != ',':
            break

        yield _COMMA_TOKEN
        la = next(it, '')
        la = _skip_ws_and_comments(la, it)

    if la != ']':
        raise _unexpected_character(la)

    yield _RBRACK_TOKEN
    la = next(it, '')

    return la  # noqa: B901


def _attr_key(la: str, it: Iterator[str]) -> tuple[Token, str]:
    # ["a"-"z","1"-"9"](["A"-"Z", "a"-"z", "-", "0"-"9", "."])*("<" (["A"-"Z", "a"-"z", "-", "0"-"9"])+ ">")?

    consumed: list[str] = []
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
    return Token(attr_key, TokenType.ATTR_KEY), la


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
    """
    Attempt to consume a line or block comment from the iterator.
    Expects la to be '/'.

    :param la: The current lookahead.
    :param it: The iterator.
    :return: A tuple `(success, consumed, la)` where
      * `success` indicates whether `consumed` is a comment
      * `consumed` is the list of consumed characters
      * `la` is the current lookahead
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
