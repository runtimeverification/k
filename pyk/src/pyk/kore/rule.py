from __future__ import annotations

import logging
from abc import ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, TypeVar, final

from .prelude import inj
from .syntax import (
    DV,
    And,
    App,
    Axiom,
    Ceil,
    Equals,
    EVar,
    Implies,
    In,
    Not,
    Pattern,
    Rewrites,
    SortApp,
    SortVar,
    String,
    Top,
)

if TYPE_CHECKING:
    from typing import Final

    from .syntax import Definition

    Attrs = dict[str, tuple[Pattern, ...]]


P = TypeVar('P', bound=Pattern)


_LOGGER: Final = logging.getLogger(__name__)


# There's a simplification rule with irregular form in the prelude module INJ.
# This rule is skipped in Rule.extract_all.
_S1, _S2, _S3, _R = (SortVar(name) for name in ['S1', 'S2', 'S3', 'R'])
_T: Final = EVar('T', _S1)
# axiom {S1, S2, S3, R} \equals{S3, R}(inj{S2, S3}(inj{S1, S2}(T:S1)), inj{S1, S3}(T:S1)) [simplification{}()]
_INJ_AXIOM: Final = Axiom(
    vars=(_S1, _S2, _S3, _R),
    pattern=Equals(_S3, _R, inj(_S2, _S3, inj(_S1, _S2, _T)), inj(_S1, _S3, _T)),
    attrs=(App('simplification'),),
)

# The following attributes mark axioms that are not rule axioms.
# Such axioms are skipped in Rule.extract_all.
_SKIPPED_ATTRS: Final = (
    'assoc',
    'constructor',
    'functional',
    'idem',
    'symbol-overload',
    'subsort',
    'unit',
)


class Rule(ABC):
    lhs: Pattern
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> Rule:
        if isinstance(axiom.pattern, Rewrites):
            return RewriteRule.from_axiom(axiom)

        if 'simplification' not in axiom.attrs_by_key:
            return FunctionRule.from_axiom(axiom)

        match axiom.pattern:
            case Implies(right=Equals(left=App())):
                return AppRule.from_axiom(axiom)
            case Implies(right=Equals(left=Ceil())):
                return CeilRule.from_axiom(axiom)
            case Implies(right=Equals(left=Equals())):
                return EqualsRule.from_axiom(axiom)
            case _:
                raise ValueError(f'Cannot parse simplification rule: {axiom.text}')

    @staticmethod
    def extract_all(defn: Definition) -> list[Rule]:
        def is_rule(axiom: Axiom) -> bool:
            if axiom == _INJ_AXIOM:
                return False

            if any(attr in axiom.attrs_by_key for attr in _SKIPPED_ATTRS):
                return False

            return True

        return [Rule.from_axiom(axiom) for axiom in defn.axioms if is_rule(axiom)]


@final
@dataclass(frozen=True)
class RewriteRule(Rule):
    lhs: App
    rhs: App
    req: Pattern | None
    ens: Pattern | None
    ctx: EVar | None
    priority: int
    uid: str
    label: str | None

    @staticmethod
    def from_axiom(axiom: Axiom) -> RewriteRule:
        lhs, rhs, req, ens, ctx = RewriteRule._extract(axiom)
        priority = _extract_priority(axiom)
        uid = _extract_uid(axiom)
        label = _extract_label(axiom)
        return RewriteRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            ctx=ctx,
            priority=priority,
            uid=uid,
            label=label,
        )

    @staticmethod
    def _extract(axiom: Axiom) -> tuple[App, App, Pattern | None, Pattern | None, EVar | None]:
        match axiom.pattern:
            case Rewrites(left=And(ops=(_lhs, _req)), right=_rhs):
                pass
            case _:
                raise ValueError(f'Cannot extract rewrite rule from axiom: {axiom.text}')

        ctx: EVar | None = None
        match _lhs:
            case App("Lbl'-LT-'generatedTop'-GT-'") as lhs:
                pass
            case And(_, (App("Lbl'-LT-'generatedTop'-GT-'") as lhs, EVar("Var'Hash'Configuration") as ctx)):
                pass
            case _:
                raise ValueError(f'Cannot extract LHS configuration from axiom: {axiom.text}')

        req = _extract_condition(_req)
        rhs, ens = _extract_rhs(_rhs)
        match rhs:
            case App("Lbl'-LT-'generatedTop'-GT-'"):
                pass
            case _:
                raise ValueError(f'Cannot extract RHS configuration from axiom: {axiom.text}')

        return lhs, rhs, req, ens, ctx


@final
@dataclass(frozen=True)
class FunctionRule(Rule):
    lhs: App
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> FunctionRule:
        lhs, rhs, req, ens = FunctionRule._extract(axiom)
        priority = _extract_priority(axiom)
        return FunctionRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )

    @staticmethod
    def _extract(axiom: Axiom) -> tuple[App, Pattern, Pattern | None, Pattern | None]:
        match axiom.pattern:
            case Implies(
                left=And(
                    ops=(Not(), And(ops=(_req, _args))) | (_req, _args),
                ),
                right=Equals(left=App() as app, right=_rhs),
            ):
                args = FunctionRule._extract_args(_args)
                lhs = app.let(args=args)
                req = _extract_condition(_req)
                rhs, ens = _extract_rhs(_rhs)
                return lhs, rhs, req, ens
            case _:
                raise ValueError(f'Cannot extract function rule from axiom: {axiom.text}')

    @staticmethod
    def _extract_args(pattern: Pattern) -> tuple[Pattern, ...]:
        match pattern:
            case Top():
                return ()
            case And(ops=(In(left=EVar(), right=arg), rest)):
                return (arg,) + FunctionRule._extract_args(rest)
            case _:
                raise ValueError(f'Cannot extract argument list from pattern: {pattern.text}')


class SimpliRule(Rule, Generic[P], ABC):
    lhs: P

    @staticmethod
    def _extract(axiom: Axiom, lhs_type: type[P]) -> tuple[P, Pattern, Pattern | None, Pattern | None]:
        match axiom.pattern:
            case Implies(left=_req, right=Equals(left=lhs, right=_rhs)):
                req = _extract_condition(_req)
                rhs, ens = _extract_rhs(_rhs)
                if not isinstance(lhs, lhs_type):
                    raise ValueError(f'Invalid LHS type from simplification axiom: {axiom.text}')
                return lhs, rhs, req, ens
            case _:
                raise ValueError(f'Cannot extract simplification rule from axiom: {axiom.text}')


@final
@dataclass(frozen=True)
class AppRule(SimpliRule[App]):
    lhs: App
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> AppRule:
        lhs, rhs, req, ens = SimpliRule._extract(axiom, App)
        priority = _extract_priority(axiom)
        return AppRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )


@final
@dataclass(frozen=True)
class CeilRule(SimpliRule):
    lhs: Ceil
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> CeilRule:
        lhs, rhs, req, ens = SimpliRule._extract(axiom, Ceil)
        priority = _extract_priority(axiom)
        return CeilRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )


@final
@dataclass(frozen=True)
class EqualsRule(SimpliRule):
    lhs: Equals
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> EqualsRule:
        lhs, rhs, req, ens = SimpliRule._extract(axiom, Equals)
        if not isinstance(lhs, Equals):
            raise ValueError(f'Cannot extract LHS as Equals from axiom: {axiom.text}')
        priority = _extract_priority(axiom)
        return EqualsRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )


def _extract_rhs(pattern: Pattern) -> tuple[Pattern, Pattern | None]:
    match pattern:
        case And(ops=(rhs, _ens)):
            return rhs, _extract_condition(_ens)
        case _:
            raise ValueError(f'Cannot extract RHS from pattern: {pattern.text}')


def _extract_condition(pattern: Pattern) -> Pattern | None:
    match pattern:
        case Top():
            return None
        case Equals(left=cond, right=DV(SortApp('SortBool'), String('true'))):
            return cond
        case _:
            raise ValueError(f'Cannot extract condition from pattern: {pattern.text}')


def _extract_uid(axiom: Axiom) -> str:
    attrs = axiom.attrs_by_key
    match attrs["UNIQUE'Unds'ID"]:
        case App(args=(String(uid),)):
            return uid
        case _:
            raise ValueError(f'Cannot extract uid from axiom: {axiom.text}')


def _extract_label(axiom: Axiom) -> str | None:
    attrs = axiom.attrs_by_key
    match attrs.get('label'):
        case App(args=(String(label),)):
            return label
        case None:
            return None
        case _:
            raise ValueError(f'Cannot extract label from axiom: {axiom.text}')


def _extract_priority(axiom: Axiom) -> int:
    attrs = axiom.attrs_by_key
    match attrs.get('priority'):
        case App(args=(String(p),)):
            assert 'owise' not in attrs
            return int(p)
        case None:
            return 200 if 'owise' in attrs else 50
        case _:
            raise ValueError(f'Cannot extract priority from axiom: {axiom.text}')
