from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import reduce
from typing import TYPE_CHECKING, Generic, TypeVar, cast, final

from .prelude import BOOL, SORT_GENERATED_TOP_CELL, TRUE, inj
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

    from .syntax import Definition, Sort

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
    sort: Sort
    priority: int

    @abstractmethod
    def to_axiom(self) -> Axiom: ...

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
    def is_rule(axiom: Axiom) -> bool:
        if axiom == _INJ_AXIOM:
            return False

        if any(attr in axiom.attrs_by_key for attr in _SKIPPED_ATTRS):
            return False

        return True

    @staticmethod
    def extract_all(defn: Definition) -> list[Rule]:
        return [Rule.from_axiom(axiom) for axiom in defn.axioms if Rule.is_rule(axiom)]


@final
@dataclass(frozen=True)
class RewriteRule(Rule):
    sort = SORT_GENERATED_TOP_CELL

    lhs: App
    rhs: App
    req: Pattern | None
    ens: Pattern | None
    ctx: EVar | None
    priority: int
    uid: str
    label: str | None

    def to_axiom(self) -> Axiom:
        lhs = self.lhs if self.ctx is None else And(self.sort, (self.lhs, self.ctx))
        req = _to_ml_pred(self.req, self.sort)
        ens = _to_ml_pred(self.ens, self.sort)
        return Axiom(
            (),
            Rewrites(
                self.sort,
                And(self.sort, (lhs, req)),
                And(self.sort, (self.rhs, ens)),
            ),
        )

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
    sort: Sort
    arg_sorts: tuple[Sort, ...]
    anti_left: Pattern | None
    priority: int

    def to_axiom(self) -> Axiom:
        R = SortVar('R')  # noqa N806

        def arg_list(rest: Pattern, arg_pair: tuple[EVar, Pattern]) -> Pattern:
            var, arg = arg_pair
            return And(R, (In(var.sort, R, var, arg), rest))

        vars = tuple(EVar(f'X{i}', sort) for i, sort in enumerate(self.arg_sorts))

        # \and{R}(\in{S1, R}(X1 : S1, Arg1), \and{R}(\in{S2, R}(X2 : S2, Arg2), \top{R}())) etc.
        _args = reduce(
            arg_list,
            reversed(tuple(zip(vars, self.lhs.args, strict=True))),
            cast('Pattern', Top(R)),
        )

        _req = _to_ml_pred(self.req, R)
        req = And(R, (_req, _args))
        if self.anti_left:
            req = And(R, (Not(R, self.anti_left), req))

        app = self.lhs.let(args=vars)
        ens = _to_ml_pred(self.ens, self.sort)

        return Axiom(
            (R,),
            Implies(
                R,
                req,
                Equals(self.sort, R, app, And(self.sort, (self.rhs, ens))),
            ),
        )

    @staticmethod
    def from_axiom(axiom: Axiom) -> FunctionRule:
        anti_left: Pattern | None = None
        match axiom.pattern:
            case Implies(
                left=And(ops=(Not(pattern=anti_left), And(ops=(_req, _args)))),
                right=Equals(op_sort=sort, left=App() as app, right=_rhs),
            ):
                pass
            case Implies(
                left=And(ops=(_req, _args)),
                right=Equals(op_sort=sort, left=App() as app, right=_rhs),
            ):
                pass
            case _:
                raise ValueError(f'Cannot extract function rule from axiom: {axiom.text}')

        arg_sorts, args = FunctionRule._extract_args(_args)
        lhs = app.let(args=args)
        req = _extract_condition(_req)
        rhs, ens = _extract_rhs(_rhs)

        priority = _extract_priority(axiom)
        return FunctionRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            sort=sort,
            arg_sorts=arg_sorts,
            anti_left=anti_left,
            priority=priority,
        )

    @staticmethod
    def _extract_args(pattern: Pattern) -> tuple[tuple[Sort, ...], tuple[Pattern, ...]]:
        match pattern:
            case Top():
                return (), ()
            case And(ops=(In(left=EVar(sort=sort), right=arg), rest)):
                sorts, args = FunctionRule._extract_args(rest)
                return (sort,) + sorts, (arg,) + args
            case _:
                raise ValueError(f'Cannot extract argument list from pattern: {pattern.text}')


class SimpliRule(Rule, Generic[P], ABC):
    lhs: P
    sort: Sort

    def to_axiom(self) -> Axiom:
        R = SortVar('R')  # noqa N806

        vars = (R, self.sort) if isinstance(self.sort, SortVar) else (R,)
        req = _to_ml_pred(self.req, R)
        ens = _to_ml_pred(self.ens, self.sort)

        return Axiom(
            vars,
            Implies(
                R,
                req,
                Equals(self.sort, R, self.lhs, And(self.sort, (self.rhs, ens))),
            ),
            attrs=(
                App(
                    'simplification',
                    args=() if self.priority == 50 else (String(str(self.priority)),),
                ),
            ),
        )

    @staticmethod
    def _extract(axiom: Axiom, lhs_type: type[P]) -> tuple[P, Pattern, Pattern | None, Pattern | None, Sort]:
        match axiom.pattern:
            case Implies(left=_req, right=Equals(op_sort=sort, left=lhs, right=_rhs)):
                req = _extract_condition(_req)
                rhs, ens = _extract_rhs(_rhs)
                if not isinstance(lhs, lhs_type):
                    raise ValueError(f'Invalid LHS type from simplification axiom: {axiom.text}')
                return lhs, rhs, req, ens, sort
            case _:
                raise ValueError(f'Cannot extract simplification rule from axiom: {axiom.text}')


@final
@dataclass(frozen=True)
class AppRule(SimpliRule[App]):
    lhs: App
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    sort: Sort
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> AppRule:
        lhs, rhs, req, ens, sort = SimpliRule._extract(axiom, App)
        priority = _extract_simpl_priority(axiom)
        return AppRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            sort=sort,
            priority=priority,
        )


@final
@dataclass(frozen=True)
class CeilRule(SimpliRule[Ceil]):
    lhs: Ceil
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    sort: Sort
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> CeilRule:
        lhs, rhs, req, ens, sort = SimpliRule._extract(axiom, Ceil)
        priority = _extract_simpl_priority(axiom)
        return CeilRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            sort=sort,
            priority=priority,
        )


@final
@dataclass(frozen=True)
class EqualsRule(SimpliRule[Equals]):
    lhs: Equals
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    sort: Sort
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> EqualsRule:
        lhs, rhs, req, ens, sort = SimpliRule._extract(axiom, Equals)
        priority = _extract_simpl_priority(axiom)
        return EqualsRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            sort=sort,
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


def _extract_simpl_priority(axiom: Axiom) -> int:
    attrs = axiom.attrs_by_key
    match attrs['simplification']:
        case App(args=() | (String(''),)):
            return 50
        case App(args=(String(p),)):
            return int(p)
        case _:
            raise ValueError(f'Cannot extract simplification priority from axiom: {axiom.text}')


def _to_ml_pred(pattern: Pattern | None, sort: Sort) -> Pattern:
    if pattern is None:
        return Top(sort)

    return Equals(BOOL, sort, pattern, TRUE)
