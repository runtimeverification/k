"""Parse KORE axioms into rewrite rules.

Based on the [LLVM Backend's implementation](https://github.com/runtimeverification/llvm-backend/blob/d5eab4b0f0e610bc60843ebb482f79c043b92702/lib/ast/pattern_matching.cpp).
"""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING, final

from .syntax import And, App, Ceil, Equals, EVar, Implies, In, Not, Rewrites, String, Top

if TYPE_CHECKING:
    from .syntax import Axiom, Definition, Pattern

    Attrs = dict[str, tuple[Pattern, ...]]


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

        attrs = (attr.symbol for attr in axiom.attrs)
        if 'simplification' in attrs:
            return SimpliRule.from_axiom(axiom)

        return FunctionRule.from_axiom(axiom)

    @staticmethod
    def extract_all(defn: Definition) -> list[Rule]:
        filter_attrs = [
            'assoc',
            'constructor',
            'functional',
            'idem',
            'symbol-overload',
            'subsort',
            'unit',
        ]

        res: list[Rule] = []
        for axiom in defn.axioms:
            attrs = {attr.symbol for attr in axiom.attrs}
            if any(attr in attrs for attr in filter_attrs):
                continue

            match axiom.pattern:
                case Equals():
                    # A single simplification from prelude module INJ:
                    # axiom {S1, S2, S3, R} \equals{S3, R}(inj{S2, S3}(inj{S1, S2}(T:S1)), inj{S1, S3}(T:S1)) [simplification{}()]
                    continue
                case Implies(right=Equals(left=Ceil())):
                    # Ceil rule
                    continue

            res.append(Rule.from_axiom(axiom))

        return res


@final
@dataclass
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
        lhs, req, ctx = RewriteRule._extract_lhs(axiom)
        rhs, ens = RewriteRule._extract_rhs(axiom)
        attrs = {attr.symbol: attr.args for attr in axiom.attrs}
        priority = _extract_priority(attrs)
        uid = _extract_uid(attrs)
        label = _extract_label(attrs)
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
    def _extract_lhs(axiom: Axiom) -> tuple[App, Pattern | None, EVar | None]:
        req: Pattern | None = None
        # Cases 0-5 of get_left_hand_side
        # Cases 5-10 of get_requires
        match axiom.pattern:
            case Rewrites(left=And(ops=(Top(), lhs))):
                pass
            case Rewrites(left=And(ops=(Equals(left=req), lhs))):
                pass
            case Rewrites(left=And(ops=(lhs, Top()))):
                pass
            case Rewrites(left=And(ops=(lhs, Equals(left=req)))):
                pass
            case Rewrites(left=And(ops=(Not(), And(ops=(Top(), lhs))))):
                pass
            case Rewrites(left=And(ops=(Not(), And(ops=(Equals(left=req), lhs))))):
                pass
            case _:
                raise ValueError(f'Cannot extract LHS from axiom: {axiom.text}')

        ctx: EVar | None = None
        match lhs:
            case App("Lbl'-LT-'generatedTop'-GT-'") as app:
                pass
            case And(_, (App("Lbl'-LT-'generatedTop'-GT-'") as app, EVar("Var'Hash'Configuration") as ctx)):
                pass

        return app, req, ctx

    @staticmethod
    def _extract_rhs(axiom: Axiom) -> tuple[App, Pattern | None]:
        # Case 2 of get_right_hand_side:
        # 2: rhs(\rewrites(_, \and(X, Y))) = get_builtin(\and(X, Y))
        # Below is a special case without get_builtin
        match axiom.pattern:
            case Rewrites(right=And(ops=(App("Lbl'-LT-'generatedTop'-GT-'") as rhs, Top() | Equals() as _ens))):
                pass
            case _:
                raise ValueError(f'Cannot extract RHS from axiom: {axiom.text}')
        ens = _extract_ensures(_ens)
        return rhs, ens


@final
@dataclass
class FunctionRule(Rule):
    lhs: App
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> FunctionRule:
        args, req = FunctionRule._extract_args(axiom)
        app, rhs, ens = FunctionRule._extract_rhs(axiom)
        lhs = app.let(args=args)
        attrs = {attr.symbol: attr.args for attr in axiom.attrs}
        priority = _extract_priority(attrs)
        return FunctionRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )

    @staticmethod
    def _extract_args(axiom: Axiom) -> tuple[tuple[Pattern, ...], Pattern | None]:
        req: Pattern | None = None
        # Cases 7-10 of get_left_hand_side
        # Cases 0-3 of get_requires
        match axiom.pattern:
            case Implies(left=And(ops=(Top(), pat))):
                return FunctionRule._get_patterns(pat), req
            case Implies(left=And(ops=(Equals(left=req), pat))):
                return FunctionRule._get_patterns(pat), req
            case Implies(left=And(ops=(Not(), And(ops=(Top(), pat))))):
                return FunctionRule._get_patterns(pat), req
            case Implies(left=And(ops=(Not(), And(ops=(Equals(left=req), pat))))):
                return FunctionRule._get_patterns(pat), req
            case _:
                raise ValueError(f'Cannot extract LHS from axiom: {axiom.text}')

    @staticmethod
    def _get_patterns(pattern: Pattern) -> tuple[Pattern, ...]:
        # get_patterns(\top()) = []
        # get_patterns(\and(\in(_, X), Y)) = X : get_patterns(Y)
        match pattern:
            case Top():
                return ()
            case And(ops=(In(right=x), y)):
                return (x,) + FunctionRule._get_patterns(y)
            case _:
                raise AssertionError()

    @staticmethod
    def _extract_rhs(axiom: Axiom) -> tuple[App, Pattern, Pattern | None]:
        # Case 0 of get_right_hand_side
        match axiom.pattern:
            case Implies(right=Equals(left=App() as app, right=And(ops=(rhs, Top() | Equals() as _ens)))):
                pass
            case _:
                raise ValueError(f'Cannot extract RHS from axiom: {axiom.text}')
        ens = _extract_ensures(_ens)
        return app, rhs, ens


@final
@dataclass
class SimpliRule(Rule):
    lhs: Pattern
    rhs: Pattern
    req: Pattern | None
    ens: Pattern | None
    priority: int

    @staticmethod
    def from_axiom(axiom: Axiom) -> SimpliRule:
        lhs, rhs, req, ens = SimpliRule._extract(axiom)
        attrs = {attr.symbol: attr.args for attr in axiom.attrs}
        priority = _extract_priority(attrs)
        return SimpliRule(
            lhs=lhs,
            rhs=rhs,
            req=req,
            ens=ens,
            priority=priority,
        )

    @staticmethod
    def _extract(axiom: Axiom) -> tuple[Pattern, Pattern, Pattern | None, Pattern | None]:
        req: Pattern | None = None
        # Cases 11-12 of get_left_hand_side
        # Case 0 of get_right_hand_side
        match axiom.pattern:
            case Implies(left=Top(), right=Equals(left=lhs, right=And(ops=(rhs, Top() | Equals() as _ens)))):
                pass
            case Implies(left=Equals(left=req), right=Equals(left=lhs, right=And(ops=(rhs, Top() | Equals() as _ens)))):
                pass
            case Equals():
                raise ValueError(f'Not a user-defined simplification rule: {axiom.text}')
            case Implies(right=Equals(left=Ceil())):
                raise ValueError(f'Axiom is a ceil rule: {axiom.text}')
            case _:
                raise ValueError(f'Cannot extract simplification rule from axiom: {axiom.text}')
        ens = _extract_ensures(_ens)
        return lhs, rhs, req, ens


def _extract_ensures(ens: Top | Equals | None) -> Pattern | None:
    match ens:
        case Top():
            return None
        case Equals(left=res):
            return res
        case _:
            raise AssertionError()


def _extract_uid(attrs: Attrs) -> str:
    match attrs["UNIQUE'Unds'ID"]:
        case (String(uid),):
            return uid
        case _:
            raise ValueError(f'Cannot extract uid from attributes: {attrs}')


def _extract_label(attrs: Attrs) -> str | None:
    match attrs.get('label'):
        case (String(label),):
            return label
        case None:
            return None
        case _:
            raise ValueError(f'Cannot extract label from attributes: {attrs}')


def _extract_priority(attrs: Attrs) -> int:
    match attrs.get('priority'):
        case (String(p),):
            return int(p)
        case None:
            return 200 if 'owise' in attrs else 50
        case _:
            raise ValueError(f'Cannot extract priority from attributes: {attrs}')
