from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CSubst, CTerm, cterm_build_claim, cterm_build_rule
from pyk.kast import Atts, KAtt
from pyk.kast.inner import KApply, KLabel, KRewrite, KSequence, KSort, KVariable, Subst
from pyk.kast.outer import KClaim
from pyk.kast.prelude.k import GENERATED_TOP_CELL, K
from pyk.kast.prelude.kbool import TRUE
from pyk.kast.prelude.kint import INT, geInt, intToken
from pyk.kast.prelude.ml import mlAnd, mlEquals, mlEqualsTrue, mlTop

from .utils import a, b, c, f, g, ge_ml, h, k, lt_ml, x, y, z

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner


mem = KLabel('<mem>')

T = KLabel('<T>')
K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])

v1 = KVariable('V1')
v2 = KVariable('V2')
unds_v1 = KVariable('_V1')
ques_v2 = KVariable('?V2')
ques_unds_v2 = KVariable('?_V2')
v1_sorted = KVariable('V1', sort=INT)


def _as_cterm(term: KInner) -> CTerm:
    return CTerm(KApply(KLabel('<generatedTop>', GENERATED_TOP_CELL), term))


MATCH_TEST_DATA: Final[tuple[tuple[KInner, KInner], ...]] = (
    (a, a),
    (a, x),
    (f(a), x),
    (f(a), f(a)),
    (f(a), f(x)),
    (f(a, b), f(x, y)),
    (f(a, b, c), f(x, y, z)),
    (f(g(h(a))), f(x)),
    (f(g(h(x))), f(x)),
    (f(a, g(b, h(c))), f(x, y)),
)


@pytest.mark.parametrize('term,pattern', MATCH_TEST_DATA, ids=count())
def test_cterm_match_and_subst(term: KInner, pattern: KInner) -> None:
    # When
    subst = _as_cterm(pattern).match(_as_cterm(term))

    # Then
    assert subst is not None
    assert subst(pattern) == term


NO_MATCH_TEST_DATA: Final = ((f(x, x), f(x, a)),)


@pytest.mark.parametrize('term,pattern', NO_MATCH_TEST_DATA, ids=count())
def test_no_cterm_match(term: KInner, pattern: KInner) -> None:
    # When
    subst = _as_cterm(pattern).match(_as_cterm(term))

    # Then
    assert subst is None


MATCH_WITH_CONSTRAINT_TEST_DATA: Final = (
    (CTerm(k(x)), CTerm(k(x))),
    (CTerm(k(x)), CTerm(k(y))),
    (CTerm(k(x)), CTerm(k(y), (mlEqualsTrue(geInt(y, intToken(0))),))),
    (
        CTerm(k(x), (mlEqualsTrue(geInt(y, intToken(0))),)),
        CTerm(
            k(y),
            (
                mlEqualsTrue(geInt(y, intToken(0))),
                mlEqualsTrue(geInt(y, intToken(5))),
            ),
        ),
    ),
)


@pytest.mark.parametrize('t1, t2', MATCH_WITH_CONSTRAINT_TEST_DATA, ids=count())
def test_cterm_match_with_constraint(t1: CTerm, t2: CTerm) -> None:
    # When
    c_subst1 = t1.match_with_constraint(t2)

    # Then
    assert c_subst1 is not None and c_subst1.apply(t1) == t2


BUILD_RULE_TEST_DATA: Final = (
    (
        T(k(KVariable('K_CELL', 'K')), mem(KVariable('MEM_CELL'))),
        T(
            k(KVariable('K_CELL')),
            mem(KApply('_[_<-_]', [KVariable('MEM_CELL'), KVariable('KEY'), KVariable('VALUE')])),
        ),
        ['K_CELL'],
        T(
            k(KVariable('_K_CELL', 'K')),
            mem(
                KRewrite(
                    KVariable('MEM_CELL'),
                    KApply('_[_<-_]', [KVariable('MEM_CELL'), KVariable('?_KEY'), KVariable('?_VALUE')]),
                )
            ),
        ),
    ),
)


@pytest.mark.parametrize('lhs,rhs,keep_vars,expected', BUILD_RULE_TEST_DATA, ids=count())
def test_build_rule(lhs: KInner, rhs: KInner, keep_vars: list[str], expected: KInner) -> None:
    # When
    rule, _ = cterm_build_rule('test-rule', CTerm.from_kast(lhs), CTerm.from_kast(rhs), keep_vars=keep_vars)
    actual = rule.body

    # Then
    assert actual == expected


def constraint(v: KVariable) -> KInner:
    return KApply('_<=Int_', intToken(0), v)


# (<k> V1 </k> #And { true #Equals 0 <=Int V2}) => <k> V2 </k>      expected: <k> _V1 => V2 </k> requires 0 <=Int V2
# <k> V1 </k> => <k> V2 </k>                                        expected: <k> _V1 => ?_V2 </k>
# <k> V1 </k> => <k> V2 </k> #And { true #Equals 0 <=Int V2 }       expected: <k> _V1 => ?V2 </k> ensures 0 <=Int ?V2
BUILD_CLAIM_TEST_DATA: Final = (
    (
        'sorted-var-1',
        mlAnd([k(v1_sorted), mlEqualsTrue(constraint(v1))]),
        k(v2),
        KClaim(k(KRewrite(v1_sorted, ques_unds_v2)), requires=constraint(v1), att=KAtt([Atts.LABEL('claim')])),
    ),
    (
        'sorted-var-2',
        mlAnd([k(v1), mlEqualsTrue(constraint(v1_sorted))]),
        k(v2),
        KClaim(k(KRewrite(v1, ques_unds_v2)), requires=constraint(v1_sorted), att=KAtt([Atts.LABEL('claim')])),
    ),
    (
        'req-rhs',
        mlAnd([k(v1), mlEqualsTrue(constraint(v2))]),
        k(v2),
        KClaim(k(KRewrite(unds_v1, v2)), requires=constraint(v2), att=KAtt([Atts.LABEL('claim')])),
    ),
    ('free-rhs', k(v1), k(v2), KClaim(k(KRewrite(unds_v1, ques_unds_v2)), att=KAtt([Atts.LABEL('claim')]))),
    (
        'bound-rhs',
        k(v1),
        mlAnd([k(v2), mlEqualsTrue(constraint(v2))]),
        KClaim(k(KRewrite(unds_v1, ques_v2)), ensures=constraint(ques_v2), att=KAtt([Atts.LABEL('claim')])),
    ),
)


@pytest.mark.parametrize(
    'test_id,init,target,expected',
    BUILD_CLAIM_TEST_DATA,
    ids=[test_id for test_id, *_ in BUILD_CLAIM_TEST_DATA],
)
def test_build_claim(test_id: str, init: KInner, target: KInner, expected: KClaim) -> None:
    # Given
    init_cterm = CTerm.from_kast(init)
    target_cterm = CTerm.from_kast(target)

    # When
    actual, _ = cterm_build_claim('claim', init_cterm, target_cterm)

    # Then
    assert actual == expected


KAST_TEST_DATA: Final = (
    ('simple-bottom', KApply('#Bottom'), CTerm.bottom()),
    ('simple-top', KApply('#Top'), CTerm.top()),
    (
        'double-and-bottom',
        KApply(
            label=KLabel(name='#And', params=(KSort(name='GeneratedTopCell'),)),
            args=(
                KApply(label=KLabel(name='#Bottom', params=(KSort(name='GeneratedTopCell'),)), args=()),
                KApply(label=KLabel(name='#Bottom', params=(KSort(name='GeneratedTopCell'),)), args=()),
            ),
        ),
        CTerm.bottom(),
    ),
)


@pytest.mark.parametrize(
    'test_id,kast,expected',
    KAST_TEST_DATA,
    ids=[test_id for test_id, *_ in KAST_TEST_DATA],
)
def test_from_kast(test_id: str, kast: KInner, expected: CTerm) -> None:
    # When
    cterm = CTerm.from_kast(kast)

    # Then
    assert cterm == expected


ML_PRED_TEST_DATA: Final = (
    ('empty', CSubst(Subst({})), mlTop()),
    ('singleton', CSubst(Subst({'X': TRUE})), mlEquals(KVariable('X', sort=K), TRUE, arg_sort=K)),
    ('identity', CSubst(Subst({'X': KVariable('X')})), mlTop()),
    (
        'double',
        CSubst(Subst({'X': TRUE, 'Y': intToken(4)})),
        mlAnd(
            [
                mlEquals(KVariable('X', sort=K), TRUE, arg_sort=K),
                mlEquals(KVariable('Y', sort=K), intToken(4), arg_sort=K),
            ]
        ),
    ),
)


@pytest.mark.parametrize('test_id,csubst,pred', ML_PRED_TEST_DATA, ids=[test_id for test_id, *_ in ML_PRED_TEST_DATA])
def test_ml_pred(test_id: str, csubst: CSubst, pred: KInner) -> None:
    assert csubst.pred() == pred


APPLY_TEST_DATA: Final = (
    (CTerm.top(), CSubst(), CTerm.top()),
    (CTerm.bottom(), CSubst(), CTerm.bottom()),
    (
        CTerm(k(KVariable('X'))),
        CSubst(),
        CTerm(k(KVariable('X'))),
    ),
    (
        CTerm(k(KVariable('X'))),
        CSubst(Subst({'X': intToken(5)})),
        CTerm(k(intToken(5))),
    ),
    (
        CTerm(k(KVariable('X'))),
        CSubst(Subst({'X': KVariable('Y')})),
        CTerm(k(KVariable('Y'))),
    ),
    (
        CTerm(k(KVariable('X')), [lt_ml('X', 5)]),
        CSubst(Subst({'X': KVariable('Y')}), [ge_ml('Y', 0)]),
        CTerm(k(KVariable('Y')), [ge_ml('Y', 0), lt_ml('Y', 5)]),
    ),
)


@pytest.mark.parametrize(
    'term,subst,expected',
    APPLY_TEST_DATA,
)
def test_csubst_apply(term: CTerm, subst: CSubst, expected: CTerm) -> None:
    # When
    actual = subst(term)

    # Then
    assert actual == expected
