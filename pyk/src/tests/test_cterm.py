from itertools import count
from typing import Final, List, Tuple

import pytest

from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast.inner import KApply, KAtt, KInner, KLabel, KRewrite, KSequence, KVariable
from pyk.kast.outer import KClaim
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlAnd, mlEqualsTrue

from .utils import a, b, c, f, g, h, k, x, y, z

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


MATCH_TEST_DATA: Final[Tuple[Tuple[KInner, KInner], ...]] = (
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


BUILD_RULE_TEST_DATA: Final = (
    (
        T(k(KVariable('K_CELL')), mem(KVariable('MEM_CELL'))),
        T(
            k(KVariable('K_CELL')),
            mem(KApply('_[_<-_]', [KVariable('MEM_CELL'), KVariable('KEY'), KVariable('VALUE')])),
        ),
        ['K_CELL'],
        T(
            k(KVariable('_K_CELL')),
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
def test_build_rule(lhs: KInner, rhs: KInner, keep_vars: List[str], expected: KInner) -> None:
    # When
    rule, _ = build_rule('test-rule', CTerm(lhs), CTerm(rhs), keep_vars=keep_vars)
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
        KClaim(k(KRewrite(v1_sorted, ques_unds_v2)), requires=constraint(v1), att=KAtt({'label': 'claim'})),
    ),
    (
        'sorted-var-2',
        mlAnd([k(v1), mlEqualsTrue(constraint(v1_sorted))]),
        k(v2),
        KClaim(k(KRewrite(v1, ques_unds_v2)), requires=constraint(v1_sorted), att=KAtt({'label': 'claim'})),
    ),
    (
        'req-rhs',
        mlAnd([k(v1), mlEqualsTrue(constraint(v2))]),
        k(v2),
        KClaim(k(KRewrite(unds_v1, v2)), requires=constraint(v2), att=KAtt({'label': 'claim'})),
    ),
    ('free-rhs', k(v1), k(v2), KClaim(k(KRewrite(unds_v1, ques_unds_v2)), att=KAtt({'label': 'claim'}))),
    (
        'bound-rhs',
        k(v1),
        mlAnd([k(v2), mlEqualsTrue(constraint(v2))]),
        KClaim(k(KRewrite(unds_v1, ques_v2)), ensures=constraint(ques_v2), att=KAtt({'label': 'claim'})),
    ),
)


@pytest.mark.parametrize(
    'test_id,init,target,expected',
    BUILD_CLAIM_TEST_DATA,
    ids=[test_id for test_id, *_ in BUILD_CLAIM_TEST_DATA],
)
def test_build_claim(test_id: str, init: KInner, target: KInner, expected: KClaim) -> None:
    # Given
    init_cterm = CTerm(init)
    target_cterm = CTerm(target)

    # When
    actual, _ = build_claim('claim', init_cterm, target_cterm)

    # Then
    assert actual == expected
