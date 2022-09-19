from typing import Final, Tuple
from unittest import TestCase

from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast import KApply, KAtt, KClaim, KInner, KLabel, KRewrite, KSequence, KVariable
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kint import intToken
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


def _as_cterm(term: KInner) -> CTerm:
    return CTerm(KApply(KLabel('<generatedTop>', (GENERATED_TOP_CELL,)), (term,)))


class CTermTest(TestCase):
    def test_cterm_match_and_subst(self) -> None:
        # Given
        test_data: Final[Tuple[Tuple[KInner, KInner], ...]] = (
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

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst_cterm = _as_cterm(pattern).match(_as_cterm(term))

                # Then
                self.assertIsNotNone(subst_cterm)
                assert subst_cterm is not None  # https://github.com/python/mypy/issues/4063
                self.assertEqual(subst_cterm(pattern), term)

    def test_no_cterm_match(self) -> None:
        # Given
        test_data: Final[Tuple[Tuple[KInner, KInner], ...]] = ((f(x, x), f(x, a)),)

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst_cterm = _as_cterm(pattern).match(_as_cterm(term))

                # Then
                self.assertIsNone(subst_cterm)


class BuildRuleTest(TestCase):
    def test_build_rule(self) -> None:
        # Given
        test_data = [
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
            )
        ]

        for i, (lhs, rhs, keep_vars, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                rule, _ = build_rule(f'test-{i}', CTerm(lhs), CTerm(rhs), keep_vars=keep_vars)
                actual = rule.body

                # Then
                self.assertEqual(actual, expected)


class BuildClaimtest(TestCase):
    def test_build_claim(self) -> None:
        # (<k> V1 </k> #And { true #Equals 0 <=Int V2}) => <k> V2 </k>      expected: <k> _V1 => V2 </k> requires 0 <=Int V2
        # <k> V1 </k> => <k> V2 </k>                                        expected: <k> _V1 => ?_V2 </k>
        # <k> V1 </k> => <k> V2 </k> #And { true #Equals 0 <=Int V2 }       expected: <k> _V1 => ?V2 </k> ensures 0 <=Int ?V2

        def constraint(v: KVariable) -> KInner:
            return KApply('_<=Int_', [intToken(0), v])

        test_data = (
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

        for name, init, target, claim in test_data:
            with self.subTest(name):
                init_cterm = CTerm(init)
                target_cterm = CTerm(target)
                kclaim, _ = build_claim('claim', init_cterm, target_cterm)
                self.assertEqual(kclaim, claim)
