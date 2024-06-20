from __future__ import annotations

from typing import TYPE_CHECKING

from hypothesis import Phase, Verbosity, given, settings
from hypothesis.strategies import builds, fixed_dictionaries, integers

from ..kast.inner import KSort
from ..konvert import _kast_to_kore
from ..kore.parser import KoreParser
from ..kore.syntax import Assoc, EVar
from ..prelude.k import inj
from ..prelude.kint import intToken
from .krun import llvm_interpret_raw

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from pathlib import Path

    from hypothesis.strategies import SearchStrategy

    from ..kast.inner import KInner
    from ..kore.syntax import Pattern


def kintegers(
    min_value: int | None = None, max_value: int | None = None, with_inj: KSort | None = None
) -> SearchStrategy[Pattern]:
    def int_dv(value: int) -> Pattern:
        res: KInner = intToken(value)
        if with_inj is not None:
            res = inj(KSort('Int'), with_inj, res)
        return _kast_to_kore(res)

    return builds(int_dv, integers(min_value=min_value, max_value=max_value))


def fuzz(
    definition_dir: str | Path,
    template: Pattern,
    subst_strategy: dict[EVar, SearchStrategy[Pattern]],
    check_func: Callable[[Pattern], None] | None = None,
    check_exit_code: bool = False,
    max_examples: int = 50,
) -> None:
    if not ((check_func is not None) ^ check_exit_code):
        raise RuntimeError('Must pass one of check_func or check_exit_code, and not both!')

    def test(subst_case: Mapping[EVar, Pattern]) -> None:
        def sub(p: Pattern) -> Pattern:
            if isinstance(p, Assoc):
                symbol = p.symbol()
                args = (arg.top_down(sub) for arg in p.app.args)
                return p.of(symbol, patterns=(p.app.let(args=args),))
            if p in subst_case.keys():
                assert isinstance(p, EVar)
                return subst_case[p]
            return p

        test_pattern = template.top_down(sub)
        res = llvm_interpret_raw(definition_dir, test_pattern.text)

        if check_exit_code:
            assert res.returncode == 0
        else:
            assert check_func is not None
            res_pattern = KoreParser(res.stdout).pattern()
            check_func(res_pattern)

    strat: SearchStrategy = fixed_dictionaries(subst_strategy)

    given(strat)(
        settings(
            deadline=50000,
            max_examples=max_examples,
            verbosity=Verbosity.verbose,
            phases=(Phase.generate, Phase.target, Phase.shrink),
        )(test)
    )()
