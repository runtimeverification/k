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
    from typing import Any

    from hypothesis.strategies import SearchStrategy

    from ..kast.inner import KInner
    from ..kore.syntax import Pattern


def kintegers(
    *,
    min_value: int | None = None,
    max_value: int | None = None,
    with_inj: KSort | None = None,
) -> SearchStrategy[Pattern]:
    """Return a search strategy for K integers.

    Args:
        min_value: Minimum value for the generated integers
        max_value: Maximum value for the generated integers
        with_inj: Return the integer as an injection into this sort

    Returns:
        A strategy which generates integer domain values.
    """

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
    check_func: Callable[[Pattern], Any] | None = None,
    check_exit_code: bool = False,
    max_examples: int = 50,
) -> None:
    """Fuzz a property test with concrete execution over a K term.

    Args:
        definition_dir: The location of the K definition to run the interpreter for.
        template: The term which will be sent to the interpreter after randomizing inputs. It should contain at least one variable which will be substituted for a value.
        subst_strategy: Should have each variable in the template term mapped to a strategy for generating values for it.
        check_func: Will be called on the kore output from the interpreter.
          Should throw an AssertionError if it determines that the output indicates a test failure.
          A RuntimeError will be thrown if this is passed as an argument and check_exit_code is True.
        check_exit_code: Check the exit code of the interpreter for a test failure instead of using check_func.
          An exit code of 0 indicates a passing test.
          A RuntimeError will be thrown if this is True and check_func is also passed as an argument.
        max_examples: The number of test cases to run.

    Raises:
        RuntimeError: If check_func exists and check_exit_code is set, or check_func doesn't exist and check_exit_code is cleared.
    """
    if bool(check_func) == check_exit_code:
        raise RuntimeError('Must pass one of check_func or check_exit_code, and not both!')

    def test(subst_case: Mapping[EVar, Pattern]) -> None:
        def sub(p: Pattern) -> Pattern:
            if isinstance(p, Assoc):
                symbol = p.symbol()
                args = (arg.top_down(sub) for arg in p.app.args)
                return p.of(symbol, patterns=(p.app.let(args=args),))
            if p in subst_case:
                assert isinstance(p, EVar)
                return subst_case[p]
            return p

        test_pattern = template.top_down(sub)
        res = llvm_interpret_raw(definition_dir, test_pattern.text)

        if check_exit_code:
            assert res.returncode == 0
        else:
            assert check_func
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
