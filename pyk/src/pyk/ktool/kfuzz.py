from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

from hypothesis import Phase, given, settings
from hypothesis.strategies import fixed_dictionaries, integers

from ..kore.parser import KoreParser
from ..kore.prelude import inj
from ..kore.syntax import DV, EVar, SortApp, String
from .krun import llvm_interpret_raw

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from pathlib import Path
    from typing import Any

    from hypothesis.strategies import SearchStrategy

    from ..kore.syntax import Pattern


class KFuzzHandler(ABC):
    """Allows custom behavior (ie. printing) during fuzzing for each test case and on a test failure.

    Can be passed to the `KFuzz` constructor or to :any:`fuzz` with the `handler` keyword argument.
    """

    @abstractmethod
    def handle_test(self, args: Mapping[EVar, Pattern]) -> None:
        """Handle each test case with the variable substitutions that are being used."""
        ...

    @abstractmethod
    def handle_failure(self, args: Mapping[EVar, Pattern]) -> None:
        """Handle a test case failure, before the `AssertionError` is raised."""
        ...


class _KFuzzNullHandler(KFuzzHandler):
    def handle_test(self, args: Mapping[EVar, Pattern]) -> None:
        pass

    def handle_failure(self, args: Mapping[EVar, Pattern]) -> None:
        pass


_DEFAULT_HANDLER = _KFuzzNullHandler()


class KFuzz:
    """Interface for fuzzing over property tests in K."""

    definition_dir: Path
    handler: KFuzzHandler

    def __init__(self, definition_dir: Path, handler: KFuzzHandler = _DEFAULT_HANDLER) -> None:
        self.definition_dir = definition_dir
        self.handler = handler

    def fuzz_with_check(
        self,
        template: Pattern,
        subst_strategy: dict[EVar, SearchStrategy[Pattern]],
        check_func: Callable[[Pattern], Any],
        **hypothesis_args: Any,
    ) -> None:
        """Fuzz over a property test using check_func to check for a passing test.

        See :any:`fuzz` for info on the parameters.
        """
        fuzz(
            self.definition_dir,
            template,
            subst_strategy,
            check_func=check_func,
            handler=self.handler,
            **hypothesis_args,
        )

    def fuzz_with_exit_code(
        self,
        template: Pattern,
        subst_strategy: dict[EVar, SearchStrategy[Pattern]],
        **hypothesis_args: Any,
    ) -> None:
        """Fuzz over a property test using the exit code from the interpreter to check for a passing test.

        See :any:`fuzz` for info on the parameters.
        """
        fuzz(
            self.definition_dir,
            template,
            subst_strategy,
            check_exit_code=True,
            handler=self.handler,
            **hypothesis_args,
        )


def kintegers(
    *,
    min_value: int | None = None,
    max_value: int | None = None,
    with_inj: str | None = None,
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
        res: Pattern = DV(SortApp('SortInt'), value=String(str(value)))
        if with_inj is not None:
            res = inj(SortApp('SortInt'), SortApp(f'Sort{with_inj}'), res)
        return res

    return integers(min_value=min_value, max_value=max_value).map(int_dv)


def fuzz(
    definition_dir: str | Path,
    template: Pattern,
    subst_strategy: dict[EVar, SearchStrategy[Pattern]],
    *,
    check_func: Callable[[Pattern], Any] | None = None,
    check_exit_code: bool = False,
    handler: KFuzzHandler = _DEFAULT_HANDLER,
    **hypothesis_args: Any,
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
        handler: An instance of a `KFuzzHandler` implementing custom behavior while fuzzing.
        hypothesis_args: Keyword arguments that will be passed as settings for the hypothesis test. Defaults:

          deadline: 5000

          phases: (Phase.explicit, Phase.reuse, Phase.generate)


    Raises:
        RuntimeError: If check_func exists and check_exit_code is set, or check_func doesn't exist and check_exit_code is cleared.
    """
    if bool(check_func) == check_exit_code:
        raise RuntimeError('Must pass one of check_func or check_exit_code, and not both!')

    def test(subst_case: Mapping[EVar, Pattern]) -> None:
        def sub(p: Pattern) -> Pattern:
            if isinstance(p, EVar) and p in subst_case:
                return subst_case[p]
            else:
                return p

        handler.handle_test(subst_case)
        test_pattern = template.top_down(sub)
        res = llvm_interpret_raw(definition_dir, test_pattern.text, check=False)

        try:
            if check_exit_code:
                assert res.returncode == 0
            else:
                assert check_func
                res_pattern = KoreParser(res.stdout).pattern()
                check_func(res_pattern)
        except AssertionError:
            handler.handle_failure(subst_case)
            raise

    strat: SearchStrategy = fixed_dictionaries(subst_strategy)

    # Default settings for hypothesis
    hypothesis_args.setdefault('deadline', 5000)
    hypothesis_args.setdefault('phases', (Phase.explicit, Phase.reuse, Phase.generate))

    given(strat)(settings(**hypothesis_args)(test))()
