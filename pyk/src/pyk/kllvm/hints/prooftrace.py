from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, final

# isort: off
import pyk.kllvm.load_static  # noqa: F401
from _kllvm.prooftrace import (  # type: ignore  # noqa: F401, TC002
    kore_header,
    llvm_rewrite_event,
    llvm_function_event,
    llvm_hook_event,
    llvm_rewrite_trace,
    llvm_rule_event,
    llvm_side_condition_end_event,
    llvm_side_condition_event,
    llvm_step_event,
)
from ..ast import Pattern

# isort: on

if TYPE_CHECKING:
    from _kllvm.prooftrace import Argument


class LLVMStepEvent(ABC):
    pass


class LLVMRewriteEvent(LLVMStepEvent):
    @property
    @abstractmethod
    def rule_ordinal(self) -> int: ...

    @property
    @abstractmethod
    def substitution(self) -> dict[str, Pattern]: ...


@final
class LLVMRuleEvent(LLVMRewriteEvent):
    _rule_event: llvm_rule_event

    def __init__(self, rule_event: llvm_rule_event) -> None:
        self._rule_event = rule_event

    def __repr__(self) -> str:
        return self._rule_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        return self._rule_event.rule_ordinal

    @property
    def substitution(self) -> dict[str, Pattern]:
        return {k: v[0] for k, v in self._rule_event.substitution.items()}


@final
class LLVMSideConditionEventEnter(LLVMRewriteEvent):
    _side_condition_event: llvm_side_condition_event

    def __init__(self, side_condition_event: llvm_side_condition_event) -> None:
        self._side_condition_event = side_condition_event

    def __repr__(self) -> str:
        return self._side_condition_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        return self._side_condition_event.rule_ordinal

    @property
    def substitution(self) -> dict[str, Pattern]:
        return {k: v[0] for k, v in self._side_condition_event.substitution.items()}


@final
class LLVMSideConditionEventExit(LLVMStepEvent):
    _side_condition_end_event: llvm_side_condition_end_event

    def __init__(self, side_condition_end_event: llvm_side_condition_end_event) -> None:
        self._side_condition_end_event = side_condition_end_event

    def __repr__(self) -> str:
        return self._side_condition_end_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        return self._side_condition_end_event.rule_ordinal

    @property
    def check_result(self) -> bool:
        return self._side_condition_end_event.check_result


@final
class LLVMFunctionEvent(LLVMStepEvent):
    _function_event: llvm_function_event

    def __init__(self, function_event: llvm_function_event) -> None:
        self._function_event = function_event

    def __repr__(self) -> str:
        return self._function_event.__repr__()

    @property
    def name(self) -> str:
        return self._function_event.name

    @property
    def relative_position(self) -> str:
        return self._function_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        return [LLVMArgument(arg) for arg in self._function_event.args]


@final
class LLVMHookEvent(LLVMStepEvent):
    _hook_event: llvm_hook_event

    def __init__(self, hook_event: llvm_hook_event) -> None:
        self._hook_event = hook_event

    def __repr__(self) -> str:
        return self._hook_event.__repr__()

    @property
    def name(self) -> str:
        return self._hook_event.name

    @property
    def relative_position(self) -> str:
        return self._hook_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        return [LLVMArgument(arg) for arg in self._hook_event.args]

    @property
    def result(self) -> Pattern:
        return self._hook_event.result


@final
class LLVMArgument:
    _argument: Argument

    def __init__(self, argument: Argument) -> None:
        self._argument = argument

    def __repr__(self) -> str:
        return self._argument.__repr__()

    @property
    def step_event(self) -> LLVMStepEvent:
        if isinstance(self._argument.step_event, llvm_rule_event):
            return LLVMRuleEvent(self._argument.step_event)
        elif isinstance(self._argument.step_event, llvm_side_condition_event):
            return LLVMSideConditionEventEnter(self._argument.step_event)
        elif isinstance(self._argument.step_event, llvm_side_condition_end_event):
            return LLVMSideConditionEventExit(self._argument.step_event)
        elif isinstance(self._argument.step_event, llvm_function_event):
            return LLVMFunctionEvent(self._argument.step_event)
        elif isinstance(self._argument.step_event, llvm_hook_event):
            return LLVMHookEvent(self._argument.step_event)
        else:
            raise AssertionError()

    @property
    def kore_pattern(self) -> Pattern:
        assert isinstance(self._argument.kore_pattern, Pattern)
        return self._argument.kore_pattern

    def is_kore_pattern(self) -> bool:
        return self._argument.is_kore_pattern()

    def is_step_event(self) -> bool:
        return self._argument.is_step_event()


@final
class LLVMRewriteTrace:
    _rewrite_trace: llvm_rewrite_trace

    def __init__(self, rewrite_trace: llvm_rewrite_trace) -> None:
        self._rewrite_trace = rewrite_trace

    def __repr__(self) -> str:
        return self._rewrite_trace.__repr__()

    @property
    def version(self) -> int:
        return self._rewrite_trace.version

    @property
    def pre_trace(self) -> list[LLVMArgument]:
        return [LLVMArgument(event) for event in self._rewrite_trace.pre_trace]

    @property
    def initial_config(self) -> LLVMArgument:
        return LLVMArgument(self._rewrite_trace.initial_config)

    @property
    def trace(self) -> list[LLVMArgument]:
        return [LLVMArgument(event) for event in self._rewrite_trace.trace]

    @staticmethod
    def parse(trace: bytes, header: kore_header) -> LLVMRewriteTrace:
        return LLVMRewriteTrace(llvm_rewrite_trace.parse(trace, header))
