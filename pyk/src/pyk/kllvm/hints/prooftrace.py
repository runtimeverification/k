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
    """
    Abstract base class representing an LLVM step event.
    """


class LLVMRewriteEvent(LLVMStepEvent):
    """
    Represents LLVM rewrite event.
    """

    @property
    @abstractmethod
    def rule_ordinal(self) -> int:
        """Returns the axiom ordinal number of the rewrite rule. The rule ordinal represents the `nth` axiom in the kore definition."""
        ...

    @property
    @abstractmethod
    def substitution(self) -> dict[str, Pattern]:
        """Returns the substitution dictionary used to perform the rewrite represented by this event."""
        ...


@final
class LLVMRuleEvent(LLVMRewriteEvent):
    """
    Represents an LLVM rule event.

    Attributes:
        _rule_event (llvm_rule_event): The underlying LLVM rule event.

    Methods:
        __init__(self, rule_event: llvm_rule_event) -> None: Initializes a new instance of the LLVMRuleEvent class.

        __repr__(self) -> str: Returns a string representation of the LLVMRuleEvent object using the AST printing method.
    """

    _rule_event: llvm_rule_event

    def __init__(self, rule_event: llvm_rule_event) -> None:
        self._rule_event = rule_event

    def __repr__(self) -> str:
        return self._rule_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        """Returns the axiom ordinal number of the rule event."""
        return self._rule_event.rule_ordinal

    @property
    def substitution(self) -> dict[str, Pattern]:
        """Returns the substitution dictionary used to perform the rewrite represented by this rule event."""
        return {k: v[0] for k, v in self._rule_event.substitution.items()}


@final
class LLVMSideConditionEventEnter(LLVMRewriteEvent):
    """
    Represents an event that enters a side condition in LLVM rewriting. This event is used to check the side condition of a rule. Mostly used in ensures/requires clauses.

    Attributes:
        _side_condition_event (llvm_side_condition_event): The underlying side condition event.

    Methods:
        __init__(self, side_condition_event: llvm_side_condition_event) -> None: Initializes a new instance of the LLVMSideConditionEventEnter class.

        __repr__(self) -> str: Returns a string representation of the LLVMSideConditionEventEnter object using the AST printing method.
    """

    _side_condition_event: llvm_side_condition_event

    def __init__(self, side_condition_event: llvm_side_condition_event) -> None:
        self._side_condition_event = side_condition_event

    def __repr__(self) -> str:
        return self._side_condition_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        """Returns the axiom ordinal number associated with the side condition event."""
        return self._side_condition_event.rule_ordinal

    @property
    def substitution(self) -> dict[str, Pattern]:
        """Returns the substitution dictionary used to perform the rewrite represented by this side condition event."""
        return {k: v[0] for k, v in self._side_condition_event.substitution.items()}


@final
class LLVMSideConditionEventExit(LLVMStepEvent):
    """
    Represents an LLVM side condition event indicating the exit of a side condition. This event contains the result of the side condition evaluation.

    Attributes:
        _side_condition_end_event (llvm_side_condition_end_event): The underlying side condition end event.

    Methods:
        __init__(side_condition_end_event: llvm_side_condition_end_event) -> None: Initializes the LLVMSideConditionEventExit instance.

        __repr__(self) -> str: Returns a string representation of the LLVMSideConditionEventExit instance using the AST printing method.
    """

    _side_condition_end_event: llvm_side_condition_end_event

    def __init__(self, side_condition_end_event: llvm_side_condition_end_event) -> None:
        self._side_condition_end_event = side_condition_end_event

    def __repr__(self) -> str:
        return self._side_condition_end_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        """Returns the axiom ordinal number associated with the side condition event."""
        return self._side_condition_end_event.rule_ordinal

    @property
    def check_result(self) -> bool:
        """Returns the boolean result of the evaluation of the side condition that corresponds to this event."""
        return self._side_condition_end_event.check_result


@final
class LLVMFunctionEvent(LLVMStepEvent):
    """
    Represents an LLVM function event in a proof trace.

    Attributes:
        _function_event (llvm_function_event): The underlying LLVM function event object.

    Methods:
        __init__(self, function_event: llvm_function_event) -> None: Initializes a new instance of the LLVMFunctionEvent class.

        __repr__(self) -> str: Returns a string representation of the LLVMFunctionEvent object using the AST printing method.
    """

    _function_event: llvm_function_event

    def __init__(self, function_event: llvm_function_event) -> None:
        self._function_event = function_event

    def __repr__(self) -> str:
        return self._function_event.__repr__()

    @property
    def name(self) -> str:
        """Returns the name of the LLVM function as a KORE Symbol Name."""
        return self._function_event.name

    @property
    def relative_position(self) -> str:
        """Returns the relative position of the LLVM function event in the proof trace. Ex.: (0:0:0:0)"""
        return self._function_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        """Returns a list of LLVMArgument objects representing the arguments of the LLVM function."""
        return [LLVMArgument(arg) for arg in self._function_event.args]


@final
class LLVMHookEvent(LLVMStepEvent):
    """
    Represents a hook event in LLVM execution.

    Attributes:
        _hook_event (llvm_hook_event): The underlying hook event object.

    Methods:
        __init__(hook_event: llvm_hook_event): Initializes a new instance of the LLVMHookEvent class.

        __repr__() -> str: Returns a string representation of the LLVMHookEvent object using the AST printing method.
    """

    _hook_event: llvm_hook_event

    def __init__(self, hook_event: llvm_hook_event) -> None:
        self._hook_event = hook_event

    def __repr__(self) -> str:
        return self._hook_event.__repr__()

    @property
    def name(self) -> str:
        """Returns the attribute name of the hook event. Ex.: "INT.add" """
        return self._hook_event.name

    @property
    def relative_position(self) -> str:
        """Returns the relative position of the hook event in the proof trace. Ex.: (0:0:0:0)"""
        return self._hook_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        """Returns a list of LLVMArgument objects representing the arguments of the hook event."""
        return [LLVMArgument(arg) for arg in self._hook_event.args]

    @property
    def result(self) -> Pattern:
        """Returns the result pattern of the hook event evaluation."""
        return self._hook_event.result


@final
class LLVMArgument:
    """
    Represents an LLVM argument.

    Attributes:
        _argument (Argument): The underlying Argument object. An argument is a wrapper object containing either a step event or a KORE pattern.

    Methods:
        __init__(self, argument: Argument) -> None: Initializes the LLVMArgument object.

        __repr__(self) -> str: Returns a string representation of the LLVMArgument object using the AST printing method.
    """

    _argument: Argument

    def __init__(self, argument: Argument) -> None:
        self._argument = argument

    def __repr__(self) -> str:
        return self._argument.__repr__()

    @property
    def step_event(self) -> LLVMStepEvent:
        """Returns the LLVMStepEvent associated with the argument if any."""
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
        """Returns the KORE Pattern associated with the argument if any."""
        assert isinstance(self._argument.kore_pattern, Pattern)
        return self._argument.kore_pattern

    def is_kore_pattern(self) -> bool:
        """Checks if the argument is a KORE Pattern."""
        return self._argument.is_kore_pattern()

    def is_step_event(self) -> bool:
        """Checks if the argument is a step event."""
        return self._argument.is_step_event()


@final
class LLVMRewriteTrace:
    """
    Represents an LLVM rewrite trace.

    Attributes:
        _rewrite_trace (llvm_rewrite_trace): The underlying LLVM rewrite trace object.

    Methods:
        __init__(self, rewrite_trace: llvm_rewrite_trace) -> None: Initializes a new instance of the LLVMRewriteTrace class.

        __repr__(self) -> str: Returns a string representation of the LLVMRewriteTrace object using the AST printing method.
    """

    _rewrite_trace: llvm_rewrite_trace

    def __init__(self, rewrite_trace: llvm_rewrite_trace) -> None:
        self._rewrite_trace = rewrite_trace

    def __repr__(self) -> str:
        return self._rewrite_trace.__repr__()

    @property
    def version(self) -> int:
        """Returns the version of the HINTS formart."""
        return self._rewrite_trace.version

    @property
    def pre_trace(self) -> list[LLVMArgument]:
        """Returns the pre-trace events as a list of LLVMArgument objects."""
        return [LLVMArgument(event) for event in self._rewrite_trace.pre_trace]

    @property
    def initial_config(self) -> LLVMArgument:
        """Returns the initial configuration as an LLVMArgument object."""
        return LLVMArgument(self._rewrite_trace.initial_config)

    @property
    def trace(self) -> list[LLVMArgument]:
        """Returns the trace events as a list of LLVMArgument objects."""
        return [LLVMArgument(event) for event in self._rewrite_trace.trace]

    @staticmethod
    def parse(trace: bytes, header: kore_header) -> LLVMRewriteTrace:
        """Parses the given proof hints byte string using the given kore_header object to create an LLVMRewriteTrace object."""
        return LLVMRewriteTrace(llvm_rewrite_trace.parse(trace, header))
