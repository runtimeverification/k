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
    annotated_llvm_event,
    llvm_rewrite_trace_iterator,
    EventType,
)
from ..ast import Pattern

# isort: on

if TYPE_CHECKING:
    from collections.abc import Generator
    from pathlib import Path

    from _kllvm.prooftrace import Argument


class LLVMStepEvent(ABC):
    """Abstract base class representing an LLVM step event."""


class LLVMRewriteEvent(LLVMStepEvent):
    """Represents LLVM rewrite event."""

    @property
    @abstractmethod
    def rule_ordinal(self) -> int:
        """Return the axiom ordinal number of the rewrite rule.

        The rule ordinal represents the `nth` axiom in the kore definition.
        """
        ...

    @property
    @abstractmethod
    def substitution(self) -> dict[str, Pattern]:
        """Returns the substitution dictionary used to perform the rewrite represented by this event."""
        ...


@final
class LLVMRuleEvent(LLVMRewriteEvent):
    """Represents an LLVM rule event.

    Attributes:
        _rule_event (llvm_rule_event): The underlying LLVM rule event.
    """

    _rule_event: llvm_rule_event

    def __init__(self, rule_event: llvm_rule_event) -> None:
        """Initialize a new instance of the LLVMRuleEvent class.

        Args:
            rule_event (llvm_rule_event): The LLVM rule event object.
        """
        self._rule_event = rule_event

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMRuleEvent object using the AST printing method.
        """
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
    """Represents an event that enters a side condition in LLVM rewriting.

    This event is used to check the side condition of a rule. Mostly used in ensures/requires clauses.

    Attributes:
        _side_condition_event (llvm_side_condition_event): The underlying side condition event.
    """

    _side_condition_event: llvm_side_condition_event

    def __init__(self, side_condition_event: llvm_side_condition_event) -> None:
        """Initialize a new instance of the LLVMSideConditionEventEnter class.

        Args:
            side_condition_event (llvm_side_condition_event): The LLVM side condition event object.
        """
        self._side_condition_event = side_condition_event

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMSideConditionEventEnter object using the AST printing method.
        """
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
    """Represents an LLVM side condition event indicating the exit of a side condition.

    This event contains the result of the side condition evaluation.

    Attributes:
        _side_condition_end_event (llvm_side_condition_end_event): The underlying side condition end event.
    """

    _side_condition_end_event: llvm_side_condition_end_event

    def __init__(self, side_condition_end_event: llvm_side_condition_end_event) -> None:
        """Initialize a new instance of the LLVMSideConditionEventExit class.

        Args:
            side_condition_end_event (llvm_side_condition_end_event): The LLVM side condition end event object.
        """
        self._side_condition_end_event = side_condition_end_event

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMSideConditionEventExit object using the AST printing method.
        """
        return self._side_condition_end_event.__repr__()

    @property
    def rule_ordinal(self) -> int:
        """Return the axiom ordinal number associated with the side condition event."""
        return self._side_condition_end_event.rule_ordinal

    @property
    def check_result(self) -> bool:
        """Return the boolean result of the evaluation of the side condition that corresponds to this event."""
        return self._side_condition_end_event.check_result


@final
class LLVMFunctionEvent(LLVMStepEvent):
    """Represent an LLVM function event in a proof trace.

    Attributes:
        _function_event (llvm_function_event): The underlying LLVM function event object.
    """

    _function_event: llvm_function_event

    def __init__(self, function_event: llvm_function_event) -> None:
        """Initialize a new instance of the LLVMFunctionEvent class.

        Args:
            function_event (llvm_function_event): The LLVM function event object.
        """
        self._function_event = function_event

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMFunctionEvent object using the AST printing method.
        """
        return self._function_event.__repr__()

    @property
    def name(self) -> str:
        """Return the name of the LLVM function as a KORE Symbol Name."""
        return self._function_event.name

    @property
    def relative_position(self) -> str:
        """Return the relative position of the LLVM function event in the proof trace."""
        return self._function_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        """Return a list of LLVMArgument objects representing the arguments of the LLVM function."""
        return [LLVMArgument(arg) for arg in self._function_event.args]


@final
class LLVMHookEvent(LLVMStepEvent):
    """Represents a hook event in LLVM execution.

    Attributes:
        _hook_event (llvm_hook_event): The underlying hook event object.
    """

    _hook_event: llvm_hook_event

    def __init__(self, hook_event: llvm_hook_event) -> None:
        """Initialize a new instance of the LLVMHookEvent class.

        Args:
            hook_event (llvm_hook_event): The LLVM hook event object.
        """
        self._hook_event = hook_event

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMHookEvent object using the AST printing method.
        """
        return self._hook_event.__repr__()

    @property
    def name(self) -> str:
        """Return the attribute name of the hook event. Ex.: "INT.add"."""
        return self._hook_event.name

    @property
    def relative_position(self) -> str:
        """Return the relative position of the hook event in the proof trace."""
        return self._hook_event.relative_position

    @property
    def args(self) -> list[LLVMArgument]:
        """Return a list of LLVMArgument objects representing the arguments of the hook event."""
        return [LLVMArgument(arg) for arg in self._hook_event.args]

    @property
    def result(self) -> Pattern:
        """Return the result pattern of the hook event evaluation."""
        return self._hook_event.result


@final
class LLVMArgument:
    """Represents an LLVM argument.

    Attributes:
        _argument (Argument): The underlying Argument object. An argument is a wrapper object containing either a step
        event or a KORE pattern.
    """

    _argument: Argument

    def __init__(self, argument: Argument) -> None:
        """Initialize the LLVMArgument object.

        Args:
            argument (Argument): The Argument object.
        """
        self._argument = argument

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            Returns a string representation of the LLVMArgument object using the AST printing method.
        """
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
        """Return the KORE Pattern associated with the argument if any."""
        assert isinstance(self._argument.kore_pattern, Pattern)
        return self._argument.kore_pattern

    def is_kore_pattern(self) -> bool:
        """Check if the argument is a KORE Pattern."""
        return self._argument.is_kore_pattern()

    def is_step_event(self) -> bool:
        """Check if the argument is a step event."""
        return self._argument.is_step_event()


@final
class LLVMRewriteTrace:
    """Represents an LLVM rewrite trace.

    Attributes:
        _rewrite_trace (llvm_rewrite_trace): The underlying LLVM rewrite trace object.
    """

    _rewrite_trace: llvm_rewrite_trace

    def __init__(self, rewrite_trace: llvm_rewrite_trace) -> None:
        """Initialize a new instance of the LLVMRewriteTrace class.

        Args:
            rewrite_trace (llvm_rewrite_trace): The LLVM rewrite trace object.
        """
        self._rewrite_trace = rewrite_trace

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMRewriteTrace object using the AST printing method.
        """
        return self._rewrite_trace.__repr__()

    @property
    def version(self) -> int:
        """Returns the version of the binary hints format used by this trace."""
        return self._rewrite_trace.version

    @property
    def pre_trace(self) -> list[LLVMArgument]:
        """Returns a list of events that occurred before the initial configuration was constructed."""
        return [LLVMArgument(event) for event in self._rewrite_trace.pre_trace]

    @property
    def initial_config(self) -> LLVMArgument:
        """Returns the initial configuration as an LLVMArgument object."""
        return LLVMArgument(self._rewrite_trace.initial_config)

    @property
    def trace(self) -> list[LLVMArgument]:
        """Returns the trace.

        The trace is the list of events that occurred after the initial configurarion was constructed until the end of the
        proof trace when the final configuration is reached.
        """
        return [LLVMArgument(event) for event in self._rewrite_trace.trace]

    @staticmethod
    def parse(trace: bytes, header: KoreHeader) -> LLVMRewriteTrace:
        """Parse the given proof hints byte string using the given kore_header object."""
        return LLVMRewriteTrace(llvm_rewrite_trace.parse(trace, header._kore_header))


class KoreHeader:
    """Represents the Kore header.

    The Kore header is a file that contains the version of the Binary KORE used to serialize/deserialize the
    Proof Trace and all the aditional information needed make this process faster the Proof Trace.

    Attributes:
        _kore_header (kore_header): The underlying KORE Header object.
    """

    _kore_header: kore_header

    def __init__(self, kore_header: kore_header) -> None:
        """Initialize a new instance of the KoreHeader class.

        Args:
            kore_header (kore_header): The KORE Header object.
        """
        self._kore_header = kore_header

    @staticmethod
    def create(header_path: Path) -> KoreHeader:
        """Create a new KoreHeader object from the given header file path."""
        return KoreHeader(kore_header(str(header_path)))


class LLVMEventType:
    """Represents an LLVM event type.

    This works as a wrapper around the EventType enum.
    It also provides properties to check the type of the event.

    Attributes:
        _event_type (EventType): The underlying EventType object.
    """

    _event_type: EventType

    def __init__(self, event_type: EventType) -> None:
        """Initialize a new instance of the LLVMEventType class.

        Args:
            event_type (EventType): The EventType object.
        """
        self._event_type = event_type

    @property
    def is_pre_trace(self) -> bool:
        """Checks if the event type is a pre-trace event."""
        return self._event_type == EventType.PreTrace

    @property
    def is_initial_config(self) -> bool:
        """Checks if the event type is an initial configuration event."""
        return self._event_type == EventType.InitialConfig

    @property
    def is_trace(self) -> bool:
        """Checks if the event type is a trace event."""
        return self._event_type == EventType.Trace


class LLVMEventAnnotated:
    """Represents an annotated LLVM event.

    This class is used to wrap an llvm_event and its corresponding event type.
    This class is used to iterate over the LLVM rewrite trace events.

    Attributes:
        _annotated_llvm_event (annotated_llvm_event): The underlying annotated LLVM event object.
    """

    _annotated_llvm_event: annotated_llvm_event

    def __init__(self, annotated_llvm_event: annotated_llvm_event) -> None:
        """Initialize a new instance of the LLVMEventAnnotated class.

        Args:
            annotated_llvm_event (annotated_llvm_event): The annotated LLVM event object.
        """
        self._annotated_llvm_event = annotated_llvm_event

    @property
    def type(self) -> LLVMEventType:
        """Returns the LLVM event type."""
        return LLVMEventType(self._annotated_llvm_event.type)

    @property
    def event(self) -> LLVMArgument:
        """Returns the LLVM event as an LLVMArgument object."""
        return LLVMArgument(self._annotated_llvm_event.event)


class LLVMRewriteTraceIterator:
    """Represents an LLVM rewrite trace iterator.

    This class is used to iterate over the LLVM rewrite trace events in the stream parser.

    Attributes:
        _rewrite_trace_iterator (llvm_rewrite_trace_iterator): The underlying LLVM rewrite trace iterator object.
    """

    _rewrite_trace_iterator: llvm_rewrite_trace_iterator

    def __init__(self, rewrite_trace_iterator: llvm_rewrite_trace_iterator) -> None:
        """Initialize a new instance of the LLVMRewriteTraceIterator class.

        Args:
            rewrite_trace_iterator (llvm_rewrite_trace_iterator): The LLVM rewrite trace iterator object.
        """
        self._rewrite_trace_iterator = rewrite_trace_iterator

    def __repr__(self) -> str:
        """Return a string representation of the object.

        Returns:
            A string representation of the LLVMRewriteTraceIterator object using the AST printing method.
        """
        return self._rewrite_trace_iterator.__repr__()

    def __iter__(self) -> Generator[LLVMEventAnnotated, None, None]:
        """Yield LLVMEventAnnotated options.

        This method is an iterator that yields LLVMEventAnnotated options.
        It iterates over the events in the trace and returns the next event as an LLVMEventAnnotated object.

        Yields:
            LLVMEventAnnotated: The next LLVMEventAnnotated option.
        """
        while True:
            next_event = self._rewrite_trace_iterator.get_next_event()
            if next_event is None:
                return
            else:
                yield LLVMEventAnnotated(next_event)

    def __next__(self) -> LLVMEventAnnotated:
        """Yield the next LLVMEventAnnotated object from the iterator.

        Returns:
            LLVMEventAnnotated: The next LLVMEventAnnotated object.

        Raises:
            StopIteration: If there are no more events in the iterator.
        """
        next_event = self._rewrite_trace_iterator.get_next_event()
        if next_event is not None:
            return LLVMEventAnnotated(next_event)
        else:
            raise StopIteration

    @property
    def version(self) -> int:
        """Return the version of the HINTS format."""
        return self._rewrite_trace_iterator.version

    @staticmethod
    def from_file(trace_path: Path, header: KoreHeader) -> LLVMRewriteTraceIterator:
        """Create a new LLVMRewriteTraceIterator object from the given trace and header file paths."""
        return LLVMRewriteTraceIterator(llvm_rewrite_trace_iterator.from_file(str(trace_path), header._kore_header))
