from graphene import Boolean, Field, InputObjectType, Int, List, Mutation, NonNull, ObjectType, String

from .common import BoolTermString, TermString
from .graph import Edge, Graph, Node, NodeID
from .process import Process


class LoadParam(InputObjectType):
    name = NonNull(String)
    program = NonNull(TermString)


class LoadInput(InputObjectType):
    program = NonNull(TermString)
    params = List(NonNull(LoadParam))


class Load(Mutation):
    class Arguments:
        input = NonNull(LoadInput)

    Output = NonNull(Graph)

    @staticmethod
    def mutate(root, info, input):  # type: ignore  # TODO add type hints
        ...


class LoadRawInput(InputObjectType):
    kore = NonNull(String)


class LoadRaw(Mutation):
    class Arguments:
        input = NonNull(LoadRawInput)

    Output = NonNull(Graph)

    @staticmethod
    def mutate(root, info, input):  # type: ignore  # TODO add type hints
        ...


class StepInput(InputObjectType):
    id = NonNull(NodeID)
    branch = NonNull(Boolean)
    depth = Int()


class StepResult(ObjectType):
    graph = NonNull(Graph)
    new_nodes = NonNull(List(NonNull(Node)))
    new_edges = NonNull(List(NonNull(Edge)))


class StepProcess(ObjectType):
    class Meta:
        interfaces = (Process,)

    result = Field(StepResult)


class Step(Mutation):
    class Arguments:
        input = NonNull(StepInput)
        wait = Boolean(default_value=False)

    Output = NonNull(StepProcess)

    @staticmethod
    def mutate(root, info, input, wait):  # type: ignore  # TODO add type hints
        ...


class RewindResult(ObjectType):
    graph = NonNull(Graph)
    new_node = NonNull(Node)
    new_edges = NonNull(List(NonNull(Edge)))
    removed_edges = NonNull(List(NonNull(Edge)))


class RewindProcess(ObjectType):
    class Meta:
        interfaces = (Process,)

    result = Field(RewindResult)


class RewindInput(InputObjectType):
    id = NonNull(NodeID)
    depth = Int()


class Rewind(Mutation):
    class Arguments:
        input = NonNull(RewindInput)
        wait = Boolean(default_value=False)

    Output = NonNull(RewindProcess)

    @staticmethod
    def mutate(root, info, input, wait):  # type: ignore  # TODO add type hints
        ...


class CaseSplitInput(InputObjectType):
    id = NonNull(NodeID)
    condition = NonNull(BoolTermString)


class CaseSplitResult(ObjectType):
    graph = NonNull(Graph)
    positive_node = NonNull(Node)
    negative_node = NonNull(Node)


class CaseSplit(Mutation):
    class Arguments:
        input = NonNull(CaseSplitInput)

    Output = NonNull(CaseSplitResult)

    @staticmethod
    def mutate(root, info, input):  # type: ignore  # TODO add type hints
        ...


class UpdateCellInput(InputObjectType):
    id = NonNull(NodeID)
    cell = NonNull(String)
    value = NonNull(TermString)


class UpdateCell(Mutation):
    class Arguments:
        input = NonNull(UpdateCellInput)

    Output = NonNull(Node)

    @staticmethod
    def mutate(root, info, input):  # type: ignore  # TODO add type hints
        ...
