from typing import Any, Final

from graphene import List, NonNull, ObjectType, Schema, String

from .graph import Graph, NodeID
from .mutations import CaseSplit, Load, LoadRaw, Rewind, Step, UpdateCell
from .process import Process, ProcessID, ProcessStatus


class Query(ObjectType):
    hello = String(name=String(default_value='stranger'))
    graph = NonNull(Graph)
    processes = NonNull(List(NonNull(Process), id=ProcessID(), status=ProcessStatus()))
    wait = NonNull(Process, id=NonNull(ProcessID))
    diff = NonNull(String, _from=NonNull(NodeID, name='from'), to=NonNull(NodeID))

    @staticmethod
    def resolve_hello(root: Any, info: Any, name: str) -> str:
        return f'Hello {name}!'


class Mutation(ObjectType):
    load = Load.Field()
    load_raw = LoadRaw.Field()
    step = Step.Field()
    rewind = Rewind.Field()
    case_split = CaseSplit.Field()
    update_cell = UpdateCell.Field()


SCHEMA: Final = Schema(query=Query, mutation=Mutation)
