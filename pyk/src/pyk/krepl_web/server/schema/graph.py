from graphene import Field, List, NonNull, ObjectType, String
from graphene.types import JSONString, Scalar


class Term(ObjectType):
    pretty = NonNull(String, cells=List(NonNull(String)))
    kast = NonNull(String)
    kast_json = NonNull(JSONString)
    kore = NonNull(String)
    kore_json = NonNull(JSONString)


class SubstItem(ObjectType):
    var = NonNull(String)
    term = NonNull(Term)


class Subst(ObjectType):
    items = NonNull(List(NonNull(SubstItem)))


class NodeID(Scalar):
    ...


class Node(ObjectType):
    id = NonNull(NodeID)
    term = NonNull(Term)
    in_edge = Field(lambda: Edge)
    out_edges = NonNull(List(NonNull(lambda: Edge)))
    tags = NonNull(List(NonNull(String)))


class EdgeID(Scalar):
    ...


class Edge(ObjectType):
    id = NonNull(EdgeID)
    source = NonNull(Node)
    target = NonNull(Node)
    condition = NonNull(Term)
    substitution = NonNull(Subst)
    tags = NonNull(List(NonNull(String)))


class Graph(ObjectType):
    init = NonNull(Node)
    node = Field(Node, id=NonNull(NodeID))
    nodes = NonNull(List(NonNull(Node)), tagged=String())
    edge = Field(Edge, id=NonNull(EdgeID))
    edges = NonNull(List(NonNull(Edge)), tagged=String())
    tags = NonNull(List(NonNull(String)))
    dot = NonNull(String)
    tree = NonNull(String)
