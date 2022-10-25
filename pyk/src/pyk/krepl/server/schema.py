from typing import Any, Final

from graphene import ObjectType, Schema, String


class Query(ObjectType):
    hello = String(name=String(default_value='stranger'))

    @staticmethod
    def resolve_hello(root: Any, info: Any, name: str) -> str:
        return f'Hello {name}!'


SCHEMA: Final = Schema(query=Query)
