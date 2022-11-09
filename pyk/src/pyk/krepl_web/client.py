from typing import Any, Dict, Final, Optional

from gql import Client, gql
from gql.transport.requests import RequestsHTTPTransport

from pyk.utils import filter_none

DEFAULT_PORT: Final = 42412


class KReplClient:
    _client: Client

    def __init__(self, host: str, port: int):
        transport = RequestsHTTPTransport(
            url=f'http://{host}:{port}/',
            verify=True,
        )

        self._client = Client(transport=transport, fetch_schema_from_transport=True)

    def hello(self, name: Optional[str] = None) -> Dict[str, Any]:
        return self._client.execute(QUERY_HELLO, variable_values=filter_none({'name': name}))


QUERY_HELLO: Final = gql(
    """
    query Hello($name: String) {
        hello(name: $name)
    }
    """
)
