from pyk.krepl_web.client import KReplClient


def test_hello(krepl_client: KReplClient) -> None:
    # When
    response = krepl_client.hello('Joe')

    # Then
    assert response == {'hello': 'Hello Joe!'}
