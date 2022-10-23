from contextlib import closing
from socket import AF_INET, SO_REUSEADDR, SOCK_STREAM, SOL_SOCKET, socket
from time import sleep


# Based on: https://stackoverflow.com/a/45690594
# Note: has an obvious race condition, use only for testing
def free_port_on_host(host: str = 'localhost') -> int:
    with closing(socket(AF_INET, SOCK_STREAM)) as sock:
        sock.bind((host, 0))
        sock.setsockopt(SOL_SOCKET, SO_REUSEADDR, 1)
        _, port = sock.getsockname()
    return port


def port_is_open(port: int) -> bool:
    sock = socket(AF_INET, SOCK_STREAM)
    try:
        sock.connect(('localhost', port))
    except BaseException:
        return False
    else:
        return True
    finally:
        sock.close()


def wait_for_port(port: int) -> None:
    while not port_is_open(port):
        sleep(0.1)
