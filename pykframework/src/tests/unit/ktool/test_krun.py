import copy
from collections import OrderedDict
from pathlib import Path
from typing import Any

import pytest

from pykframework.ktool.krun import KRunOutput, _build_arg_list

required_args: dict[str, Any] = OrderedDict(
    [
        ('command', 'krun'),
        ('input_file', None),
        ('definition_dir', None),
        ('output', None),
        ('parser', None),
        ('depth', None),
        ('pmap', None),
        ('cmap', None),
        ('term', False),
        ('temp_dir', None),
        ('no_expand_macros', False),
        ('search_final', False),
        ('no_pattern', False),
        ('debugger', False),
    ]
)

optional_args: dict[str, tuple[Any, list[str]]] = {
    'input_file': (Path('input/path'), ['input/path']),
    'definition_dir': (Path('def/path'), ['--definition', 'def/path']),
    'output': (KRunOutput.JSON, ['--output', 'json']),
    'parser': ('cat', ['--parser', 'cat']),
    'depth': (1234, ['--depth', '1234']),
    'pmap': ({'FOO': 'bar', 'BUZZ': 'kill'}, ['-pFOO=bar', '-pBUZZ=kill']),
    'cmap': ({'COO': 'car', 'FUZZ': 'bill'}, ['-cCOO=car', '-cFUZZ=bill']),
    'term': (True, ['--term']),
    'temp_dir': (Path('/tmp/path'), ['--temp-dir', '/tmp/path']),
    'no_expand_macros': (True, ['--no-expand-macros']),
    'search_final': (True, ['--search-final']),
    'no_pattern': (True, ['--no-pattern']),
    'debugger': (True, ['--debugger']),
}


def make_kwargs(test_id: str, keys: list[str]) -> tuple[str, dict[str, Any], list[str]]:
    ret_kwargs = copy.deepcopy(required_args)
    ret_expected = ['krun']
    for key in keys:
        arg_param, arg_expected = optional_args[key]
        ret_kwargs[key] = arg_param
        ret_expected += arg_expected
    return (test_id, ret_kwargs, ret_expected)


test_data: tuple[tuple[str, list[str]], ...] = (
    ('optional-only', []),
    ('all-args', [key for key in required_args.keys() if key != 'command']),
    *((key, [key]) for key in required_args.keys() if key != 'command'),  # All optional arguments passed alone
)


@pytest.mark.parametrize('params', test_data, ids=[x[0] for x in test_data])
def test_build_arg_list(params: tuple[str, list[str]]) -> None:
    test_id, kwargs, expected = make_kwargs(*params)
    print(kwargs)
    actual = _build_arg_list(**kwargs)
    assert actual == expected
