from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KInner
from pyk.kast.kast import KAst, kast_term
from pyk.kast.outer import read_kast_definition
from pyk.kast.pretty import PrettyPrinter
from pyk.kllvm.compiler import compile_runtime
from pyk.kllvm.importer import import_runtime
from pyk.konvert import _kast_to_kore, _kore_to_kast
from pyk.kore.parser import KoreParser
from pyk.kore.prelude import SORT_K_ITEM, STRING, generated_counter, generated_top, inj, int_dv, k, kseq, str_dv
from pyk.kore.rpc import KoreClient, KoreServer, StuckResult
from pyk.kore.syntax import App
from pyk.ktool.kprint import _kast
from pyk.ktool.krun import KRun
from pyk.prelude.string import stringToken

from .utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import FixtureRequest

    from pyk.kllvm.runtime import Runtime
    from pyk.kore.syntax import Pattern
    from pyk.testing import Kompiler

TEST_DATA: Final = (
    'hello',
    '\n',
    '\x01',
    '£',
    '𐍈',
    '武天老師',
    '🙂',
)

KOMPILE_MAIN_FILE = K_FILES / 'string-rewrite.k'
KOMPILE_MAIN_MODULE = 'STRING-REWRITE'


@pytest.fixture(scope='module')
def llvm_dir(kompile: Kompiler) -> Path:
    return kompile(
        KOMPILE_MAIN_FILE,
        main_module=KOMPILE_MAIN_MODULE,
        backend='llvm',
    )


@pytest.fixture(scope='module')
def haskell_dir(kompile: Kompiler) -> Path:
    return kompile(
        KOMPILE_MAIN_FILE,
        main_module=KOMPILE_MAIN_MODULE,
        backend='haskell',
    )


@pytest.fixture(scope='module', params=['llvm', 'haskell'])
def backend(request: FixtureRequest) -> str:
    return request.param


@pytest.fixture(scope='module')
def definition_dir(request: FixtureRequest, backend: str) -> Path:
    return request.getfixturevalue(f'{backend}_dir')


@pytest.fixture(scope='module')
def runtime(llvm_dir: Path) -> Runtime:
    import pyk.kllvm.load  # noqa: F401

    compile_runtime(llvm_dir)
    return import_runtime(llvm_dir)


def kore_config(kval: str | None, sval: str) -> Pattern:
    def s(pattern: Pattern) -> App:
        return App("Lbl'-LT-'s'-GT-'", (), (pattern,))

    kitems = (inj(STRING, SORT_K_ITEM, str_dv(kval)),) if kval is not None else ()
    return generated_top(
        (
            k(kseq(kitems)),
            s(str_dv(sval)),
            generated_counter(int_dv(0)),
        )
    )


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_kast_to_kore(text: str) -> None:  # TODO turn into unit test
    # Given
    kast = stringToken(text)

    # When
    kore = _kast_to_kore(kast)

    # Then
    assert kore == str_dv(text)


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_kore_to_kast(text: str) -> None:  # TODO turn into unit test
    # Given
    kore = str_dv(text)

    # When
    kast = _kore_to_kast(kore)

    # Then
    assert kast == stringToken(text)


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_cli_kast_to_kore(llvm_dir: Path, text: str) -> None:
    # Given
    kast = stringToken(text)
    kast_dict = {'format': 'KAST', 'version': KAst.version(), 'term': kast.to_dict()}  # TODO extract function
    kast_json = json.dumps(kast_dict)

    # When
    proc_res = _kast(
        definition_dir=llvm_dir,
        expression=kast_json,
        input='json',
        output='kore',
    )
    kore_text = proc_res.stdout
    kore = KoreParser(kore_text).dv()

    # Then
    assert kore == str_dv(text)


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_cli_kore_to_kast(llvm_dir: Path, text: str) -> None:
    # Given
    kore = str_dv(text)
    kore_text = kore.text

    # When
    proc_res = _kast(
        definition_dir=llvm_dir,
        expression=kore_text,
        input='kore',
        output='json',
    )
    kast_json = proc_res.stdout
    kast = KInner.from_dict(kast_term(json.loads(kast_json)))

    # Then
    assert kast == stringToken(text)


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_cli_rule_to_kast(llvm_dir: Path, text: str) -> None:
    # Given
    pretty_printer = PrettyPrinter(read_kast_definition(llvm_dir / 'compiled.json'))
    input_kast = stringToken(text)
    rule_text = pretty_printer.print(input_kast)

    # When
    proc_res = _kast(
        definition_dir=llvm_dir,
        expression=rule_text,
        input='rule',
        output='json',
    )
    kast_json = proc_res.stdout
    output_kast = KInner.from_dict(kast_term(json.loads(kast_json)))

    # Then
    assert input_kast == output_kast


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_krun(backend: str, definition_dir: Path, text: str) -> None:
    if backend == 'llvm':
        try:
            text.encode('latin-1')
        except ValueError:
            # https://github.com/runtimeverification/k/issues/3344
            pytest.skip()

    # Given
    kore = kore_config(text, '')
    expected = kore_config(None, text)
    krun = KRun(definition_dir)

    # When
    actual = krun.run_pattern(kore)

    # Then
    assert actual == expected


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_bindings(runtime: Runtime, text: str) -> None:
    from pyk.kllvm.convert import llvm_to_pattern, pattern_to_llvm

    # Given
    kore = kore_config(text, '')
    expected = kore_config(None, text)

    # When
    kore_llvm = runtime.run(pattern_to_llvm(kore))
    actual = llvm_to_pattern(kore_llvm)

    # Then
    assert actual == expected


@pytest.mark.parametrize('text', TEST_DATA, ids=TEST_DATA)
def test_kore_rpc(haskell_dir: Path, text: str) -> None:
    try:
        text.encode('latin-1')
    except ValueError:
        # https://github.com/runtimeverification/pyk/issues/348
        pytest.skip()

    # Given
    kore = kore_config(text, '')
    expected = kore_config(None, text)

    # When
    with KoreServer({'kompiled_dir': haskell_dir, 'module_name': KOMPILE_MAIN_MODULE}) as server:
        with KoreClient('localhost', server.port) as client:
            result = client.execute(kore)

    assert isinstance(result, StuckResult)
    assert result.state.term == expected
