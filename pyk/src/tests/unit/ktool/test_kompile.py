from pathlib import Path

from pyk.ktool.kompile import KompileBackend, LLVMKompileType, _build_arg_list


def test_all_args_1() -> None:
    # Given
    # fmt: off
    expected = [
        'kevm', 'kompile',
        'imp.k',
        '--output-definition', 'path/to/kompiled',
        '--backend', 'haskell',
        '--main-module', 'MAIN-MODULE',
        '--syntax-module', 'SYNTAX-MODULE',
        '-I', '/',
        '-I', '/include/lib',
        '--md-selector', 'k & ! nobytes & ! node',
        '--hook-namespaces', 'JSON KRYPTO BLOCKCHAIN',
        '--emit-json',
        '--post-process', "'echo \"hello\"'",
        '--concrete-rules', 'foo,bar',
    ]
    # fmt: on

    # When
    actual = _build_arg_list(
        command=('kevm', 'kompile'),
        main_file=Path('imp.k'),
        output_dir=Path('path/to/kompiled'),
        backend=KompileBackend.HASKELL,
        main_module='MAIN-MODULE',
        syntax_module='SYNTAX-MODULE',
        include_dirs=(Path(path) for path in ['/', '/include/lib']),
        md_selector='k & ! nobytes & ! node',
        hook_namespaces=['JSON', 'KRYPTO', 'BLOCKCHAIN'],
        emit_json=True,
        gen_bison_parser=False,
        bison_parser_library=False,
        post_process='echo "hello"',
        opt_level=None,
        ccopts=(),
        no_llvm_kompile=False,
        enable_search=False,
        enable_llvm_debug=False,
        llvm_kompile_type=None,
        concrete_rules=['foo', 'bar'],
    )

    # Then
    assert actual == expected


def test_all_args_2() -> None:
    # Given
    # fmt: off
    expected = [
        'kevm', 'kompile',
        'imp.k',
        '--output-definition', 'path/to/kompiled',
        '--backend', 'llvm',
        '--main-module', 'MAIN-MODULE',
        '--syntax-module', 'SYNTAX-MODULE',
        '-I', '/',
        '-I', '/include/lib',
        '--md-selector', 'k & ! nobytes & ! node',
        '--hook-namespaces', 'JSON KRYPTO BLOCKCHAIN',
        '--emit-json',
        '--post-process', "'echo \"hello\"'",
        '--llvm-kompile-type', 'c',
    ]
    # fmt: on

    # When
    actual = _build_arg_list(
        command=('kevm', 'kompile'),
        main_file=Path('imp.k'),
        output_dir=Path('path/to/kompiled'),
        backend=KompileBackend.LLVM,
        main_module='MAIN-MODULE',
        syntax_module='SYNTAX-MODULE',
        include_dirs=(Path(path) for path in ['/', '/include/lib']),
        md_selector='k & ! nobytes & ! node',
        hook_namespaces=['JSON', 'KRYPTO', 'BLOCKCHAIN'],
        emit_json=True,
        gen_bison_parser=False,
        bison_parser_library=False,
        post_process='echo "hello"',
        opt_level=None,
        ccopts=(),
        no_llvm_kompile=False,
        enable_search=False,
        enable_llvm_debug=False,
        llvm_kompile_type=LLVMKompileType.C,
        concrete_rules=(),
    )

    # Then
    assert actual == expected
