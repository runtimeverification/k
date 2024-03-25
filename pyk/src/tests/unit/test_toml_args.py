from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.cli.pyk import create_argument_parser, parse_toml_args

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

TEST_TOML: Final = TEST_DATA_DIR / 'pyk_toml_test.toml'


def test_continue_when_default_toml_absent() -> None:
    parser = create_argument_parser()
    cmd_args = ['coverage', '.', str(TEST_TOML)]
    args = parser.parse_args(cmd_args)
    assert hasattr(args, 'config_file')
    assert str(args.config_file) == 'pyk.toml'
    assert hasattr(args, 'config_profile')
    assert str(args.config_profile) == 'default'
    args_dict = parse_toml_args(args)
    assert len(args_dict) == 0


def test_toml_read() -> None:
    parser = create_argument_parser()
    cmd_args = ['coverage', '--config-file', str(TEST_TOML), '.', str(TEST_TOML), '--verbose']
    args = parser.parse_args(cmd_args)
    args_dict = parse_toml_args(args)
    assert 'output' in args_dict
    assert args_dict['output'] == 'default-file'
    assert hasattr(args, 'verbose')
    assert args.verbose


def test_toml_profiles() -> None:
    parser = create_argument_parser()
    cmd_args = ['coverage', '--config-file', str(TEST_TOML), '--config-profile', 'a_profile', '.', str(TEST_TOML)]
    args = parser.parse_args(cmd_args)
    args_dict = parse_toml_args(args)
    assert 'verbose' in args_dict
    assert args_dict['verbose']
    assert 'output' in args_dict
    assert args_dict['output'] == 'a-profile-file'
