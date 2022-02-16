import json
from argparse import ArgumentParser
from os.path import relpath
from pathlib import Path
from typing import Any, Callable, List, Optional, TypeVar

from pyk.cli_utils import check_dir_path, check_file_path, dir_path, file_path
from pyk.kast import EMPTY_ATT, KClaim, KFlatModule
from pyk.kastManip import remove_generated_cells
from pyk.kcfg import KCFG
from pyk.ktool import KompileBackend, kompile, kprove
from pyk.utils import nonempty_str

from .prover import CfgProver, cterms_from_rule

T = TypeVar('T')


def main():
    argument_parser = create_argument_parser()
    args = argument_parser.parse_args()

    command = args.command
    if command == 'init':
        init(args)
    elif command == 'expand':
        expand(args)
    elif command == 'cover':
        cover(args)
    elif command == 'dot':
        dot(args)
    elif command == 'nodes':
        nodes(args)
    elif command == 'node':
        node(args)
    else:
        assert False


def create_argument_parser() -> ArgumentParser:
    argument_parser = ArgumentParser(prog='kit')
    argument_parser.add_argument('-w', '--workdir', metavar='WORKDIR', dest='work_dir', type=Path, default=Path('.'), help='Working directory.')
    command_subparsers = argument_parser.add_subparsers(dest='command', required=True)

    init_subparser = command_subparsers.add_parser('init', help='Initialize prover.')
    init_subparser.add_argument('main_file', type=file_path, help='Path to main definition file.')
    init_subparser.add_argument('spec_file', type=file_path, help='Path to specification file.')
    init_subparser.add_argument('-I', '--include', metavar='INCLUDE', dest='include_dirs', type=dir_path, default=[], action='append', help='Path to directory to include.')
    init_subparser.add_argument('-f', '--force', dest='force', default=False, action='store_true', help='Overwrite existing configuration.')

    expand_subparser = command_subparsers.add_parser('expand', help='Expand node.')
    expand_subparser.add_argument('node_id', type=str, help='ID of node to expland.')

    cover_subparser = command_subparsers.add_parser('cover', help='Cover node.')
    cover_subparser.add_argument('node_id', type=str, help='ID of node to cover.')
    cover_subparser.add_argument('-b', '--by', metavar='COVERER_ID', dest='coverer_ids', type=str, default=None, action='append', help='ID of node to attempt covering by.')
    cover_subparser.add_argument('-s', '--semantic', dest='semantic', default=False, action='store_true', help='Check coverage syntactically.')

    dot_subparser = command_subparsers.add_parser('dot', help='Export CFG in dot format.')
    dot_subparser.add_argument('-o', '--output', metavar='OUTPUT', dest='dot_path', type=str, default='-', help='Path to write CFG in dot format to.')

    command_subparsers.add_parser('nodes', help='List nodes of the CFG.')

    node_subparser = command_subparsers.add_parser('node', help='Pretty print CFG node.')
    node_subparser.add_argument('node_id', type=str, help='ID of node to pretty print.')

    return argument_parser


# Commands

def init(args):
    if not args.work_dir.exists():
        raise ValueError(f'Working directory does not exist: {args.work_dir}')

    kit_dir = args.work_dir / '.kit'
    if not args.force and kit_dir.exists():
        raise ValueError(f'Project already exists at: {kit_dir}')

    kit_dir.mkdir(exist_ok=True)

    # Kompile
    kompiled_dir = kit_dir / f'{args.main_file.stem}-kompiled'
    kompile(args.main_file, backend=KompileBackend.HASKELL, output_dir=kompiled_dir, emit_json=True)

    # Emit JSON spec
    json_spec_file = kit_dir / (args.spec_file.stem + '.json')
    kprove(args.spec_file, kompiled_dir=kompiled_dir, emit_json_spec=json_spec_file, dry_run=True)

    # Init CFG
    cfg_file = kit_dir / 'cfg.json'
    claim = _extract_claim_from_spec_file(json_spec_file)
    cfg = _create_cfg_from_claim(claim)

    # Create config
    config_file = kit_dir / 'config.json'
    prover_dir = kit_dir / 'kprove'

    config = {
        'kompiledDir': relpath(kompiled_dir, kit_dir),
        'mainFile': relpath(args.main_file, kit_dir),
        'cfgFile': relpath(cfg_file, kit_dir),
        'proverDir': relpath(prover_dir, kit_dir),
        'includeDirs': [relpath(include_dir, kit_dir) for include_dir in args.include_dirs],
    }

    with open(config_file, 'w') as f:
        f.write(json.dumps(config, indent=4))
        f.write('\n')

    with open(cfg_file, 'w') as f:
        f.write(cfg.to_json())
        f.write('\n')

    prover_dir.mkdir(exist_ok=True)


def expand(args):
    prover = load_prover(args.work_dir / '.kit/config.json')
    child_ids = prover.expand(args.node_id)
    prover.write_cfg(args.work_dir / '.kit/cfg.json')

    if not child_ids:
        print('ok')
        return

    for child_id in child_ids:
        print(child_id)


def cover(args):
    prover = load_prover(args.work_dir / '.kit/config.json')
    cover_res = prover.cover(args.node_id, coverer_ids=args.coverer_ids, semantic=args.semantic)

    if not cover_res:
        print('fail')
        return

    prover.write_cfg(args.work_dir / '.kit/cfg.json')
    coverer_id, subst = cover_res
    print(coverer_id)
    for k, v in subst.minimize().items():
        print(k + ' |-> ' + prover.kprove.pretty_print(v))  # TODO enforce LoD ; Subst.pretty


def dot(args):
    prover = load_prover(args.work_dir / '.kit/config.json')
    content = prover.cfg_dot()
    _write_file_or_stdout(content, args.dot_path)


def nodes(args):
    prover = load_prover(args.work_dir / '.kit/config.json')
    for node in prover.cfg.nodes:
        print(node.id)


def node(args):
    prover = load_prover(args.work_dir / '.kit/config.json')
    node = prover.cfg.node(args.node_id)
    print(prover.kprove.pretty_print(node.cterm.term))


# Helpers

def load_prover(config_file: Path) -> 'CfgProver':
    check_file_path(config_file)

    with open(config_file) as f:
        config = json.load(f)

    def required_prop(name: str, parser: Callable[[Any], T]) -> T:
        value = config.get(name)
        if value is None:
            raise ValueError(f'Property {name} is required.')
        return parser(value)

    def optional_prop(name: str, parser: Callable[[Any], T]) -> Optional[T]:
        value = config.get(name)
        if value is None:
            return None
        return parser(value)

    def make_relative(base: Path, path: Path) -> Path:
        return path if path.is_absolute() else base / path

    def path_rel_to(base: Path) -> Callable[[Any], Path]:
        def parse(x: Any) -> Path:
            path = make_relative(base, Path(nonempty_str(x)))
            return path
        return parse

    def file_path_rel_to(base: Path) -> Callable[[Any], Path]:
        def parse(x: Any) -> Path:
            path = make_relative(base, Path(nonempty_str(x)))
            check_file_path(path)
            return path
        return parse

    def dir_path_rel_to(base: Path) -> Callable[[Any], Path]:
        def parse(x: Any) -> Path:
            path = make_relative(base, Path(nonempty_str(x)))
            check_dir_path(path)
            return path
        return parse

    def list_of(elem_parser: Callable[[Any], T]) -> Callable[[List[Any]], List[T]]:
        return lambda xs: list(map(elem_parser, xs))

    kit_dir = config_file.parent
    kompiled_dir = required_prop('kompiledDir', dir_path_rel_to(kit_dir))
    main_file = required_prop('mainFile', file_path_rel_to(kit_dir))
    cfg_file = required_prop('cfgFile', file_path_rel_to(kit_dir))
    prover_dir = optional_prop('proverDir', path_rel_to(kit_dir))
    include_dirs = optional_prop('includeDirs', list_of(dir_path_rel_to(kit_dir)))
    max_depth = optional_prop('maxDepth', int)

    with open(cfg_file, 'r') as f:
        cfg = KCFG.from_json(f.read())

    return CfgProver(
        cfg=cfg,
        kompiled_dir=kompiled_dir,
        main_file=main_file,
        prover_dir=prover_dir,
        include_dirs=include_dirs,
        max_depth=max_depth,
    )


def _extract_claim_from_spec_file(spec_file: Path) -> KClaim:
    with open(spec_file, 'r') as f:
        spec = json.load(f)

    module = KFlatModule.from_dict(spec['term'])
    claims = [sentence for sentence in module if type(sentence) is KClaim]

    if len(claims) != 1:
        raise ValueError(f'Expected exactly one claim in {str(spec_file)}, found: {len(claims)}')

    claim = claims[0]
    claim = claim.let(body=remove_generated_cells(claim.body), att=EMPTY_ATT)
    return claim


def _create_cfg_from_claim(claim: KClaim) -> KCFG:
    init_cterm, target_cterm = cterms_from_rule(claim)
    cfg = KCFG()
    init = cfg.create_node(init_cterm)
    target = cfg.create_node(target_cterm)
    cfg.add_init(init.id)
    cfg.add_target(target.id)
    return cfg


def _write_file_or_stdout(content: str, path='-') -> None:
    if path == '-':
        print(content)
    else:
        with open(path, 'w') as f:
            f.write(content)


if __name__ == "__main__":
    main()
