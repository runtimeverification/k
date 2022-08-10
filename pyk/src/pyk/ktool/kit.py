import json
import logging
import sys
from argparse import ArgumentParser, FileType
from pathlib import Path
from typing import Any, Dict, Final, List, Optional, Tuple

from ..cfg_manager import CFGManager
from ..cterm import CTerm
from ..kast import (
    KApply,
    KDefinition,
    KFlatModuleList,
    KInner,
    KRewrite,
    KToken,
    KVariable,
)
from ..kastManip import (
    abstract_term_safely,
    bottom_up,
    extract_lhs,
    extract_rhs,
    flatten_label,
    getCell,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    splitConfigFrom,
)
from ..kcfg import KCFG
from ..ktool import KProve
from ..ktool.kprint import KPrint
from ..prelude import Sorts, mlEqualsTrue, mlOr, mlTop
from ..utils import add_indent, shorten_hashes

_LOGGER: Final = logging.getLogger(__name__)


def parse_spec_to_json(kprove: KProve, *, spec_file: Path, out: Path, spec_module: Optional[str]) -> None:
    kprove_args = ['--emit-json-spec', str(out)]
    if spec_module:
        kprove_args += ['--spec-module', spec_module]
    _LOGGER.info(f'Parsing: {spec_file} => {out}')
    kprove.prove(spec_file, args=kprove_args, dry_run=True)


class KIT:
    @staticmethod
    def arg_list_of(elem_type, delim=';'):
        def parse(s):
            return [elem_type(elem) for elem in s.split(delim)]
        return parse

    @staticmethod
    def arg_pair_of(fst_type, snd_type, delim=','):
        def parse(s):
            elems = s.split(delim)
            length = len(elems)
            if length != 2:
                raise ValueError(f'Expected 2 elements, found {length}')
            return fst_type(elems[0]), snd_type(elems[1])
        return parse

    @staticmethod
    def arg_edges():
        return KIT.arg_list_of(KIT.arg_pair_of(str, str))

    def generic_args(self) -> ArgumentParser:
        ret = ArgumentParser(add_help=False)
        ret.add_argument('--cfg-id', type=str, dest='cfg-id', help='CFG identifier to work with.')
        ret.add_argument('--minimize', default=True, action='store_true', help='Minimize output before printing.')
        ret.add_argument('--no-minimize', dest='minimize', action='store_false', help='Do not minimize output before printing.')
        ret.add_argument('-o', '--output', type=FileType('w'), default='-', help='File to write to.')
        return ret

    def create_argument_parser(self) -> ArgumentParser:
        argument_parser = ArgumentParser()
        argument_parser.add_argument('summary-dir', type=str, help='Where to store summarized output.')
        argument_parser.add_argument('-v', '--verbose', action='count', help='Verbosity level, repeat for more verbosity.')
        argument_parser.add_argument('--log-format', type=str, default='%(levelname)s %(asctime)s %(name)s - %(message)s', help='Log format string. See https://docs.python.org/3/library/logging.html#logging.Formatter')
        argument_parser.add_argument('--bug-report', default=False, action='store_true', help='Produce Haskell backend bug reports for each proof run.')

        command_subparsers = argument_parser.add_subparsers(dest='command')
        self.create_subparsers(command_subparsers)
        return argument_parser

    def create_subparsers(self, command_subparsers) -> None:
        self.create_init_subparser(command_subparsers)

        list_cfgs_subparser = command_subparsers.add_parser('list-cfgs', help='List the CFGs in the summary.', parents=[self.generic_args()])
        list_cfgs_subparser.set_defaults(callback_cfg=list_cfgs)

        show_cfg_subparser = command_subparsers.add_parser('show-cfg', help='Show the details of a CFG.', parents=[self.generic_args()])
        show_cfg_subparser.set_defaults(callback_cfg=show_cfg)

        show_edge_subparser = command_subparsers.add_parser('show-edge', help='Show the details of a CFG.', parents=[self.generic_args()])
        show_edge_subparser.set_defaults(callback_cfg=show_edge)
        show_edge_subparser.add_argument('edge', type=KIT.arg_pair_of(str, str), help='"source,target" pair identifying edge to pretty-print.')

        show_node_subparser = command_subparsers.add_parser('show-node', help='Write out pretty version of node.', parents=[self.generic_args()])
        show_node_subparser.set_defaults(callback_cfg=show_node)
        show_node_subparser.add_argument('node', type=str, help='Node to write out state for.')

        add_alias_subparser = command_subparsers.add_parser('add-alias', help='Add alias for a node in a CFG.', parents=[self.generic_args()])
        add_alias_subparser.set_defaults(callback_cfg=add_alias)
        add_alias_subparser.add_argument('name', type=str, help='Name of the alias.')
        add_alias_subparser.add_argument('node', type=str, help='Node id of the for the alias to map to.')

        remove_alias_subparser = command_subparsers.add_parser('remove-alias', help='Add alias for a node in a CFG.', parents=[self.generic_args()])
        remove_alias_subparser.set_defaults(callback_cfg=remove_alias)
        remove_alias_subparser.add_argument('alias', type=str, help='Name of the alias.')

        case_split_subparser = command_subparsers.add_parser('case-split', help='Split the given node on a given boolean condition.', parents=[self.generic_args()])
        case_split_subparser.set_defaults(callback_cfg=case_split)
        case_split_subparser.add_argument('node', type=str, help='Node identifier to perform case-splitting on.')
        case_split_subparser.add_argument('condition', type=str, help='Boolean condition to case split on.')
        case_split_subparser.add_argument('--alias-true', type=str, default=None, help='Alias for true branch.')
        case_split_subparser.add_argument('--alias-false', type=str, default=None, help='Alias for false branch.')

        build_edges_subparser = command_subparsers.add_parser('build-edges', help='Add (unverified) rewrite edges.', parents=[self.generic_args()])
        build_edges_subparser.set_defaults(callback_cfg=build_edges)
        build_edges_subparser.add_argument('edges', type=KIT.arg_edges(), help='Semicolon-separated list of state pairs "start,stop" with existing paths between them to build edges between.')

        verify_edges_subparser = command_subparsers.add_parser('verify-edges', help='Verify generated basic blocks.', parents=[self.generic_args()])
        verify_edges_subparser.set_defaults(callback_cfg=verify_edges)
        verify_edges_subparser.add_argument('--edges', type=KIT.arg_edges(), help='Semicolon-separated list of state pairs "start,stop" to verify edges between (defaults to all edges).')
        verify_edges_subparser.add_argument('--exclude-edges', type=KIT.arg_edges(), default=[], help='Semicolon-separated list of state pairs "start,stop" to exclude from verification.')
        verify_edges_subparser.add_argument('--min-depth', type=int, default=0, help='Minimum number K steps to take in exploration.')

    def create_init_subparser(self, command_subparsers) -> None:
        init_subparser = command_subparsers.add_parser('init', help='Initialize a summary.')
        init_subparser.add_argument('summary-name', type=str, help='ID for summary. Used for display purposes.')
        init_subparser.add_argument('spec-file', type=str, help='File with specifications to prove.')
        init_subparser.add_argument('--reparse', default=False, action='store_true', help='Reparse the specification file even if target json file exists.')
        init_subparser.add_argument('--reinit', default=True, action='store_true', help='Reinitialize the CFG.')
        init_subparser.add_argument('--no-reinit', dest='reinit', action='store_false', help='Do not reinitialize the CFG.')


def main() -> None:
    sys.setrecursionlimit(15000000)
    kit = KIT()
    argument_parser = kit.create_argument_parser()
    args = vars(argument_parser.parse_args())
    configure_logger(args)
    summary_dir = Path(args['summary-dir'])

    # INITIALIZATION
    if args['command'] == 'init':
        init(summary_dir, args)
        return

    # CFG READERS
    manager = CFGManager.load(summary_dir)
    if args['command'] == 'list-cfgs':
        list_cfgs(manager)
        return

    kprove = KProve(manager.definition_dir, use_directory=manager.use_directory)
    if args['bug_report']:
        kprove.prover_args.append('--bug-report')
    cfg_id = args['cfg-id'] if args.get('cfg-id') else manager.default_cfg_id()
    del args['cfg-id']

    cfg = manager.readCFG(cfg_id)
    if 'callback_cfg' in args:
        if args['callback_cfg'](manager, kprove, args, cfg_id, cfg):
            manager.writeCFG(cfg_id, cfg)
        return

    assert False, '!!! Should be unreachable. `callback_cfg` not set.'


def configure_logger(args) -> None:
    log_format = args['log_format']

    if not args['verbose']:
        logging.basicConfig(level=logging.WARNING, format=log_format)
    elif args['verbose'] == 1:
        logging.basicConfig(level=logging.INFO, format=log_format)
    elif args['verbose'] > 1:
        logging.basicConfig(level=logging.DEBUG, format=log_format)
    _LOGGER.info(f'Command: {args["command"]}')


def init(summary_dir: Path, args: Dict[str, Any]) -> None:
    spec_file = Path(args['spec-file'])
    summary_name = args['summary-name']
    manager = CFGManager.create(
        summary_name=summary_name,
        summary_dir=summary_dir,
        spec_file=spec_file,
        main_file=None,
        strategy_name='default'
    )

    kompiled_timestamp = manager.definition_dir / 'timestamp'
    json_spec_file = spec_file.with_suffix('.json')

    if not kompiled_timestamp.exists():
        raise ValueError(f'Summary directory must contain K semantics kompiled with `--emit-json` at {str(manager.definition_dir)}')
    kprove = KProve(manager.definition_dir, use_directory=manager.use_directory)

    if not json_spec_file.exists() or args['reparse']:
        parse_spec_to_json(kprove, spec_file=spec_file, out=json_spec_file, spec_module=args.get('spec-module', None))

    if args['reinit']:
        manager._writeCFGs(cfgs_from_spec(manager, kprove.definition, json_spec_file))


def cfgs_from_spec(manager: CFGManager, kdef: KDefinition, json_spec_file: Path) -> Dict[str, KCFG]:
    with open(json_spec_file, 'r') as jsp:
        spec = json.loads(jsp.read())
        module_list = KFlatModuleList.from_dict(spec['term'])
        proof_module = [module for module in module_list.modules if module.name == module_list.mainModule][0]
    _LOGGER.info(f'Initializing: {json_spec_file}')
    return {claim.att['label']: manager.cfg_from_claim(kdef, claim) for claim in proof_module.claims}


def list_cfgs(manager: CFGManager) -> None:
    print('\n'.join(manager.listCFGs()))


def show_cfg(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> None:
    list(map(print, cfg.pretty(kprove)))


def show_node(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> None:
    node = cfg.node(args['node'])
    term = node.cterm.term
    if args['minimize']:
        term = minimize_term(term)
    args['output'].write(kprove.pretty_print(term) + '\n')
    args['output'].flush()
    _LOGGER.info(f'Wrote node: {shorten_hashes((node.id))}')


def show_edge(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> None:
    (source, target) = args['edge']
    edges = cfg.edge_likes(source_id=source, target_id=target)

    if edges:
        edge = edges[0]
        print(cfg.node_short_info(edge.source))
        list(map(print, add_indent('│ ', edge.pretty(kprove))))
        print(cfg.node_short_info(edge.target))
        print()
    else:
        raise ValueError(f'Could not find edge: {source},{target}')


def add_alias(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> bool:
    cfg.add_alias(args['name'], args['node'])
    return True


def remove_alias(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> bool:
    cfg.remove_alias(args['alias'])
    return True


def case_split(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> bool:
    node_id = args['node']
    condition = kprove.parse_token(KToken(args['condition'], 'Bool'))
    true_node_id, false_node_id = cfg.create_case_split(node_id, [mlEqualsTrue(condition), mlEqualsTrue(KApply('notBool', [condition]))])
    if args['alias_true']:
        cfg.add_alias(args['alias_true'], true_node_id)
    if args['alias_false']:
        cfg.add_alias(args['alias_false'], false_node_id)
    _LOGGER.info(f'Case split: {node_id} on predicate {kprove.pretty_print(condition)} to make {shorten_hashes((true_node_id, false_node_id))}\n')
    return True


def build_edges(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> bool:
    for source_id, target_id in args['edges']:
        if not cfg.is_frontier(source_id):
            raise ValueError(f'Not a frontier node: {source_id}.')
        cfg.create_edge(source_id, target_id, mlTop(), -1)
        cfg.add_expanded(source_id)
    return True


def check_implication(kprint: KPrint, concrete: CTerm, abstract: CTerm) -> Tuple[bool, str]:

    def _no_cell_rewrite_to_dots(term: KInner) -> KInner:
        def _no_cell_rewrite_to_dots(_term: KInner):
            if type(_term) is KApply and _term.is_cell:
                lhs = extract_lhs(_term)
                rhs = extract_rhs(_term)
                if lhs == rhs:
                    return KApply(_term.label, [abstract_term_safely(lhs, base_name=_term.label.name)])
            return _term
        return bottom_up(_no_cell_rewrite_to_dots, term)

    def _is_cell_subst(csubst: KInner) -> bool:
        if type(csubst) is KApply and csubst.label.name == '_==K_':
            csubst_arg = csubst.args[0]
            if type(csubst_arg) is KVariable and csubst_arg.name.endswith('_CELL'):
                return True
        return False

    def _is_negative_cell_subst(constraint: KInner) -> bool:
        constraint_bool = ml_pred_to_bool(constraint)
        if type(constraint_bool) is KApply and constraint_bool.label.name == 'notBool_':
            negative_constraint = constraint_bool.args[0]
            if type(negative_constraint) is KApply and negative_constraint.label.name == '_andBool_':
                constraints = flatten_label('_andBool_', negative_constraint)
                cell_constraints = list(filter(_is_cell_subst, constraints))
                if len(cell_constraints) > 0:
                    return True
        return False

    concrete_config, *concrete_constraints = concrete
    abstract_config, *abstract_constraints = abstract
    config_match = abstract_config.match(concrete_config)
    if config_match is None:
        _, concrete_subst = splitConfigFrom(concrete_config)
        cell_names = concrete_subst.keys()
        failing_cells = []
        for cell in cell_names:
            concrete_cell = getCell(concrete_config, cell)
            abstract_cell = getCell(abstract_config, cell)
            cell_match = abstract_cell.match(concrete_cell)
            if cell_match is None:
                failing_cell = push_down_rewrites(KRewrite(concrete_cell, abstract_cell))
                failing_cell = _no_cell_rewrite_to_dots(failing_cell)
                failing_cells.append((cell, failing_cell))
            else:
                abstract_config = cell_match.apply(abstract_config)
        failing_cells_str = '\n'.join(f'{cell}: {kprint.pretty_print(minimize_term(rew))}' for cell, rew in failing_cells)
        return (False, f'Structural matching failed, the following cells failed individually (abstract => concrete):\n{failing_cells_str}')
    else:
        abstract_constraints = [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]
        abstract_constraints = list(filter(lambda x: not CTerm._is_spurious_constraint(x), [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]))
        impl = CTerm._ml_impl(concrete_constraints, abstract_constraints)
        if impl != mlTop(Sorts.GENERATED_TOP_CELL):
            fail_str = kprint.pretty_print(impl)
            negative_cell_constraints = list(filter(_is_negative_cell_subst, concrete_constraints))
            if len(negative_cell_constraints) > 0:
                fail_str = f'{fail_str}\n\nNegated cell substitutions found (consider using _ => ?_):\n' + '\n'.join([kprint.pretty_print(cc) for cc in negative_cell_constraints])
            return (False, f'Implication check failed, the following is the remaining implication:\n{fail_str}')
    return (True, '')


def verify_edges(manager: CFGManager, kprove: KProve, args, cfg_id: str, cfg: KCFG) -> None:

    def _edge_prove(edge: KCFG.Edge, min_depth: Optional[int]) -> List[KInner]:
        claim_id = f'BASIC-BLOCK-{edge.source.id}-TO-{edge.target.id}'
        haskell_args = []
        if min_depth is not None:
            haskell_args += ['--min-depth', str(min_depth)]
        elif edge.depth > 0:
            haskell_args += ['--min-depth', str(edge.depth)]
        return kprove.prove_cterm(claim_id, edge.pre(), edge.post(), haskell_args=haskell_args)

    edges: List[KCFG.Edge] = []
    if args.get('edges'):
        edges = [edge for (source_id, target_id) in args['edges'] for edge in cfg.edges(source_id=source_id, target_id=target_id)]
    else:
        edges = [edge for edge in cfg.edges()]
    edges = [edge for edge in edges if shorten_hashes((edge.source.id, edge.target.id)) not in args['exclude_edges']]
    edges = [edge for edge in edges if edge.depth != 0 and not cfg.is_verified(edge.source.id, edge.target.id)]
    if len(edges) == 0:
        raise ValueError('Could not find any non-zero-step edges!')

    failed: List[KCFG.Edge] = []

    for edge in edges:
        _LOGGER.info(f'Verifying edge: {shorten_hashes((edge.source.id, edge.target.id))}')
        basic_block_id = f'BASIC-BLOCK-{edge.source.id}-TO-{edge.target.id}'
        proven_states = _edge_prove(edge, min_depth=args.get('min_depth'))
        if len(proven_states) == 1 and proven_states[0] == mlTop():
            cfg.add_verified(edge.source.id, edge.target.id)
            manager.writeCFG(cfg_id, cfg)
            _LOGGER.info(f'Verified claim: {basic_block_id}')
        else:
            errs = [check_implication(kprove, CTerm(ps), edge.target.cterm) for ps in proven_states]
            failed.append(edge)
            proven_state = mlOr(proven_states)
            proven_state = minimize_term(proven_state) if args['minimize'] else proven_state
            prover_output = kprove.pretty_print(proven_state)
            minimized_error_output = '\n==\n'.join([err if not success else 'No minimized output.' for (success, err) in errs])
            _LOGGER.warning(f'Could not verify claim: {basic_block_id}\n\nProver output:\n\n{prover_output}\n\nMinimized output:\n\n{minimized_error_output}')

    if failed:
        edge_strs = [(edge.source.id, edge.target.id) for edge in failed]
        raise ValueError(f'Failed to verify {len(failed)} edges: {shorten_hashes(edge_strs)}!')
