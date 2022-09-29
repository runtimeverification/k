import json
import logging
import os
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Any, Callable, Dict, Final, Iterable, Optional

from ..cli_utils import check_dir_path, run_process
from ..kast import (
    KApply,
    KAs,
    KAst,
    KAtt,
    KBubble,
    KClaim,
    KContext,
    KDefinition,
    KFlatModule,
    KImport,
    KInner,
    KNonTerminal,
    KProduction,
    KRegexTerminal,
    KRequire,
    KRewrite,
    KRule,
    KSequence,
    KSort,
    KSortSynonym,
    KSyntaxAssociativity,
    KSyntaxLexical,
    KSyntaxPriority,
    KSyntaxSort,
    KTerminal,
    KToken,
    KVariable,
    read_kast_definition,
)
from ..kastManip import flatten_label
from ..kore.parser import KoreParser
from ..kore.syntax import Kore
from ..prelude.k import DOTS, EMPTY_K
from ..prelude.kbool import TRUE

_LOGGER: Final = logging.getLogger(__name__)

SymbolTable = Dict[str, Callable[..., str]]


def _kast(
    definition: Path,
    expression: str,
    check: bool = True,
    profile: bool = False,
    input: str = 'program',
    output: str = 'json',
    sort: Optional[KSort] = None,
    args: Iterable[str] = (),
) -> str:
    kast_command = ['kast', '--definition', str(definition)]
    kast_command += ['--input', input, '--output', output]
    if sort:
        kast_command += ['--sort', sort.name]
    kast_command += ['--expression', expression]
    command_env = os.environ.copy()
    proc_result = run_process(kast_command, env=command_env, logger=_LOGGER, check=check, profile=profile)
    if proc_result.returncode != 0:
        raise RuntimeError(f'Calling kast failed: {kast_command}')
    return proc_result.stdout


class KPrint:

    definition_dir: Path
    use_directory: Path
    _profile: bool

    _definition: Optional[KDefinition]
    _symbol_table: Optional[SymbolTable]

    def __init__(self, definition_dir: Path, use_directory: Optional[Path] = None, profile: bool = False) -> None:
        self.definition_dir = Path(definition_dir)
        if use_directory:
            self.use_directory = use_directory
        else:
            td = TemporaryDirectory()
            self.use_directory = Path(td.name)
        check_dir_path(self.use_directory)
        self._definition = None
        self._symbol_table = None
        self._profile = profile

    @property
    def definition(self) -> KDefinition:
        if not self._definition:
            self._definition = read_kast_definition(self.definition_dir / 'compiled.json')
        return self._definition

    @property
    def definition_hash(self) -> str:
        return self.definition.hash

    @property
    def symbol_table(self) -> SymbolTable:
        if not self._symbol_table:
            self._symbol_table = build_symbol_table(self.definition, opinionated=True)
        return self._symbol_table

    def parse_token(self, ktoken: KToken, *, as_rule: bool = False) -> KInner:
        input = 'rule' if as_rule else 'program'
        output = _kast(self.definition_dir, ktoken.token, sort=ktoken.sort, input=input, profile=self._profile)
        kast_token = KAst.from_dict(json.loads(output)['term'])
        assert isinstance(kast_token, KInner)
        return kast_token

    def kore_to_kast(self, kore: Kore) -> KAst:
        output = _kast(self.definition_dir, kore.text, input='kore', output='json', profile=self._profile)
        return KAst.from_dict(json.loads(output)['term'])

    def kast_to_kore(self, kast: KAst, sort: Optional[KSort] = None) -> Kore:
        kast_json = {'format': 'KAST', 'version': 2, 'term': kast.to_dict()}
        output = _kast(
            self.definition_dir, json.dumps(kast_json), input='json', output='kore', sort=sort, profile=self._profile
        )
        return KoreParser(output).pattern()

    def pretty_print(self, kast: KAst, debug: bool = False) -> str:
        return pretty_print_kast(kast, self.symbol_table, debug=debug)


def unparser_for_production(prod: KProduction) -> Callable[..., str]:
    def _unparser(*args: Any) -> str:
        index = 0
        result = []
        for item in prod.items:
            if type(item) is KTerminal:
                result.append(item.value)
            elif type(item) is KNonTerminal and index < len(args):
                result.append(args[index])
                index += 1
        return ' '.join(result)

    return _unparser


def build_symbol_table(definition: KDefinition, opinionated: bool = False) -> SymbolTable:
    """Build the unparsing symbol table given a JSON encoded definition.

    -   Input: JSON encoded K definition.
    -   Return: Python dictionary mapping klabels to automatically generated unparsers.
    """
    symbol_table = {}
    for module in definition.modules:
        for prod in module.syntax_productions:
            assert prod.klabel
            label = prod.klabel.name
            unparser = unparser_for_production(prod)

            symbol_table[label] = unparser
            if 'symbol' in prod.att and 'klabel' in prod.att:
                symbol_table[prod.att['klabel']] = unparser

    if opinionated:
        symbol_table['#And'] = lambda c1, c2: c1 + '\n#And ' + c2
        symbol_table['#Or'] = lambda c1, c2: c1 + '\n#Or\n' + indent(c2, size=4)

    return symbol_table


def pretty_print_kast(kast: KAst, symbol_table: SymbolTable, debug: bool = False) -> str:
    """Print out KAST terms/outer syntax.

    -   Input: KAST term.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if type(kast) is KVariable:
        sort = kast.sort
        if not sort:
            return kast.name
        return kast.name + ':' + pretty_print_kast(sort, symbol_table, debug)
    if type(kast) is KSort:
        return kast.name
    if type(kast) is KToken:
        return kast.token
    if type(kast) is KApply:
        label = kast.label.name
        args = kast.args
        unparsed_args = [pretty_print_kast(arg, symbol_table, debug=debug) for arg in args]
        if kast.is_cell:
            cell_contents = '\n'.join(unparsed_args).rstrip()
            cell_str = label + '\n' + indent(cell_contents) + '\n</' + label[1:]
            return cell_str.rstrip()
        unparser = applied_label_str(label) if label not in symbol_table else symbol_table[label]
        return unparser(*unparsed_args)
    if type(kast) is KAs:
        pattern_str = pretty_print_kast(kast.pattern, symbol_table, debug=debug)
        alias_str = pretty_print_kast(kast.alias, symbol_table, debug=debug)
        return pattern_str + ' #as ' + alias_str
    if type(kast) is KRewrite:
        lhs_str = pretty_print_kast(kast.lhs, symbol_table, debug=debug)
        rhs_str = pretty_print_kast(kast.rhs, symbol_table, debug=debug)
        return '( ' + lhs_str + ' => ' + rhs_str + ' )'
    if type(kast) is KSequence:
        if kast.arity == 0:
            return pretty_print_kast(EMPTY_K, symbol_table, debug=debug)
        if kast.arity == 1:
            return pretty_print_kast(kast.items[0], symbol_table, debug=debug)
        unparsed_k_seq = '\n~> '.join([pretty_print_kast(item, symbol_table, debug=debug) for item in kast.items[0:-1]])
        if kast.items[-1] == DOTS:
            unparsed_k_seq = unparsed_k_seq + '\n' + pretty_print_kast(DOTS, symbol_table, debug=debug)
        else:
            unparsed_k_seq = unparsed_k_seq + '\n~> ' + pretty_print_kast(kast.items[-1], symbol_table, debug=debug)
        return unparsed_k_seq
    if type(kast) is KTerminal:
        return '"' + kast.value + '"'
    if type(kast) is KRegexTerminal:
        return 'r"' + kast.regex + '"'
    if type(kast) is KNonTerminal:
        return pretty_print_kast(kast.sort, symbol_table, debug=debug)
    if type(kast) is KProduction:
        if 'klabel' not in kast.att and kast.klabel:
            kast = kast.update_atts({'klabel': kast.klabel.name})
        syntax_str = 'syntax ' + pretty_print_kast(kast.sort, symbol_table, debug=debug)
        if kast.items:
            syntax_str += ' ::= ' + ' '.join([pretty_print_kast(pi, symbol_table, debug=debug) for pi in kast.items])
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        if att_str:
            syntax_str += ' ' + att_str
        return syntax_str
    if type(kast) is KSyntaxSort:
        sort_str = pretty_print_kast(kast.sort, symbol_table, debug=debug)
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        return 'syntax ' + sort_str + ' ' + att_str
    if type(kast) is KSortSynonym:
        new_sort_str = pretty_print_kast(kast.new_sort, symbol_table, debug=debug)
        old_sort_str = pretty_print_kast(kast.old_sort, symbol_table, debug=debug)
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        return 'syntax ' + new_sort_str + ' = ' + old_sort_str + ' ' + att_str
    if type(kast) is KSyntaxLexical:
        name_str = kast.name
        regex_str = kast.regex
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        # todo: proper escaping
        return 'syntax lexical ' + name_str + ' = r"' + regex_str + '" ' + att_str
    if type(kast) is KSyntaxAssociativity:
        assoc_str = kast.assoc.value
        tags_str = ' '.join(kast.tags)
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        return 'syntax associativity ' + assoc_str + ' ' + tags_str + ' ' + att_str
    if type(kast) is KSyntaxPriority:
        priorities_str = ' > '.join([' '.join(group) for group in kast.priorities])
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        return 'syntax priority ' + priorities_str + ' ' + att_str
    if type(kast) is KBubble:
        body = '// KBubble(' + kast.sentence_type + ', ' + kast.content + ')'
        att_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        return body + ' ' + att_str
    if type(kast) is KRule or type(kast) is KClaim:
        body = '\n     '.join(pretty_print_kast(kast.body, symbol_table, debug=debug).split('\n'))
        rule_str = 'rule ' if type(kast) is KRule else 'claim '
        if 'label' in kast.att:
            rule_str = rule_str + '[' + kast.att['label'] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        if kast.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(
                pretty_print_kast_bool(kast.requires, symbol_table, debug=debug).split('\n')
            )
            rule_str = rule_str + '\n  ' + requires_str
        if kast.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(
                pretty_print_kast_bool(kast.ensures, symbol_table, debug=debug).split('\n')
            )
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str
    if type(kast) is KContext:
        body = indent(pretty_print_kast(kast.body, symbol_table, debug=debug))
        context_str = 'context alias ' + body
        requires_str = ''
        atts_str = pretty_print_kast(kast.att, symbol_table, debug=debug)
        if kast.requires != TRUE:
            requires_str = pretty_print_kast(kast.requires, symbol_table, debug=debug)
            requires_str = 'requires ' + indent(requires_str)
        return context_str + '\n  ' + requires_str + '\n  ' + atts_str
    if type(kast) is KAtt:
        if not kast.atts:
            return ''
        att_strs = [k + '(' + v + ')' for k, v in kast.atts.items()]
        return '[' + ', '.join(att_strs) + ']'
    if type(kast) is KImport:
        return ' '.join(['imports', ('public' if kast.public else 'private'), kast.name])
    if type(kast) is KFlatModule:
        name = kast.name
        imports = '\n'.join([pretty_print_kast(kimport, symbol_table, debug=debug) for kimport in kast.imports])
        sentences = '\n\n'.join([pretty_print_kast(sentence, symbol_table, debug=debug) for sentence in kast.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'
    if type(kast) is KRequire:
        return 'requires "' + kast.require + '"'
    if type(kast) is KDefinition:
        requires = '\n'.join([pretty_print_kast(require, symbol_table, debug=debug) for require in kast.requires])
        modules = '\n\n'.join([pretty_print_kast(module, symbol_table, debug=debug) for module in kast.modules])
        return requires + '\n\n' + modules

    raise ValueError(f'Error unparsing: {kast}')


def pretty_print_kast_bool(kast: KAst, symbol_table: SymbolTable, debug: bool = False) -> str:
    """Print out KAST requires/ensures clause.

    -   Input: KAST Bool for requires/ensures clause.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if type(kast) is KApply and kast.label.name in ['_andBool_', '_orBool_']:
        clauses = [pretty_print_kast_bool(c, symbol_table, debug=debug) for c in flatten_label(kast.label.name, kast)]
        head = kast.label.name.replace('_', ' ')
        if head == ' orBool ':
            head = '  orBool '
        separator = ' ' * (len(head) - 7)
        spacer = ' ' * len(head)

        def join_sep(s: str) -> str:
            return ('\n' + separator).join(s.split('\n'))

        clauses = (
            ['( ' + join_sep(clauses[0])]
            + [head + '( ' + join_sep(c) for c in clauses[1:]]
            + [spacer + (')' * len(clauses))]
        )
        return '\n'.join(clauses)
    else:
        return pretty_print_kast(kast, symbol_table, debug=debug)


def paren(printer: Callable[..., str]) -> Callable[..., str]:
    return lambda *args: '( ' + printer(*args) + ' )'


def applied_label_str(symbol: str) -> Callable[..., str]:
    return lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )'


def indent(text: str, size: int = 2) -> str:
    return '\n'.join([(' ' * size) + line for line in text.split('\n')])


def assoc_with_unit(assoc_join: str, unit: str) -> Callable[..., str]:
    def _assoc_with_unit(*args: str) -> str:
        return assoc_join.join(arg for arg in args if arg != unit)

    return _assoc_with_unit
