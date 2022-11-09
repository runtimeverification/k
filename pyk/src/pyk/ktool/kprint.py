import json
import logging
import os
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
    KLabel,
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
from ..kore.syntax import DV, And, App, Equals, EVar, Kore, Pattern, SortApp, String
from ..prelude.k import DOTS, EMPTY_K
from ..prelude.kbool import TRUE

_LOGGER: Final = logging.getLogger(__name__)

SymbolTable = Dict[str, Callable[..., str]]

_unmunge_codes: Dict[str, str] = {
    'Spce': ' ',
    'Bang': '!',
    'Quot': '"',
    'Hash': '#',
    'Dolr': '$',
    'Perc': '%',
    'And-': '&',
    'Apos': "'",
    'LPar': '(',
    'RPar': ')',
    'Star': '*',
    'Plus': '+',
    'Comm': ',',
    'Stop': '.',
    'Slsh': '/',
    'Coln': ':',
    'SCln': ';',
    '-LT-': '<',
    'Eqls': '=',
    '-GT-': '>',
    'Ques': '?',
    '-AT-': '@',
    'LSqB': '[',
    'RSqB': ']',
    'Bash': '\\',
    'Xor-': '^',
    'Unds': '_',
    'BQuo': '`',
    'LBra': '{',
    'Pipe': '|',
    'RBra': '}',
    'Tild': '~',
}
_munge_codes: Dict[str, str] = {v: k for k, v in _unmunge_codes.items()}


def _munge(label: str) -> str:
    global _munge_codes
    _symbol = ''
    literal_mode = True
    while len(label) > 0:
        if label[0] in _munge_codes:
            if not literal_mode:
                _symbol += _munge_codes[label[0]]
                label = label[1:]
            else:
                _symbol += "'"
                literal_mode = False
        else:
            if literal_mode:
                _symbol += label[0]
                label = label[1:]
            else:
                _symbol += "'"
                literal_mode = True
    if not literal_mode:
        _symbol += "'"
    return _symbol


def _unmunge(symbol: str) -> str:
    global _unmunge_codes
    _label = ''
    literal_mode = True
    while len(symbol) > 0:
        if symbol[0] == "'":
            literal_mode = not literal_mode
            symbol = symbol[1:]
        else:
            if literal_mode:
                _label += symbol[0]
                symbol = symbol[1:]
            else:
                _label += _unmunge_codes[symbol[0:4]]
                symbol = symbol[4:]
    return _label


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
    _temp_dir: Optional[TemporaryDirectory] = None

    _unmunge_codes: Dict[str, str]
    _munge_codes: Dict[str, str]

    def __init__(self, definition_dir: Path, use_directory: Optional[Path] = None, profile: bool = False) -> None:
        self.definition_dir = Path(definition_dir)
        if use_directory:
            self.use_directory = use_directory
        else:
            self._temp_dir = TemporaryDirectory()
            self.use_directory = Path(self._temp_dir.name)
        check_dir_path(self.use_directory)
        self._definition = None
        self._symbol_table = None
        self._profile = profile

    def __del__(self) -> None:
        if self._temp_dir is not None:
            self._temp_dir.cleanup()

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
        if isinstance(kore, Pattern):
            _kast_out = self._kore_to_kast(kore)
            if _kast_out is not None:
                return _kast_out
        _LOGGER.warning(f'Falling back to using `kast` for Kore -> Kast: {kore.text}')
        output = _kast(self.definition_dir, kore.text, input='kore', output='json', profile=self._profile)
        return KAst.from_dict(json.loads(output)['term'])

    def _kore_to_kast(self, kore: Pattern) -> Optional[KInner]:
        _LOGGER.debug(f'_kore_to_kast: {kore}')

        if type(kore) is DV and kore.sort.name.startswith('Sort'):
            return KToken(kore.value.value, KSort(kore.sort.name[4:]))

        elif type(kore) is EVar:
            vname = _unmunge(kore.name[3:])
            return KVariable(vname, sort=KSort(kore.sort.name[4:]))

        elif type(kore) is App:

            if kore.symbol == 'inj' and len(kore.sorts) == 2 and len(kore.patterns) == 1:
                return self._kore_to_kast(kore.patterns[0])

            elif len(kore.sorts) == 0:

                if kore.symbol == 'dotk' and len(kore.patterns) == 0:
                    return KSequence([])

                elif kore.symbol == 'kseq' and len(kore.patterns) == 2:
                    p0 = self._kore_to_kast(kore.patterns[0])
                    p1 = self._kore_to_kast(kore.patterns[1])
                    if p0 is not None and p1 is not None:
                        return KSequence([p0, p1])

                else:
                    _label_name = _unmunge(kore.symbol[3:])
                    klabel = KLabel(_label_name, [KSort(k.name[4:]) for k in kore.sorts])
                    args = [self._kore_to_kast(_a) for _a in kore.patterns]
                    # TODO: Written like this to appease the type-checker.
                    new_args = [a for a in args if a is not None]
                    if len(new_args) == len(args):
                        return KApply(klabel, new_args)

        elif type(kore) is And:
            psort = KSort(kore.sort.name[4:])
            larg = self._kore_to_kast(kore.left)
            rarg = self._kore_to_kast(kore.right)
            if larg is not None and rarg is not None:
                return KApply(KLabel('#And', [psort]), [larg, rarg])

        elif type(kore) is Equals:
            osort = KSort(kore.op_sort.name[4:])
            psort = KSort(kore.sort.name[4:])
            larg = self._kore_to_kast(kore.left)
            rarg = self._kore_to_kast(kore.right)
            if larg is not None and rarg is not None:
                return KApply(KLabel('#Equals', [osort, psort]), [larg, rarg])

        _LOGGER.warning(f'KPrint._kore_to_kast failed on input: {kore}')
        return None

    def kast_to_kore(self, kast: KAst, sort: Optional[KSort] = None) -> Kore:
        if isinstance(kast, KInner):
            _kore_out = self._kast_to_kore(kast, sort=sort)
            if _kore_out is not None:
                return _kore_out
        _LOGGER.warning(f'Falling back to using `kast` for KAst -> Kore: {kast}')
        kast_json = {'format': 'KAST', 'version': 2, 'term': kast.to_dict()}
        output = _kast(
            self.definition_dir, json.dumps(kast_json), input='json', output='kore', sort=sort, profile=self._profile
        )
        return KoreParser(output).pattern()

    def _kast_to_kore(self, kast: KInner, sort: Optional[KSort] = None) -> Optional[Pattern]:
        _LOGGER.debug(f'_kast_to_kore: {kast}')

        def _get_sort(_ki: KInner) -> Optional[KSort]:
            if type(_ki) is KApply:
                return self.definition.return_sort(_ki.label)
            return None

        if type(kast) is KToken:
            dv: Pattern = DV(SortApp('Sort' + kast.sort.name), String(kast.token))
            if sort is not None:
                dv = self._add_sort_injection(dv, kast.sort, sort)
            return dv

        elif type(kast) is KVariable:
            vname = _munge('Var' + kast.name)
            if sort is not None and kast.sort is not None:
                return self._add_sort_injection(EVar(vname, SortApp('Sort' + kast.sort.name)), kast.sort, sort)
            if sort is not None and kast.sort is None:
                return EVar(vname, SortApp('Sort' + sort.name))
            if sort is None and kast.sort is not None:
                return EVar(vname, SortApp('Sort' + kast.sort.name))

        elif type(kast) is KApply:

            if len(kast.label.params) == 0:
                # TODO: KAST validation should be a separate pass
                argument_sorts = self.definition.argument_sorts(kast.label)
                if kast.arity != len(argument_sorts):
                    raise ValueError(
                        f'Incorrect argument count for label {kast.label}:\n'
                        f'    Actual: {kast.args}\n'
                        f'    Expected: {argument_sorts}\n'
                    )
                args = [self._kast_to_kore(arg, sort=arg_sort) for arg, arg_sort in zip(kast.args, argument_sorts)]
                # TODO: Written like this to appease the type-checker.
                new_args = [a for a in args if a is not None]
                if len(new_args) == len(args):
                    label_name = 'Lbl' + _munge(kast.label.name)
                    app: Pattern = App(label_name, (), new_args)
                    isort = _get_sort(kast)
                    if sort is not None and isort is not None:
                        app = self._add_sort_injection(app, isort, sort)
                    return app

            elif len(kast.label.params) == 1:
                psort = kast.label.params[0]
                if kast.label.name == '#And' and kast.arity == 2:
                    larg = self._kast_to_kore(kast.args[0], sort=psort)
                    rarg = self._kast_to_kore(kast.args[1], sort=psort)
                    if larg is not None and rarg is not None:
                        _and: Pattern = And(SortApp('Sort' + psort.name), larg, rarg)
                        if sort is not None:
                            _and = self._add_sort_injection(_and, psort, sort)
                        return _and

            elif len(kast.label.params) == 2:
                osort = kast.label.params[0]
                psort = kast.label.params[1]

                if kast.label.name == '#Equals' and kast.arity == 2:
                    larg = self._kast_to_kore(kast.args[0], sort=osort)
                    rarg = self._kast_to_kore(kast.args[1], sort=osort)
                    if larg is not None and rarg is not None:
                        _equals: Pattern = Equals(
                            SortApp('Sort' + osort.name), SortApp('Sort' + psort.name), larg, rarg
                        )
                        if sort is not None:
                            _equals = self._add_sort_injection(_equals, psort, sort)
                        return _equals

        elif type(kast) is KSequence:
            args = [self._kast_to_kore(i, sort=KSort('KItem')) for i in reversed(kast.items)]
            # TODO: Written like this to appease the type-checker.
            new_args = [a for a in args if a is not None]
            if len(new_args) == len(args):
                seq = App('dotk', (), ())
                for a in new_args:
                    seq = App('kseq', (), [a, seq])
                return seq

        _LOGGER.warning(f'KPrint._kast_to_kore failed on input: {kast}')
        return None

    def _add_sort_injection(self, pat: Pattern, isort: KSort, osort: KSort) -> Pattern:
        if isort == osort:
            return pat
        if isort not in self.definition.subsorts(osort):
            raise ValueError(f'Could not find injection from subsort to supersort: {isort} -> {osort}')
        return App('inj', [SortApp('Sort' + isort.name), SortApp('Sort' + osort.name)], [pat])

    def pretty_print(self, kast: KAst) -> str:
        return pretty_print_kast(kast, self.symbol_table)


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


def pretty_print_kast(kast: KAst, symbol_table: SymbolTable) -> str:
    """Print out KAST terms/outer syntax.

    -   Input: KAST term.
    -   Output: Best-effort string representation of KAST term.
    """
    _LOGGER.debug(f'pretty_print_kast: {kast}')
    if type(kast) is KVariable:
        sort = kast.sort
        if not sort:
            return kast.name
        return kast.name + ':' + pretty_print_kast(sort, symbol_table)
    if type(kast) is KSort:
        return kast.name
    if type(kast) is KToken:
        return kast.token
    if type(kast) is KApply:
        label = kast.label.name
        args = kast.args
        unparsed_args = [pretty_print_kast(arg, symbol_table) for arg in args]
        if kast.is_cell:
            cell_contents = '\n'.join(unparsed_args).rstrip()
            cell_str = label + '\n' + indent(cell_contents) + '\n</' + label[1:]
            return cell_str.rstrip()
        unparser = applied_label_str(label) if label not in symbol_table else symbol_table[label]
        return unparser(*unparsed_args)
    if type(kast) is KAs:
        pattern_str = pretty_print_kast(kast.pattern, symbol_table)
        alias_str = pretty_print_kast(kast.alias, symbol_table)
        return pattern_str + ' #as ' + alias_str
    if type(kast) is KRewrite:
        lhs_str = pretty_print_kast(kast.lhs, symbol_table)
        rhs_str = pretty_print_kast(kast.rhs, symbol_table)
        return '( ' + lhs_str + ' => ' + rhs_str + ' )'
    if type(kast) is KSequence:
        if kast.arity == 0:
            return pretty_print_kast(EMPTY_K, symbol_table)
        if kast.arity == 1:
            return pretty_print_kast(kast.items[0], symbol_table)
        unparsed_k_seq = '\n~> '.join([pretty_print_kast(item, symbol_table) for item in kast.items[0:-1]])
        if kast.items[-1] == DOTS:
            unparsed_k_seq = unparsed_k_seq + '\n' + pretty_print_kast(DOTS, symbol_table)
        else:
            unparsed_k_seq = unparsed_k_seq + '\n~> ' + pretty_print_kast(kast.items[-1], symbol_table)
        return unparsed_k_seq
    if type(kast) is KTerminal:
        return '"' + kast.value + '"'
    if type(kast) is KRegexTerminal:
        return 'r"' + kast.regex + '"'
    if type(kast) is KNonTerminal:
        return pretty_print_kast(kast.sort, symbol_table)
    if type(kast) is KProduction:
        if 'klabel' not in kast.att and kast.klabel:
            kast = kast.update_atts({'klabel': kast.klabel.name})
        syntax_str = 'syntax ' + pretty_print_kast(kast.sort, symbol_table)
        if kast.items:
            syntax_str += ' ::= ' + ' '.join([pretty_print_kast(pi, symbol_table) for pi in kast.items])
        att_str = pretty_print_kast(kast.att, symbol_table)
        if att_str:
            syntax_str += ' ' + att_str
        return syntax_str
    if type(kast) is KSyntaxSort:
        sort_str = pretty_print_kast(kast.sort, symbol_table)
        att_str = pretty_print_kast(kast.att, symbol_table)
        return 'syntax ' + sort_str + ' ' + att_str
    if type(kast) is KSortSynonym:
        new_sort_str = pretty_print_kast(kast.new_sort, symbol_table)
        old_sort_str = pretty_print_kast(kast.old_sort, symbol_table)
        att_str = pretty_print_kast(kast.att, symbol_table)
        return 'syntax ' + new_sort_str + ' = ' + old_sort_str + ' ' + att_str
    if type(kast) is KSyntaxLexical:
        name_str = kast.name
        regex_str = kast.regex
        att_str = pretty_print_kast(kast.att, symbol_table)
        # todo: proper escaping
        return 'syntax lexical ' + name_str + ' = r"' + regex_str + '" ' + att_str
    if type(kast) is KSyntaxAssociativity:
        assoc_str = kast.assoc.value
        tags_str = ' '.join(kast.tags)
        att_str = pretty_print_kast(kast.att, symbol_table)
        return 'syntax associativity ' + assoc_str + ' ' + tags_str + ' ' + att_str
    if type(kast) is KSyntaxPriority:
        priorities_str = ' > '.join([' '.join(group) for group in kast.priorities])
        att_str = pretty_print_kast(kast.att, symbol_table)
        return 'syntax priority ' + priorities_str + ' ' + att_str
    if type(kast) is KBubble:
        body = '// KBubble(' + kast.sentence_type + ', ' + kast.content + ')'
        att_str = pretty_print_kast(kast.att, symbol_table)
        return body + ' ' + att_str
    if type(kast) is KRule or type(kast) is KClaim:
        body = '\n     '.join(pretty_print_kast(kast.body, symbol_table).split('\n'))
        rule_str = 'rule ' if type(kast) is KRule else 'claim '
        if 'label' in kast.att:
            rule_str = rule_str + '[' + kast.att['label'] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = pretty_print_kast(kast.att, symbol_table)
        if kast.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(pretty_print_kast_bool(kast.requires, symbol_table).split('\n'))
            rule_str = rule_str + '\n  ' + requires_str
        if kast.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(pretty_print_kast_bool(kast.ensures, symbol_table).split('\n'))
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str
    if type(kast) is KContext:
        body = indent(pretty_print_kast(kast.body, symbol_table))
        context_str = 'context alias ' + body
        requires_str = ''
        atts_str = pretty_print_kast(kast.att, symbol_table)
        if kast.requires != TRUE:
            requires_str = pretty_print_kast(kast.requires, symbol_table)
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
        imports = '\n'.join([pretty_print_kast(kimport, symbol_table) for kimport in kast.imports])
        sentences = '\n\n'.join([pretty_print_kast(sentence, symbol_table) for sentence in kast.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'
    if type(kast) is KRequire:
        return 'requires "' + kast.require + '"'
    if type(kast) is KDefinition:
        requires = '\n'.join([pretty_print_kast(require, symbol_table) for require in kast.requires])
        modules = '\n\n'.join([pretty_print_kast(module, symbol_table) for module in kast.modules])
        return requires + '\n\n' + modules

    raise ValueError(f'Error unparsing: {kast}')


def pretty_print_kast_bool(kast: KAst, symbol_table: SymbolTable) -> str:
    """Print out KAST requires/ensures clause.

    -   Input: KAST Bool for requires/ensures clause.
    -   Output: Best-effort string representation of KAST term.
    """
    _LOGGER.debug(f'pretty_print_kast_bool: {kast}')
    if type(kast) is KApply and kast.label.name in ['_andBool_', '_orBool_']:
        clauses = [pretty_print_kast_bool(c, symbol_table) for c in flatten_label(kast.label.name, kast)]
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
        return pretty_print_kast(kast, symbol_table)


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
