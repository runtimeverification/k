from __future__ import annotations

import json
import logging
from collections.abc import Callable
from contextlib import contextmanager
from enum import Enum
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING

from ..cli_utils import check_dir_path, check_file_path, run_process
from ..kast import kast_term
from ..kast.inner import KApply, KAs, KAtt, KInner, KRewrite, KSequence, KSort, KToken, KVariable
from ..kast.manip import flatten_label, undo_aliases
from ..kast.outer import (
    KBubble,
    KClaim,
    KContext,
    KDefinition,
    KFlatModule,
    KImport,
    KNonTerminal,
    KProduction,
    KRegexTerminal,
    KRequire,
    KRule,
    KSortSynonym,
    KSyntaxAssociativity,
    KSyntaxLexical,
    KSyntaxPriority,
    KSyntaxSort,
    KTerminal,
    read_kast_definition,
)
from ..konvert import kast_to_kore, kore_to_kast
from ..kore.kompiled import KompiledKore
from ..kore.parser import KoreParser
from ..kore.syntax import App, SortApp
from ..prelude.k import DOTS, EMPTY_K
from ..prelude.kbool import TRUE

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from subprocess import CompletedProcess
    from tempfile import _TemporaryFileWrapper
    from typing import Any, Final

    from ..cli_utils import BugReport
    from ..kast import KAst
    from ..kore.syntax import Pattern

_LOGGER: Final = logging.getLogger(__name__)

SymbolTable = dict[str, Callable[..., str]]


class KAstInput(Enum):
    PROGRAM = 'program'
    BINARY = 'binary'
    JSON = 'json'
    KAST = 'kast'
    KORE = 'kore'
    RULE = 'rule'


class KAstOutput(Enum):
    PRETTY = 'pretty'
    PROGRAM = 'program'
    KAST = 'kast'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


def _kast(
    file: str | Path | None = None,
    *,
    command: str | None = None,
    definition_dir: str | Path | None = None,
    input: str | KAstInput | None = None,
    output: str | KAstOutput | None = None,
    expression: str | None = None,
    module: str | None = None,
    sort: str | None = None,
    gen_glr_parser: bool = False,
    # ---
    check: bool = True,
) -> CompletedProcess:
    if file is not None:
        file = Path(file)

    if file and not gen_glr_parser:
        check_file_path(file)

    if not file and gen_glr_parser:
        raise ValueError('No output file specified for --gen-glr-parser')

    if definition_dir is not None:
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)

    if input is not None:
        input = KAstInput(input)

    if output is not None:
        output = KAstOutput(output)

    args = _build_arg_list(
        file=file,
        command=command,
        definition_dir=definition_dir,
        input=input,
        output=output,
        expression=expression,
        module=module,
        sort=sort,
        gen_glr_parser=gen_glr_parser,
    )

    try:
        return run_process(args, logger=_LOGGER, check=check)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kast exited with code {err.returncode} for: {file}', err.stdout, err.stderr
        ) from err


def gen_glr_parser(
    parser_file: str | Path,
    *,
    command: str | None = None,
    definition_dir: str | Path | None = None,
    module: str | None = None,
    sort: str | None = None,
) -> Path:
    parser_file = Path(parser_file)
    _kast(
        file=parser_file,
        command=command,
        definition_dir=definition_dir,
        module=module,
        sort=sort,
        gen_glr_parser=True,
        check=True,
    )
    assert parser_file.is_file()
    return parser_file


def _build_arg_list(
    *,
    file: Path | None,
    command: str | None,
    definition_dir: Path | None,
    input: KAstInput | None,
    output: KAstOutput | None,
    expression: str | None,
    module: str | None,
    sort: str | None,
    gen_glr_parser: bool,
) -> list[str]:
    args = [command if command is not None else 'kast']
    if file:
        args += [str(file)]
    if definition_dir:
        args += ['--definition', str(definition_dir)]
    if input:
        args += ['--input', input.value]
    if output:
        args += ['--output', output.value]
    if expression:
        args += ['--expression', expression]
    if module:
        args += ['--module', module]
    if sort:
        args += ['--sort', sort]
    if gen_glr_parser:
        args += ['--gen-glr-parser']
    return args


class KPrint:
    definition_dir: Path
    use_directory: Path | None
    main_module: str
    backend: str
    _extra_unparsing_modules: Iterable[KFlatModule]

    _bug_report: BugReport | None

    def __init__(
        self,
        definition_dir: Path,
        use_directory: Path | None = None,
        bug_report: BugReport | None = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
    ) -> None:
        self.definition_dir = definition_dir

        if use_directory:
            check_dir_path(use_directory)

        self.use_directory = use_directory
        self._definition = None
        self._symbol_table = None
        with open(self.definition_dir / 'mainModule.txt') as mm:
            self.main_module = mm.read()
        with open(self.definition_dir / 'backend.txt') as ba:
            self.backend = ba.read()
        self._extra_unparsing_modules = extra_unparsing_modules
        self._bug_report = bug_report
        if self._bug_report:
            self._bug_report.add_definition(self.definition_dir)

    @contextmanager
    def _temp_file(self, suffix: str | None = None) -> Iterator[_TemporaryFileWrapper]:
        with NamedTemporaryFile(
            'w',
            dir=self.use_directory,
            delete=not self.use_directory,
            suffix=suffix,
        ) as ntf:
            _LOGGER.info(f'Created temporary file: {ntf.name}')
            yield ntf

    @cached_property
    def definition(self) -> KDefinition:
        return read_kast_definition(self.definition_dir / 'compiled.json')

    @cached_property
    def kompiled_kore(self) -> KompiledKore:
        return KompiledKore(self.definition_dir)

    @property
    def definition_hash(self) -> str:
        return self.definition.hash

    @cached_property
    def symbol_table(self) -> SymbolTable:
        symb_table = build_symbol_table(self.definition, extra_modules=self._extra_unparsing_modules, opinionated=True)
        self._patch_symbol_table(symb_table)
        return symb_table

    @classmethod
    def _patch_symbol_table(cls, symbol_table: SymbolTable) -> None:
        pass

    def parse_token(self, ktoken: KToken, *, as_rule: bool = False) -> KInner:
        input = KAstInput('rule' if as_rule else 'program')
        proc_res = self._expression_kast(
            ktoken.token,
            input=input,
            output=KAstOutput.JSON,
            sort=ktoken.sort.name,
        )
        return kast_term(json.loads(proc_res.stdout), KInner)  # type: ignore # https://github.com/python/mypy/issues/4717

    def kore_to_pretty(self, pattern: Pattern) -> str:
        proc_res = self._expression_kast(
            pattern.text,
            input=KAstInput.KORE,
            output=KAstOutput.PRETTY,
        )
        return proc_res.stdout

    def kore_to_kast(self, kore: Pattern) -> KInner:
        _LOGGER.debug(f'kore_to_kast: {kore.text}')

        try:
            return kore_to_kast(self.definition, kore)
        except ValueError as err:
            _LOGGER.warning(err)

        _LOGGER.warning(f'Falling back to using `kast` for Kore -> Kast: {kore.text}')
        proc_res = self._expression_kast(
            kore.text,
            input=KAstInput.KORE,
            output=KAstOutput.JSON,
        )
        return kast_term(json.loads(proc_res.stdout), KInner)  # type: ignore # https://github.com/python/mypy/issues/4717

    def kast_to_kore(self, kast: KInner, sort: KSort | None = None) -> Pattern:
        try:
            return kast_to_kore(self.definition, self.kompiled_kore, kast, sort)
        except ValueError as ve:
            _LOGGER.warning(ve)

        _LOGGER.warning(f'Falling back to using `kast` for KAst -> Kore: {kast}')
        kast_json = {'format': 'KAST', 'version': 2, 'term': kast.to_dict()}
        proc_res = self._expression_kast(
            json.dumps(kast_json),
            input=KAstInput.JSON,
            output=KAstOutput.KORE,
            sort=sort.name if sort is not None else None,
        )
        return KoreParser(proc_res.stdout).pattern()

    def _add_sort_injection(self, pat: Pattern, isort: KSort, osort: KSort) -> Pattern:
        if isort == osort:
            return pat
        if isort not in self.definition.subsorts(osort):
            raise ValueError(
                f'Could not find injection from subsort to supersort {isort} -> {osort} for pattern: {pat}'
            )
        return App('inj', [SortApp('Sort' + isort.name), SortApp('Sort' + osort.name)], [pat])

    def pretty_print(self, kast: KAst, *, unalias: bool = True) -> str:
        if unalias and isinstance(kast, KInner):
            kast = undo_aliases(self.definition, kast)
        return PrettyPrinter(self.symbol_table).print(kast)

    def _expression_kast(
        self,
        expression: str,
        *,
        command: str | None = None,
        input: str | KAstInput | None = None,
        output: str | KAstOutput | None = None,
        module: str | None = None,
        sort: str | None = None,
        # ---
        check: bool = True,
    ) -> CompletedProcess:
        if len(expression) < 128 * 1024:
            return _kast(
                expression=expression,
                command=command,
                definition_dir=self.definition_dir,
                input=input,
                output=output,
                module=module,
                sort=sort,
                check=check,
            )

        with self._temp_file() as ntf:
            ntf.write(expression)
            ntf.flush()

            return _kast(
                ntf.name,
                command=command,
                definition_dir=self.definition_dir,
                input=input,
                output=output,
                module=module,
                sort=sort,
                check=check,
            )


def pretty_print_kast(kast: KAst, symbol_table: SymbolTable) -> str:
    return PrettyPrinter(symbol_table).print(kast)


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


def build_symbol_table(
    definition: KDefinition, extra_modules: Iterable[KFlatModule] = (), opinionated: bool = False
) -> SymbolTable:
    """Build the unparsing symbol table given a JSON encoded definition.

    -   Input: JSON encoded K definition.
    -   Return: Python dictionary mapping klabels to automatically generated unparsers.
    """
    symbol_table = {}
    all_modules = list(definition.all_modules) + ([] if extra_modules is None else list(extra_modules))
    for module in all_modules:
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


def paren(printer: Callable[..., str]) -> Callable[..., str]:
    return lambda *args: '( ' + printer(*args) + ' )'


def indent(text: str, size: int = 2) -> str:
    return '\n'.join([(' ' * size) + line for line in text.split('\n')])


def assoc_with_unit(assoc_join: str, unit: str) -> Callable[..., str]:
    def _assoc_with_unit(*args: str) -> str:
        return assoc_join.join(arg for arg in args if arg != unit)

    return _assoc_with_unit


class PrettyPrinter:
    symbol_table: SymbolTable

    def __init__(self, symbol_table: SymbolTable):
        self.symbol_table = symbol_table

    def print(self, kast: KAst) -> str:
        """Print out KAST terms/outer syntax.
        -   Input: KAST term.
        -   Output: Best-effort string representation of KAST term.
        """
        _LOGGER.debug(f'pretty_print_kast: {kast}')
        match kast:
            case KVariable():
                return self._print_kvariable(kast)
            case KSort():
                return self._print_ksort(kast)
            case KToken():
                return self._print_ktoken(kast)
            case KApply():
                return self._print_kapply(kast)
            case KAs():
                return self._print_kas(kast)
            case KRewrite():
                return self._print_krewrite(kast)
            case KSequence():
                return self._print_ksequence(kast)
            case KTerminal():
                return self._print_kterminal(kast)
            case KRegexTerminal():
                return self._print_kregexterminal(kast)
            case KNonTerminal():
                return self._print_knonterminal(kast)
            case KProduction():
                return self._print_kproduction(kast)
            case KSyntaxSort():
                return self._print_ksyntaxsort(kast)
            case KSortSynonym():
                return self._print_ksortsynonym(kast)
            case KSyntaxLexical():
                return self._print_ksyntaxlexical(kast)
            case KSyntaxAssociativity():
                return self._print_ksyntaxassociativity(kast)
            case KSyntaxPriority():
                return self._print_ksyntaxpriority(kast)
            case KBubble():
                return self._print_kbubble(kast)
            case KRule():
                return self._print_krule(kast)
            case KClaim():
                return self._print_kclaim(kast)
            case KContext():
                return self._print_kcontext(kast)
            case KAtt():
                return self._print_katt(kast)
            case KImport():
                return self._print_kimport(kast)
            case KFlatModule():
                return self._print_kflatmodule(kast)
            case KRequire():
                return self._print_krequire(kast)
            case KDefinition():
                return self._print_kdefinition(kast)
            case _:
                raise AssertionError(f'Error unparsing: {kast}')

    def _print_kvariable(self, kvariable: KVariable) -> str:
        sort = kvariable.sort
        if not sort:
            return kvariable.name
        return kvariable.name + ':' + self.print(sort)

    def _print_ksort(self, ksort: KSort) -> str:
        return ksort.name

    def _print_ktoken(self, ktoken: KToken) -> str:
        return ktoken.token

    def _print_kapply(self, kapply: KApply) -> str:
        label = kapply.label.name
        args = kapply.args
        unparsed_args = [self.print(arg) for arg in args]
        if kapply.is_cell:
            cell_contents = '\n'.join(unparsed_args).rstrip()
            cell_str = label + '\n' + indent(cell_contents) + '\n</' + label[1:]
            return cell_str.rstrip()
        unparser = self._applied_label_str(label) if label not in self.symbol_table else self.symbol_table[label]
        return unparser(*unparsed_args)

    def _print_kas(self, kas: KAs) -> str:
        pattern_str = self.print(kas.pattern)
        alias_str = self.print(kas.alias)
        return pattern_str + ' #as ' + alias_str

    def _print_krewrite(self, krewrite: KRewrite) -> str:
        lhs_str = self.print(krewrite.lhs)
        rhs_str = self.print(krewrite.rhs)
        return '( ' + lhs_str + ' => ' + rhs_str + ' )'

    def _print_ksequence(self, ksequence: KSequence) -> str:
        if ksequence.arity == 0:
            return self.print(EMPTY_K)
        if ksequence.arity == 1:
            return self.print(ksequence.items[0])
        unparsed_k_seq = '\n~> '.join([self.print(item) for item in ksequence.items[0:-1]])
        if ksequence.items[-1] == DOTS:
            unparsed_k_seq = unparsed_k_seq + '\n' + self.print(DOTS)
        else:
            unparsed_k_seq = unparsed_k_seq + '\n~> ' + self.print(ksequence.items[-1])
        return unparsed_k_seq

    def _print_kterminal(self, kterminal: KTerminal) -> str:
        return '"' + kterminal.value + '"'

    def _print_kregexterminal(self, kregexterminal: KRegexTerminal) -> str:
        return 'r"' + kregexterminal.regex + '"'

    def _print_knonterminal(self, knonterminal: KNonTerminal) -> str:
        return self.print(knonterminal.sort)

    def _print_kproduction(self, kproduction: KProduction) -> str:
        if 'klabel' not in kproduction.att and kproduction.klabel:
            kproduction = kproduction.update_atts({'klabel': kproduction.klabel.name})
        syntax_str = 'syntax ' + self.print(kproduction.sort)
        if kproduction.items:
            syntax_str += ' ::= ' + ' '.join([self.print(pi) for pi in kproduction.items])
        att_str = self.print(kproduction.att)
        if att_str:
            syntax_str += ' ' + att_str
        return syntax_str

    def _print_ksyntaxsort(self, ksyntaxsort: KSyntaxSort) -> str:
        sort_str = self.print(ksyntaxsort.sort)
        att_str = self.print(ksyntaxsort.att)
        return 'syntax ' + sort_str + ' ' + att_str

    def _print_ksortsynonym(self, ksortsynonym: KSortSynonym) -> str:
        new_sort_str = self.print(ksortsynonym.new_sort)
        old_sort_str = self.print(ksortsynonym.old_sort)
        att_str = self.print(ksortsynonym.att)
        return 'syntax ' + new_sort_str + ' = ' + old_sort_str + ' ' + att_str

    def _print_ksyntaxlexical(self, ksyntaxlexical: KSyntaxLexical) -> str:
        name_str = ksyntaxlexical.name
        regex_str = ksyntaxlexical.regex
        att_str = self.print(ksyntaxlexical.att)
        # todo: proper escaping
        return 'syntax lexical ' + name_str + ' = r"' + regex_str + '" ' + att_str

    def _print_ksyntaxassociativity(self, ksyntaxassociativity: KSyntaxAssociativity) -> str:
        assoc_str = ksyntaxassociativity.assoc.value
        tags_str = ' '.join(ksyntaxassociativity.tags)
        att_str = self.print(ksyntaxassociativity.att)
        return 'syntax associativity ' + assoc_str + ' ' + tags_str + ' ' + att_str

    def _print_ksyntaxpriority(self, ksyntaxpriority: KSyntaxPriority) -> str:
        priorities_str = ' > '.join([' '.join(group) for group in ksyntaxpriority.priorities])
        att_str = self.print(ksyntaxpriority.att)
        return 'syntax priority ' + priorities_str + ' ' + att_str

    def _print_kbubble(self, kbubble: KBubble) -> str:
        body = '// KBubble(' + kbubble.sentence_type + ', ' + kbubble.content + ')'
        att_str = self.print(kbubble.att)
        return body + ' ' + att_str

    def _print_krule(self, kterm: KRule) -> str:
        body = '\n     '.join(self.print(kterm.body).split('\n'))
        rule_str = 'rule '
        if 'label' in kterm.att:
            rule_str = rule_str + '[' + kterm.att['label'] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = self.print(kterm.att)
        if kterm.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(self._print_kast_bool(kterm.requires).split('\n'))
            rule_str = rule_str + '\n  ' + requires_str
        if kterm.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(self._print_kast_bool(kterm.ensures).split('\n'))
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str

    def _print_kclaim(self, kterm: KClaim) -> str:
        body = '\n     '.join(self.print(kterm.body).split('\n'))
        rule_str = 'claim '
        if 'label' in kterm.att:
            rule_str = rule_str + '[' + kterm.att['label'] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = self.print(kterm.att)
        if kterm.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(self._print_kast_bool(kterm.requires).split('\n'))
            rule_str = rule_str + '\n  ' + requires_str
        if kterm.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(self._print_kast_bool(kterm.ensures).split('\n'))
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str

    def _print_kcontext(self, kcontext: KContext) -> str:
        body = indent(self.print(kcontext.body))
        context_str = 'context alias ' + body
        requires_str = ''
        atts_str = self.print(kcontext.att)
        if kcontext.requires != TRUE:
            requires_str = self.print(kcontext.requires)
            requires_str = 'requires ' + indent(requires_str)
        return context_str + '\n  ' + requires_str + '\n  ' + atts_str

    def _print_katt(self, katt: KAtt) -> str:
        return katt.pretty

    def _print_kimport(self, kimport: KImport) -> str:
        return ' '.join(['imports', ('public' if kimport.public else 'private'), kimport.name])

    def _print_kflatmodule(self, kflatmodule: KFlatModule) -> str:
        name = kflatmodule.name
        imports = '\n'.join([self.print(kimport) for kimport in kflatmodule.imports])
        sentences = '\n\n'.join([self.print(sentence) for sentence in kflatmodule.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'

    def _print_krequire(self, krequire: KRequire) -> str:
        return 'requires "' + krequire.require + '"'

    def _print_kdefinition(self, kdefinition: KDefinition) -> str:
        requires = '\n'.join([self.print(require) for require in kdefinition.requires])
        modules = '\n\n'.join([self.print(module) for module in kdefinition.all_modules])
        return requires + '\n\n' + modules

    def _print_kast_bool(self, kast: KAst) -> str:
        """Print out KAST requires/ensures clause.

        -   Input: KAST Bool for requires/ensures clause.
        -   Output: Best-effort string representation of KAST term.
        """
        _LOGGER.debug(f'_print_kast_bool: {kast}')
        if type(kast) is KApply and kast.label.name in ['_andBool_', '_orBool_']:
            clauses = [self._print_kast_bool(c) for c in flatten_label(kast.label.name, kast)]
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
            return self.print(kast)

    def _applied_label_str(self, symbol: str) -> Callable[..., str]:
        return lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )'
