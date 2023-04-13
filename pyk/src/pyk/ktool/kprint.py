from __future__ import annotations

import json
import logging
from collections.abc import Callable
from enum import Enum
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

from ..cli_utils import check_dir_path, check_file_path, run_process
from ..kast import kast_term
from ..kast.inner import KApply, KAs, KAtt, KInner, KLabel, KRewrite, KSequence, KSort, KToken, KVariable
from ..kast.manip import flatten_label
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
from ..konvert import kast_to_kore, unmunge
from ..kore.kompiled import KompiledKore
from ..kore.parser import KoreParser
from ..kore.prelude import BYTES as KORE_BYTES
from ..kore.prelude import STRING as KORE_STRING
from ..kore.syntax import DV, And, App, Assoc, Bottom, Ceil, Equals, EVar, Exists, Implies, Not, SortApp, Top
from ..prelude.bytes import bytesToken
from ..prelude.k import DOTS, EMPTY_K
from ..prelude.kbool import TRUE
from ..prelude.ml import mlAnd, mlBottom, mlCeil, mlEquals, mlExists, mlImplies, mlNot, mlTop
from ..prelude.string import stringToken

if TYPE_CHECKING:
    from collections.abc import Iterable
    from subprocess import CompletedProcess
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
    use_directory: Path
    main_module: str
    backend: str
    _extra_unparsing_modules: Iterable[KFlatModule]

    _temp_dir: TemporaryDirectory | None = None

    _bug_report: BugReport | None

    def __init__(
        self,
        definition_dir: Path,
        use_directory: Path | None = None,
        bug_report: BugReport | None = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
    ) -> None:
        self.definition_dir = Path(definition_dir)
        if use_directory:
            self.use_directory = use_directory
        else:
            self._temp_dir = TemporaryDirectory()
            self.use_directory = Path(self._temp_dir.name)
        check_dir_path(self.use_directory)
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

    def __del__(self) -> None:
        if self._temp_dir is not None:
            self._temp_dir.cleanup()

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
        _kast_out = self._kore_to_kast(kore)
        if _kast_out is not None:
            return self.definition.remove_cell_map_items(_kast_out)
        _LOGGER.warning(f'Falling back to using `kast` for Kore -> Kast: {kore.text}')
        proc_res = self._expression_kast(
            kore.text,
            input=KAstInput.KORE,
            output=KAstOutput.JSON,
        )
        return kast_term(json.loads(proc_res.stdout), KInner)  # type: ignore # https://github.com/python/mypy/issues/4717

    def _kore_to_kast(self, kore: Pattern) -> KInner | None:
        _LOGGER.debug(f'_kore_to_kast: {kore}')

        if type(kore) is DV and kore.sort.name.startswith('Sort'):
            if kore.sort == KORE_STRING:
                return stringToken(kore.value.value)
            if kore.sort == KORE_BYTES:
                return bytesToken(kore.value.value)
            return KToken(kore.value.value, KSort(kore.sort.name[4:]))

        elif type(kore) is EVar:
            vname = unmunge(kore.name[3:])
            return KVariable(vname, sort=KSort(kore.sort.name[4:]))

        elif type(kore) is App:
            if kore.symbol == 'inj' and len(kore.sorts) == 2 and len(kore.args) == 1:
                return self._kore_to_kast(kore.args[0])

            elif len(kore.sorts) == 0:
                if kore.symbol == 'dotk' and len(kore.args) == 0:
                    return KSequence([])

                elif kore.symbol == 'kseq' and len(kore.args) == 2:
                    p0 = self._kore_to_kast(kore.args[0])
                    p1 = self._kore_to_kast(kore.args[1])
                    if p0 is not None and p1 is not None:
                        return KSequence([p0, p1])

                else:
                    _label_name = unmunge(kore.symbol[3:])
                    klabel = KLabel(_label_name, [KSort(k.name[4:]) for k in kore.sorts])
                    args = [self._kore_to_kast(_a) for _a in kore.args]
                    # TODO: Written like this to appease the type-checker.
                    new_args = [a for a in args if a is not None]
                    if len(new_args) == len(args):
                        return KApply(klabel, new_args)

            # hardcoded polymorphic operators
            elif (
                len(kore.sorts) == 1
                and kore.symbol
                == "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
            ):
                _label_name = unmunge(kore.symbol[3:])
                klabel = KLabel(_label_name, [KSort(kore.sorts[0].name[4:])])
                # TODO: Written like this to appease the type-checker.
                args = [self._kore_to_kast(_a) for _a in kore.args]
                new_args = [a for a in args if a is not None]
                if len(new_args) == len(args):
                    return KApply(klabel, new_args)

        elif type(kore) is Top:
            return mlTop(sort=KSort(kore.sort.name[4:]))

        elif type(kore) is Bottom:
            return mlBottom(sort=KSort(kore.sort.name[4:]))

        elif type(kore) is And:
            psort = KSort(kore.sort.name[4:])
            larg = self._kore_to_kast(kore.left)
            rarg = self._kore_to_kast(kore.right)
            if larg is not None and rarg is not None:
                return mlAnd([larg, rarg], sort=psort)

        elif type(kore) is Implies:
            psort = KSort(kore.sort.name[4:])
            larg = self._kore_to_kast(kore.left)
            rarg = self._kore_to_kast(kore.right)
            if larg is not None and rarg is not None:
                return mlImplies(larg, rarg, sort=psort)

        elif type(kore) is Not:
            psort = KSort(kore.sort.name[4:])
            arg = self._kore_to_kast(kore.pattern)
            if arg is not None:
                return mlNot(arg, sort=psort)

        elif type(kore) is Exists:
            psort = KSort(kore.sort.name[4:])
            var = self._kore_to_kast(kore.var)
            body = self._kore_to_kast(kore.pattern)
            if var is not None and body is not None:
                assert type(var) is KVariable
                return mlExists(var, body, sort=psort)

        elif type(kore) is Equals:
            osort = KSort(kore.op_sort.name[4:])
            psort = KSort(kore.sort.name[4:])
            larg = self._kore_to_kast(kore.left)
            rarg = self._kore_to_kast(kore.right)
            if larg is not None and rarg is not None:
                return mlEquals(larg, rarg, arg_sort=osort, sort=psort)

        elif type(kore) is Ceil:
            osort = KSort(kore.op_sort.name[4:])
            psort = KSort(kore.sort.name[4:])
            arg = self._kore_to_kast(kore.pattern)
            if arg is not None:
                return mlCeil(arg, arg_sort=osort, sort=psort)

        elif isinstance(kore, Assoc):
            return self._kore_to_kast(kore.pattern)

        _LOGGER.warning(f'KPrint._kore_to_kast failed on input: {kore}')
        return None

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

    def pretty_print(self, kast: KAst) -> str:
        return pretty_print_kast(kast, self.symbol_table)

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
        file_path = self.use_directory / 'kast.input'
        file_path.write_text(expression)
        return _kast(
            file_path,
            command=command,
            definition_dir=self.definition_dir,
            input=input,
            output=output,
            module=module,
            sort=sort,
            check=check,
        )


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
        return kast.pretty
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
        modules = '\n\n'.join([pretty_print_kast(module, symbol_table) for module in kast.all_modules])
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
