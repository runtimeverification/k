from __future__ import annotations

import logging
from functools import singledispatch
from typing import TYPE_CHECKING

from .att import EMPTY_ATT, Atts
from .outer import KAtt, KDefinition, KFlatModule, KImport, KRequire, KSentence  # noqa: TC002
from .outer_syntax import Att, Definition, Import, Module, Require, Sentence  # noqa: TC002

if TYPE_CHECKING:
    from typing import Any, Final

    from .outer import KAst
    from .outer_syntax import AST

_LOGGER: Final = logging.getLogger(__name__)


@singledispatch
def _ast_to_kast(ast: AST, **kwargs: Any) -> KAst:
    raise AssertionError(f'Unimplemented AST->KAst conversion for: {type(ast)}')


@_ast_to_kast.register
def _definition_to_kdefinition(d: Definition, main_module: str) -> KDefinition:
    modules = (_module_to_kflatmodule(m) for m in d.modules)
    requires = (_require_to_krequire(r) for r in d.requires)
    return KDefinition(main_module, modules, requires)


@_ast_to_kast.register
def _module_to_kflatmodule(m: Module) -> KFlatModule:
    sentences = (_sentence_to_ksentence(s) for s in m.sentences)
    imports = (_import_to_kimport(i) for i in m.imports)
    att = _att_to_katt(m.att)
    att = att.update([Atts.LOCATION(m.location)]) if m.location and not att.get(Atts.LOCATION) else att
    att = att.update([Atts.SOURCE(m.source)]) if m.source and not att.get(Atts.SOURCE) else att
    return KFlatModule(m.name, sentences, imports, att)


@_ast_to_kast.register
def _import_to_kimport(i: Import) -> KImport:
    return KImport(i.module_name, i.public)


@_ast_to_kast.register
def _require_to_krequire(r: Require) -> KRequire:
    return KRequire(r.path)


@_ast_to_kast.register
def _att_to_katt(att: Att) -> KAtt:
    if not att.items:
        return EMPTY_ATT
    return KAtt.parse(dict(att.items))


@singledispatch
@_ast_to_kast.register
def _sentence_to_ksentence(s: Sentence) -> KSentence:
    raise AssertionError(f'Unimplemented Sentence->KSentence conversion for: {type(s)}')
