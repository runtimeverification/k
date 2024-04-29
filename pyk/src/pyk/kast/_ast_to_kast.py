from __future__ import annotations

import logging
from functools import singledispatch
from typing import TYPE_CHECKING

from .att import EMPTY_ATT
from .outer import KAtt, KDefinition, KFlatModule, KImport, KRequire, KSentence  # noqa: TC002
from .outer_syntax import Att, Definition, Import, Module, Require, Sentence  # noqa: TC002

if TYPE_CHECKING:
    from typing import Any, Final

    from .outer import KAst
    from .outer_syntax import AST

_LOGGER: Final = logging.getLogger(__name__)


@singledispatch
def _ast_to_kast(ast: AST, **kwargs: Any) -> KAst:
    _LOGGER.error(f'Unimplemented conversion for {type(ast)}')
    return None  # type: ignore


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
    return KAtt.from_dict({'att': dict(att.items)})


@singledispatch
@_ast_to_kast.register
def _sentence_to_ksentence(s: Sentence) -> KSentence:
    _LOGGER.error(f'Unimplemented conversion for {type(s)}')
    return None  # type: ignore
