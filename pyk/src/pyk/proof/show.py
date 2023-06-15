from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kcfg.show import NodePrinter

if TYPE_CHECKING:
    from typing import Final

    from ..kcfg import KCFG
    from ..ktool.kprint import KPrint
    from .reachability import APRBMCProof, APRProof

_LOGGER: Final = logging.getLogger(__name__)


class APRProofNodePrinter(NodePrinter):
    proof: APRProof

    def __init__(self, proof: APRProof, kprint: KPrint, full_printer: bool = False, minimize: bool = False):
        super().__init__(kprint, full_printer=full_printer, minimize=minimize)
        self.proof = proof

    def node_attrs(self, kcfg: KCFG, node: KCFG.Node) -> list[str]:
        attrs = super().node_attrs(kcfg, node)
        if self.proof.is_pending(node.id):
            attrs.append('pending')
        if self.proof.is_terminal(node.id):
            attrs.append('terminal')
            if 'stuck' in attrs:
                attrs.remove('stuck')
        return attrs


class APRBMCProofNodePrinter(APRProofNodePrinter):
    proof: APRBMCProof

    def __init__(self, proof: APRBMCProof, kprint: KPrint, full_printer: bool = False, minimize: bool = False):
        super().__init__(proof, kprint, full_printer=full_printer, minimize=minimize)

    def node_attrs(self, kcfg: KCFG, node: KCFG.Node) -> list[str]:
        attrs = super().node_attrs(kcfg, node)
        if self.proof.is_bounded(node.id):
            attrs.append('bounded')
            if 'stuck' in attrs:
                attrs.remove('stuck')
        return attrs
