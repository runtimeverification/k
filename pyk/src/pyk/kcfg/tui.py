from typing import Callable, Iterable, List, Optional

from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical
from textual.events import Click
from textual.message import Message, MessageTarget
from textual.widget import Widget
from textual.widgets import Static

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite
from pyk.kast.manip import flatten_label, minimize_term, push_down_rewrites
from pyk.ktool.kprint import KPrint
from pyk.prelude.kbool import TRUE

from ..kcfg import KCFG
from ..utils import shorten_hashes


class GraphChunk(Static):
    _node_text: str

    class Selected(Message):
        chunk_id: str

        def __init__(self, sender: MessageTarget, chunk_id: str) -> None:
            self.chunk_id = chunk_id
            super().__init__(sender)

    def __init__(self, id: str, node_text: Iterable[str] = ()) -> None:
        self._node_text = '\n'.join(node_text)
        super().__init__(self._node_text, id=id, classes='cfg-node')

    def on_enter(self) -> None:
        self.styles.border_left = ('double', 'red')  # type: ignore

    def on_leave(self) -> None:
        self.styles.border_left = None  # type: ignore

    async def on_click(self, click: Click) -> None:
        await self.emit(GraphChunk.Selected(self, self.id or ''))
        click.stop()


class BehaviorView(Widget):
    _kcfg: KCFG
    _kprint: KPrint
    _minimize: bool
    _node_printer: Optional[Callable[[CTerm], Iterable[str]]]
    _nodes: Iterable[GraphChunk]

    def __init__(
        self,
        kcfg: KCFG,
        kprint: KPrint,
        minimize: bool = True,
        node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None,
        id: str = '',
    ):
        super().__init__(id=id)
        self._kcfg = kcfg
        self._kprint = kprint
        self._minimize = minimize
        self._node_printer = node_printer
        self._nodes = []
        for lseg_id, node_lines in self._kcfg.pretty_segments(
            self._kprint, minimize=self._minimize, node_printer=self._node_printer
        ):
            self._nodes.append(GraphChunk(lseg_id, node_lines))

    def compose(self) -> ComposeResult:
        return self._nodes


class KCFGViewer(App):
    CSS_PATH = 'style.css'

    _kcfg: KCFG
    _kprint: KPrint
    _node_printer: Optional[Callable[[CTerm], Iterable[str]]]
    _minimize: bool
    _hidden_chunks: List[str]
    _selected_chunk: Optional[str]

    def __init__(
        self,
        kcfg: KCFG,
        kprint: KPrint,
        node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None,
        minimize: bool = True,
    ) -> None:
        super().__init__()
        self._kcfg = kcfg
        self._kprint = kprint
        self._node_printer = node_printer
        self._minimize = True
        self._hidden_chunks = []
        self._selected_chunk = None

    def compose(self) -> ComposeResult:
        yield Vertical(
            BehaviorView(self._kcfg, self._kprint, node_printer=self._node_printer, id='behavior'),
            id='navigation',
        )
        yield Vertical(
            Horizontal(Static('Info', id='info'), id='info-view'),
            Horizontal(Static('Term', id='term'), id='term-view'),
            Horizontal(Static('Constraint', id='constraint'), id='constraint-view'),
            id='display',
        )

    def on_graph_chunk_selected(self, message: GraphChunk.Selected) -> None:
        def _mostly_bool_constraints(cs: List[KInner]) -> List[KInner]:
            new_cs = []
            for c in cs:
                if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                    new_cs.append(c.args[1])
                else:
                    new_cs.append(c)
            return new_cs

        if message.chunk_id.startswith('node_'):
            self._selected_chunk = message.chunk_id
            node = message.chunk_id[5:]
            config, *_constraints = self._kcfg.node(node).cterm
            if self._minimize:
                config = minimize_term(config)
            constraints = _mostly_bool_constraints(_constraints)
            self.query_one('#info', Static).update(f'node({shorten_hashes(node)})')
            self.query_one('#term', Static).update(self._kprint.pretty_print(config))
            self.query_one('#constraint', Static).update('\n'.join(self._kprint.pretty_print(c) for c in constraints))

        elif message.chunk_id.startswith('edge_'):
            self._selected_chunk = None
            node_source, node_target = message.chunk_id[5:].split('_')
            config_source, *_constraints_source = self._kcfg.node(node_source).cterm
            config_target, *_constraints_target = self._kcfg.node(node_target).cterm
            constraints_source = _mostly_bool_constraints(_constraints_source)
            constraints_target = _mostly_bool_constraints(_constraints_target)
            constraints_new = [c for c in constraints_target if c not in constraints_source]
            config = push_down_rewrites(KRewrite(config_source, config_target))
            if self._minimize:
                config = minimize_term(config)
            self.query_one('#info', Static).update(
                f'edge({shorten_hashes(node_source)}, {shorten_hashes(node_target)})'
            )
            self.query_one('#term', Static).update(
                '\n'.join(self._kprint.pretty_print(c) for c in [config] + constraints_source)
            )
            self.query_one('#constraint', Static).update(
                '\n'.join(self._kprint.pretty_print(c) for c in constraints_new)
            )

        elif message.chunk_id.startswith('cover_'):
            self._selected_chunk = None
            node_source, node_target = message.chunk_id[6:].split('_')
            cover = self._kcfg.covers(source_id=node_source, target_id=node_target)[0]
            self.query_one('#info', Static).update(
                f'cover({shorten_hashes(node_source)}, {shorten_hashes(node_target)})'
            )
            subst_equalities = flatten_label('#And', cover.subst.ml_pred)
            self.query_one('#term', Static).update('\n'.join(self._kprint.pretty_print(se) for se in subst_equalities))
            constraints = flatten_label('#And', cover.constraint)
            self.query_one('#constraint', Static).update('\n'.join(self._kprint.pretty_print(c) for c in constraints))

    BINDINGS = [
        ('h', 'keystroke("h")', 'Hide selected node from graph.'),
        ('H', 'keystroke("H")', 'Unhide all nodes from graph.'),
    ]

    def action_keystroke(self, key: str) -> None:
        if key == 'h':
            if self._selected_chunk is not None and self._selected_chunk.startswith('node_'):
                node_id = self._selected_chunk[5:]
                self._hidden_chunks.append(self._selected_chunk)
                self.query_one(f'#{self._selected_chunk}', GraphChunk).add_class('hidden')
                self.query_one('#info', Static).update(f'HIDDEN: node({shorten_hashes(node_id)})')
        if key == 'H':
            for hc in self._hidden_chunks:
                self.query_one(f'#{hc}', GraphChunk).remove_class('hidden')
            node_ids = [nid[5:] for nid in self._hidden_chunks]
            self.query_one('#info', Static).update(f'UNHIDDEN: nodes({shorten_hashes(node_ids)})')
            self._hidden_chunks = []
