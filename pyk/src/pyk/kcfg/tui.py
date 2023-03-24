from typing import Callable, Iterable, List, Optional, Tuple, Union

from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical
from textual.events import Click
from textual.message import Message, MessageTarget
from textual.widget import Widget
from textual.widgets import Footer, Static

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KRewrite
from pyk.kast.manip import flatten_label, minimize_term, push_down_rewrites
from pyk.ktool.kprint import KPrint
from pyk.prelude.kbool import TRUE
from pyk.prelude.ml import mlAnd

from ..kcfg import KCFG
from ..utils import shorten_hashes, single

KCFGElem = Union[KCFG.Node, KCFG.EdgeLike]


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


class NodeView(Widget):
    _kprint: KPrint
    _custom_view: Optional[Callable[[KCFGElem], Iterable[str]]]

    _element: Optional[KCFGElem]

    _minimize: bool
    _term_on: bool
    _constraint_on: bool
    _custom_on: bool

    def __init__(
        self,
        kprint: KPrint,
        id: str = '',
        minimize: bool = True,
        term_on: bool = True,
        constraint_on: bool = True,
        custom_on: bool = False,
        custom_view: Optional[Callable[[KCFGElem], Iterable[str]]] = None,
    ):
        super().__init__(id=id)
        self._kprint = kprint
        self._element = None
        self._minimize = minimize
        self._term_on = term_on
        self._constraint_on = constraint_on
        self._custom_on = custom_on or custom_view is not None
        self._custom_view = custom_view

    def _info_text(self) -> str:
        term_str = '✅' if self._term_on else '❌'
        constraint_str = '✅' if self._constraint_on else '❌'
        custom_str = '✅' if self._custom_on else '❌'
        minimize_str = '✅' if self._minimize else '❌'
        element_str = 'NOTHING'
        if type(self._element) is KCFG.Node:
            element_str = f'node({shorten_hashes(self._element.id)})'
        elif type(self._element) is KCFG.Edge:
            element_str = f'edge({shorten_hashes(self._element.source.id)},{shorten_hashes(self._element.target.id)})'
        elif type(self._element) is KCFG.Cover:
            element_str = f'cover({shorten_hashes(self._element.source.id)},{shorten_hashes(self._element.target.id)})'
        return f'{element_str} selected. {minimize_str} Minimize Output. {term_str} Term View. {constraint_str} Constraint View. {custom_str} Custom View.'

    def compose(self) -> ComposeResult:
        yield Horizontal(Static(self._info_text(), id='info'), id='info-view')
        yield Horizontal(Static('Term', id='term'), id='term-view', classes=('' if self._term_on else 'hidden'))
        yield Horizontal(
            Static('Constraint', id='constraint'),
            id='constraint-view',
            classes=('' if self._constraint_on else 'hidden'),
        )
        yield Horizontal(Static('Custom', id='custom'), id='custom-view', classes=('' if self._custom_on else 'hidden'))

    def toggle_option(self, field: str) -> bool:
        assert field in ['minimize', 'term_on', 'constraint_on', 'custom_on']
        field_attr = f'_{field}'
        old_value = getattr(self, field_attr)
        new_value = not old_value
        # Do not turn on custom view if it's not available
        if field == 'custom_on' and self._custom_view is None:
            new_value = False
        setattr(self, field_attr, new_value)
        self.query_one('#info', Static).update(self._info_text())
        self._update()
        return new_value

    def toggle_view(self, field: str) -> None:
        assert field in ['term', 'constraint', 'custom']
        if self.toggle_option(f'{field}_on'):
            self.query_one(f'#{field}-view', Horizontal).remove_class('hidden')
        else:
            self.query_one(f'#{field}-view', Horizontal).add_class('hidden')

    def update(self, element: KCFGElem) -> None:
        self._element = element
        self._update()

    def _update(self) -> None:
        def _boolify(c: KInner) -> KInner:
            if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                return c.args[1]
            else:
                return c

        def _cterm_text(cterm: CTerm) -> Tuple[str, str]:
            config = cterm.config
            constraints = map(_boolify, cterm.constraints)
            if self._minimize:
                config = minimize_term(config)
            return (self._kprint.pretty_print(config), '\n'.join(self._kprint.pretty_print(c) for c in constraints))

        term_str = 'Term'
        constraint_str = 'Constraint'
        custom_str = 'Custom'

        if self._element is not None:
            if type(self._element) is KCFG.Node:
                term_str, constraint_str = _cterm_text(self._element.cterm)

            elif type(self._element) is KCFG.Edge:
                config_source, *constraints_source = self._element.source.cterm
                config_target, *constraints_target = self._element.target.cterm
                constraints_new = [c for c in constraints_target if c not in constraints_source]
                config = push_down_rewrites(KRewrite(config_source, config_target))
                crewrite = CTerm(mlAnd([config] + constraints_new))
                term_str, constraint_str = _cterm_text(crewrite)

            elif type(self._element) is KCFG.Cover:
                subst_equalities = map(_boolify, flatten_label('#And', self._element.csubst.subst.ml_pred))
                constraints = map(_boolify, flatten_label('#And', self._element.csubst.constraint))
                term_str = '\n'.join(self._kprint.pretty_print(se) for se in subst_equalities)
                constraint_str = '\n'.join(self._kprint.pretty_print(c) for c in constraints)

            if self._custom_view is not None:
                custom_str = '\n'.join(self._custom_view(self._element))

        self.query_one('#info', Static).update(self._info_text())
        self.query_one('#term', Static).update(term_str)
        self.query_one('#constraint', Static).update(constraint_str)
        self.query_one('#custom', Static).update(custom_str)


class KCFGViewer(App):
    CSS_PATH = 'style.css'

    _kcfg: KCFG
    _kprint: KPrint

    _node_printer: Optional[Callable[[CTerm], Iterable[str]]]
    _custom_view: Optional[Callable[[KCFGElem], Iterable[str]]]

    _minimize: bool

    _hidden_chunks: List[str]
    _selected_chunk: Optional[str]

    def __init__(
        self,
        kcfg: KCFG,
        kprint: KPrint,
        node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None,
        custom_view: Optional[Callable[[KCFGElem], Iterable[str]]] = None,
        minimize: bool = True,
    ) -> None:
        super().__init__()
        self._kcfg = kcfg
        self._kprint = kprint
        self._node_printer = node_printer
        self._custom_view = custom_view
        self._minimize = minimize
        self._hidden_chunks = []
        self._selected_chunk = None

    def compose(self) -> ComposeResult:
        yield Horizontal(
            Vertical(
                BehaviorView(self._kcfg, self._kprint, node_printer=self._node_printer, id='behavior'),
                id='navigation',
            ),
            Vertical(NodeView(self._kprint, custom_view=self._custom_view, id='node-view'), id='display'),
        )
        yield Footer()

    def on_graph_chunk_selected(self, message: GraphChunk.Selected) -> None:
        if message.chunk_id.startswith('node_'):
            self._selected_chunk = message.chunk_id
            node = message.chunk_id[5:]
            self.query_one('#node-view', NodeView).update(self._kcfg.node(node))

        elif message.chunk_id.startswith('edge_'):
            self._selected_chunk = None
            node_source, node_target = message.chunk_id[5:].split('_')
            edge = single(self._kcfg.edges(source_id=node_source, target_id=node_target))
            self.query_one('#node-view', NodeView).update(edge)

        elif message.chunk_id.startswith('cover_'):
            self._selected_chunk = None
            node_source, node_target = message.chunk_id[6:].split('_')
            cover = single(self._kcfg.covers(source_id=node_source, target_id=node_target))
            self.query_one('#node-view', NodeView).update(cover)

        else:
            # should be unreachable
            raise AssertionError()

    BINDINGS = [
        ('h', 'keystroke("h")', 'Hide selected node.'),
        ('H', 'keystroke("H")', 'Unhide all nodes.'),
        ('t', 'keystroke("term")', 'Toggle term.'),
        ('c', 'keystroke("constraint")', 'Toggle constraint.'),
        ('v', 'keystroke("custom")', 'Toggle custom.'),
        ('m', 'keystroke("minimize")', 'Toggle minimization.'),
    ]

    def action_keystroke(self, key: str) -> None:
        if key == 'h':
            if self._selected_chunk is not None and self._selected_chunk.startswith('node_'):
                node_id = self._selected_chunk[5:]
                self._hidden_chunks.append(self._selected_chunk)
                self.query_one(f'#{self._selected_chunk}', GraphChunk).add_class('hidden')
                self.query_one('#info', Static).update(f'HIDDEN: node({shorten_hashes(node_id)})')
        elif key == 'H':
            for hc in self._hidden_chunks:
                self.query_one(f'#{hc}', GraphChunk).remove_class('hidden')
            node_ids = [nid[5:] for nid in self._hidden_chunks]
            self.query_one('#info', Static).update(f'UNHIDDEN: nodes({shorten_hashes(node_ids)})')
            self._hidden_chunks = []
        elif key in ['term', 'constraint', 'custom']:
            self.query_one('#node-view', NodeView).toggle_view(key)
        elif key in ['minimize']:
            self.query_one('#node-view', NodeView).toggle_option(key)
