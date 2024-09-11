from __future__ import annotations

from typing import TYPE_CHECKING, Union

from textual.app import App
from textual.binding import Binding
from textual.containers import Horizontal, ScrollableContainer, Vertical
from textual.message import Message
from textual.reactive import reactive
from textual.widget import Widget
from textual.widgets import Footer, Static

from ..cterm import CTerm
from ..kast.inner import KApply, KRewrite
from ..kast.manip import flatten_label, minimize_term, push_down_rewrites
from ..prelude.kbool import TRUE
from ..utils import ROOT, shorten_hashes, single
from .kcfg import KCFG
from .show import KCFGShow

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

    from textual.app import ComposeResult
    from textual.events import Click

    from ..kast import KInner
    from ..ktool.kprint import KPrint
    from .show import NodePrinter


KCFGElem = Union[KCFG.Node, KCFG.Successor]


class GraphChunk(Static):
    _node_text: str

    class Selected(Message):
        chunk_id: str

        def __init__(self, chunk_id: str) -> None:
            self.chunk_id = chunk_id
            super().__init__()

    def __init__(self, id: str, node_text: Iterable[str] = ()) -> None:
        self._node_text = '\n'.join(node_text)
        super().__init__(self._node_text, id=id, classes='cfg-node')

    def on_enter(self) -> None:
        self.styles.border_left = ('double', 'red')  # type: ignore

    def on_leave(self) -> None:
        self.styles.border_left = None  # type: ignore

    def on_click(self, click: Click) -> None:
        self.post_message(GraphChunk.Selected(self.id or ''))
        click.stop()


class NavWidget(ScrollableContainer, can_focus=True):
    text: reactive[str] = reactive('', init=False)

    class Selected(Message):
        def __init__(self) -> None:
            super().__init__()

    BINDINGS = [
        ('g', 'scroll_home', 'Go to vert start'),
        ('G', 'scroll_end', 'Go to vert end'),
    ]

    def __init__(self, id: str):
        super().__init__(id=id)

    def update(self, text: str) -> None:
        self.text = text

    def compose(self) -> ComposeResult:
        yield Static(self.text)

    def watch_text(self) -> None:
        self.query_one(Static).update(self.text)


class Info(Widget, can_focus=False):
    text: reactive[str] = reactive('', init=False)

    def __init__(self) -> None:
        super().__init__(id='info')

    def update(self, text: str) -> None:
        self.text = text

    def compose(self) -> ComposeResult:
        yield Static(self.text)

    def watch_text(self) -> None:
        self.query_one(Static).update(self.text)


class Status(NavWidget):
    def __init__(self) -> None:
        super().__init__(id='status')

    def on_click(self, click: Click) -> None:
        click.stop()
        self.post_message(Status.Selected())


class Term(NavWidget):
    def __init__(self) -> None:
        super().__init__(id='term')

    def on_click(self, click: Click) -> None:
        click.stop()
        self.post_message(Term.Selected())


class Constraint(NavWidget):
    def __init__(self) -> None:
        super().__init__(id='constraint')

    def on_click(self, click: Click) -> None:
        click.stop()
        self.post_message(Constraint.Selected())


class Custom(NavWidget):
    def __init__(self) -> None:
        super().__init__(id='custom')

    def on_click(self, click: Click) -> None:
        click.stop()
        self.post_message(Custom.Selected())


class BehaviorView(ScrollableContainer, can_focus=True):
    _kcfg: KCFG
    _kprint: KPrint
    _minimize: bool
    _node_printer: NodePrinter | None
    _kcfg_nodes: Iterable[GraphChunk]

    class Selected(Message):
        def __init__(self) -> None:
            super().__init__()

    def __init__(
        self,
        kcfg: KCFG,
        kprint: KPrint,
        minimize: bool = True,
        node_printer: NodePrinter | None = None,
        id: str = '',
    ):
        super().__init__(id=id)
        self._kcfg = kcfg
        self._kprint = kprint
        self._minimize = minimize
        self._node_printer = node_printer
        self._kcfg_nodes = []
        kcfg_show = KCFGShow(kprint, node_printer=node_printer)
        for lseg_id, node_lines in kcfg_show.pretty_segments(self._kcfg, minimize=self._minimize):
            self._kcfg_nodes.append(GraphChunk(lseg_id, node_lines))

    def compose(self) -> ComposeResult:
        return self._kcfg_nodes

    def on_click(self, click: Click) -> None:
        click.stop()
        self.post_message(BehaviorView.Selected())


class NodeView(Widget):
    _kprint: KPrint
    _custom_view: Callable[[KCFGElem], Iterable[str]] | None

    _element: KCFGElem | None

    _minimize: bool
    _term_on: bool
    _constraint_on: bool
    _custom_on: bool
    _status_on: bool
    _proof_status: str
    _proof_id: str
    _exec_time: float

    def __init__(
        self,
        kprint: KPrint,
        id: str = '',
        minimize: bool = True,
        term_on: bool = True,
        constraint_on: bool = True,
        custom_on: bool = False,
        status_on: bool = True,
        custom_view: Callable[[KCFGElem], Iterable[str]] | None = None,
        proof_status: str = '',
        proof_id: str = '',
        exec_time: float = 0,
    ):
        super().__init__(id=id)
        self._kprint = kprint
        self._element = None
        self._minimize = minimize
        self._term_on = term_on
        self._constraint_on = constraint_on
        self._custom_on = custom_on or custom_view is not None
        self._custom_view = custom_view
        self._status_on = status_on
        self._proof_status = proof_status
        self._proof_id = proof_id
        self._exec_time = exec_time

    def _info_text(self) -> str:
        term_str = '✅' if self._term_on else '❌'
        constraint_str = '✅' if self._constraint_on else '❌'
        custom_str = '' if self._custom_view is None else f'{"✅" if self._custom_on else "❌"} Custom View.'
        minimize_str = '✅' if self._minimize else '❌'
        status_str = '✅' if self._status_on else '❌'
        element_str = 'NOTHING'
        if type(self._element) is KCFG.Node:
            element_str = f'node({shorten_hashes(self._element.id)})'
        elif type(self._element) is KCFG.Edge:
            element_str = f'edge({shorten_hashes(self._element.source.id)},{shorten_hashes(self._element.target.id)})'
        elif type(self._element) is KCFG.MergedEdge:
            element_str = (
                f'merged_edge({shorten_hashes(self._element.source.id)},{shorten_hashes(self._element.target.id)})'
            )
        elif type(self._element) is KCFG.Cover:
            element_str = f'cover({shorten_hashes(self._element.source.id)},{shorten_hashes(self._element.target.id)})'
        return f'{element_str} selected. {minimize_str} Minimize Output. {term_str} Term View. {constraint_str} Constraint View. {status_str} Status View. {custom_str}'

    def _status_text(self) -> str:
        exec_time = str(round(self._exec_time, 2))
        return f'Proof ID: {self._proof_id}. Status: {self._proof_status}. Exec Time: {exec_time}s.'

    def compose(self) -> ComposeResult:
        yield Info()
        yield Status()
        yield Term()
        yield Constraint()
        if self._custom_view is not None:
            yield Custom()

    def toggle_option(self, field: str) -> bool:
        assert field in ['minimize', 'term_on', 'constraint_on', 'custom_on', 'status_on']
        field_attr = f'_{field}'
        old_value = getattr(self, field_attr)
        new_value = not old_value
        # Do not turn on custom view if it's not available
        if field == 'custom_on' and self._custom_view is None:
            new_value = False
        setattr(self, field_attr, new_value)
        self._update()
        return new_value

    def toggle_view(self, field: str) -> None:
        assert field in ['term', 'constraint', 'custom', 'status']
        if self.toggle_option(f'{field}_on'):
            self.query_one(f'#{field}').remove_class('hidden')
        else:
            self.query_one(f'#{field}').add_class('hidden')

    def update(self, element: KCFGElem) -> None:
        self._element = element
        self._update()

    def on_mount(self) -> None:
        self._update()

    def _update(self) -> None:
        def _boolify(c: KInner) -> KInner:
            if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                return c.args[1]
            else:
                return c

        def _cterm_text(cterm: CTerm) -> tuple[str, str]:
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
                crewrite = CTerm(config, constraints_new)
                term_str, constraint_str = _cterm_text(crewrite)

            elif type(self._element) is KCFG.MergedEdge:
                config_source, *constraints_source = self._element.source.cterm
                config_target, *constraints_target = self._element.target.cterm
                constraints_new = [c for c in constraints_target if c not in constraints_source]
                config = push_down_rewrites(KRewrite(config_source, config_target))
                crewrite = CTerm(config, constraints_new)
                term_str, constraint_str = _cterm_text(crewrite)

            elif type(self._element) is KCFG.Cover:
                subst_equalities = map(
                    _boolify,
                    flatten_label(
                        '#And', self._element.csubst.pred(sort_with=self._kprint.definition, constraints=False)
                    ),
                )
                constraints = map(_boolify, flatten_label('#And', self._element.csubst.constraint))
                term_str = '\n'.join(self._kprint.pretty_print(se) for se in subst_equalities)
                constraint_str = '\n'.join(self._kprint.pretty_print(c) for c in constraints)

            elif type(self._element) is KCFG.Split:
                term_strs = [f'split: {shorten_hashes(self._element.source.id)}']
                for target_id, csubst in self._element.splits.items():
                    term_strs.append('')
                    term_strs.append(f'  - {shorten_hashes(target_id)}')
                    if len(csubst.subst) > 0:
                        subst_equalities = map(
                            _boolify,
                            flatten_label('#And', csubst.pred(sort_with=self._kprint.definition, constraints=False)),
                        )
                        term_strs.extend(f'    {self._kprint.pretty_print(cline)}' for cline in subst_equalities)
                    if len(csubst.constraints) > 0:
                        constraints = map(_boolify, flatten_label('#And', csubst.constraint))
                        term_strs.extend(f'    {self._kprint.pretty_print(cline)}' for cline in constraints)
                term_str = '\n'.join(term_strs)

            elif type(self._element) is KCFG.NDBranch:
                term_strs = [f'ndbranch: {shorten_hashes(self._element.source.id)}']
                for target in self._element.targets:
                    term_strs.append('')
                    term_strs.append(f'  - {shorten_hashes(target.id)}')
                    term_strs.append('    (1 step)')
                term_str = '\n'.join(term_strs)

            if self._custom_view is not None:
                # To appease the type-checker
                if type(self._element) is KCFG.Node:
                    custom_str = '\n'.join(self._custom_view(self._element))
                elif isinstance(self._element, KCFG.Successor):
                    custom_str = '\n'.join(self._custom_view(self._element))

        self.query_one('#info', Info).text = self._info_text()
        self.query_one('#term', Term).text = term_str
        self.query_one('#constraint', Constraint).text = constraint_str
        if self._custom_view is not None:
            self.query_one('#custom', Custom).text = custom_str
        self.query_one('#status', Status).text = self._status_text()

    def on_behavior_view_selected(self) -> None:
        self.query_one('#behavior').focus()

    def on_term_selected(self) -> None:
        self.query_one(Term).focus()

    def on_constraint_selected(self) -> None:
        self.query_one(Constraint).focus()

    def on_custom_selected(self) -> None:
        self.query_one(Custom).focus()

    def on_status_selected(self) -> None:
        self.query_one(Status).focus()


class KCFGViewer(App):
    CSS_PATH = ROOT / 'kcfg/style.css'

    _kcfg: KCFG
    _kprint: KPrint

    _node_printer: NodePrinter | None
    _custom_view: Callable[[KCFGElem], Iterable[str]] | None

    _minimize: bool

    _hidden_chunks: list[str]
    _selected_chunk: str | None

    def __init__(
        self,
        kcfg: KCFG,
        kprint: KPrint,
        node_printer: NodePrinter | None = None,
        custom_view: Callable[[KCFGElem], Iterable[str]] | None = None,
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
        if self._custom_view is not None:
            self.bind('v', 'keystroke("custom")', description='Toggle custom.')

    def compose(self) -> ComposeResult:
        yield Horizontal(
            Vertical(
                BehaviorView(self._kcfg, self._kprint, node_printer=self._node_printer, id='behavior'),
                id='navigation',
            ),
            Vertical(
                NodeView(
                    self._kprint,
                    custom_view=self._custom_view,
                    proof_id=str(self._kcfg._node_id),
                    id='node-view',
                ),
                id='display',
            ),
        )
        yield Footer()

    def on_graph_chunk_selected(self, message: GraphChunk.Selected) -> None:
        self.query_one('#behavior').focus()

        if message.chunk_id.startswith('node_'):
            self._selected_chunk = message.chunk_id
            node, *_ = message.chunk_id[5:].split('_')
            node_id = int(node)
            self.query_one('#node-view', NodeView).update(self._kcfg.node(node_id))

        elif message.chunk_id.startswith('edge_'):
            self._selected_chunk = None
            node_source, node_target, *_ = message.chunk_id[5:].split('_')
            source_id = int(node_source)
            target_id = int(node_target)
            edge = single(self._kcfg.edges(source_id=source_id, target_id=target_id))
            self.query_one('#node-view', NodeView).update(edge)

        elif message.chunk_id.startswith('merged_edge_'):
            self._selected_chunk = None
            node_source, node_target, *_ = message.chunk_id[12:].split('_')
            source_id = int(node_source)
            target_id = int(node_target)
            merged_edge = single(self._kcfg.merged_edges(source_id=source_id, target_id=target_id))
            self.query_one('#node-view', NodeView).update(merged_edge)

        elif message.chunk_id.startswith('cover_'):
            self._selected_chunk = None
            node_source, node_target, *_ = message.chunk_id[6:].split('_')
            source_id = int(node_source)
            target_id = int(node_target)
            cover = single(self._kcfg.covers(source_id=source_id, target_id=target_id))
            self.query_one('#node-view', NodeView).update(cover)

        elif message.chunk_id.startswith('split_'):
            self._selected_chunk = None
            node_source, node_target, *_ = message.chunk_id[6:].split('_')
            source_id = int(node_source)
            target_id = int(node_target)
            split = single(self._kcfg.splits(source_id=source_id, target_id=target_id))
            self.query_one('#node-view', NodeView).update(split)

        elif message.chunk_id.startswith('ndbranch_'):
            self._selected_chunk = None
            node_source, node_target, *_ = message.chunk_id[8:].split('_')
            source_id = int(node_source)
            target_id = int(node_target)
            ndbranch = single(self._kcfg.ndbranches(source_id=source_id, target_id=target_id))
            self.query_one('#node-view', NodeView).update(ndbranch)

    BINDINGS = [
        ('h', 'keystroke("h")', 'Hide selected node.'),
        ('H', 'keystroke("H")', 'Unhide all nodes.'),
        ('t', 'keystroke("term")', 'Toggle term.'),
        ('c', 'keystroke("constraint")', 'Toggle constraint.'),
        ('m', 'keystroke("minimize")', 'Toggle minimization.'),
        ('s', 'keystroke("status")', 'Toggle status.'),
        Binding('q', 'quit', priority=True),
    ]

    def action_keystroke(self, key: str) -> None:
        if key == 'h':
            if self._selected_chunk is not None and self._selected_chunk.startswith('node_'):
                node_id = self._selected_chunk[5:]
                self._hidden_chunks.append(self._selected_chunk)
                self.query_one(f'#{self._selected_chunk}', GraphChunk).add_class('hidden')
                self.query_one('#info', Info).text = f'HIDDEN: node({shorten_hashes(node_id)})'
        elif key == 'H':
            for hc in self._hidden_chunks:
                self.query_one(f'#{hc}', GraphChunk).remove_class('hidden')
            node_ids = [nid[5:] for nid in self._hidden_chunks]
            self.query_one('#info', Info).text = f'UNHIDDEN: nodes({shorten_hashes(node_ids)})'
            self._hidden_chunks = []
        elif key in ['term', 'constraint', 'status']:
            self.query_one('#node-view', NodeView).toggle_view(key)
        elif key == 'custom' and self._custom_view is not None:
            self.query_one('#node-view', NodeView).toggle_view(key)
        elif key in ['minimize']:
            self.query_one('#node-view', NodeView).toggle_option(key)
