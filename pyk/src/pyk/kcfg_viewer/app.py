import json
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple, Union

from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical
from textual.widgets import Header, Static

from pyk.kast.inner import KApply
from pyk.kast.manip import minimize_term
from pyk.ktool import KPrint
from pyk.prelude.kbool import FALSE, TRUE, notBool

from ..cli_utils import check_file_path
from ..kcfg import KCFG
from ..utils import shorten_hashes


class KCFGViewer(App):
    CSS_PATH = 'style.css'

    _kcfg_file: Path
    _cfg: KCFG
    _kprint: KPrint
    _curr_node: str
    _minimize: bool

    BINDINGS = [
        ('p', 'keystroke("p")', 'Select previous node'),
        ('n', 'keystroke("n")', 'Select next node'),
        ('0', 'keystroke("0")', 'Select node 0'),
        ('1', 'keystroke("1")', 'Select node 1'),
        ('2', 'keystroke("2")', 'Select node 2'),
        ('3', 'keystroke("3")', 'Select node 3'),
        ('4', 'keystroke("4")', 'Select node 4'),
        ('5', 'keystroke("5")', 'Select node 5'),
        ('6', 'keystroke("6")', 'Select node 6'),
        ('7', 'keystroke("7")', 'Select node 7'),
        ('8', 'keystroke("8")', 'Select node 8'),
        ('9', 'keystroke("9")', 'Select node 9'),
        ('m', 'keystroke("m")', 'Toggle node minimization'),
    ]

    def __init__(self, kcfg_file: Union[str, Path], kprint: KPrint) -> None:
        kcfg_file = Path(kcfg_file)
        check_file_path(kcfg_file)
        super().__init__()
        self._kcfg_file = kcfg_file
        self._cfg = KCFG.from_dict(json.loads(kcfg_file.read_text()))
        self._kprint = kprint
        self._curr_node = self._cfg.get_unique_init().id
        self._minimize = True

    def _navigation_options(self) -> Dict[str, Tuple[str, str]]:
        nav_opts = {}
        in_edges: List[KCFG.EdgeLike] = []
        out_edges: List[KCFG.EdgeLike] = []
        for e in self._cfg.edges(target_id=self._curr_node):
            in_edges.append(e)
        for c in self._cfg.covers(target_id=self._curr_node):
            in_edges.append(c)
        for e in self._cfg.edges(source_id=self._curr_node):
            out_edges.append(e)
        for c in self._cfg.covers(source_id=self._curr_node):
            out_edges.append(c)
        counter = 0
        if len(in_edges) == 1:
            nav_opts['p'] = ('prev', in_edges[0].source.id)
        else:
            for ie in in_edges:
                if counter > 9:
                    break
                nav_opts[str(counter)] = ('prev', ie.source.id)
                counter += 1
        if len(out_edges) == 1:
            nav_opts['n'] = ('next', out_edges[0].target.id)
        else:
            for oe in out_edges:
                if counter > 9:
                    break
                nav_opts[str(counter)] = ('next', oe.target.id)
                counter += 1
        return nav_opts

    def _navigation_text(self) -> str:
        text_lines = [f'current node: {shorten_hashes(self._curr_node)}']
        for k, (d, n) in self._navigation_options().items():
            text_lines.append(f'    {k}: {d} {shorten_hashes(n)}')
        return '\n'.join(text_lines)

    def _behavior_text(self) -> str:
        text_lines = self._cfg.pretty(self._kprint, minimize=self._minimize)
        return '\n'.join(text_lines)

    def _display_text(self) -> str:
        text_lines = ['display options:']
        text_lines.append(f'    m: toggle minimization: {self._minimize}')
        return '\n'.join(text_lines)

    def _node_text(self) -> str:
        kast = self._cfg.node(self._curr_node).cterm.config
        if self._minimize:
            kast = minimize_term(kast)
        return self._kprint.pretty_print(kast)

    def _constraint_text(self) -> str:
        constraints = self._cfg.node(self._curr_node).cterm.constraints
        text_lines = []
        for c in constraints:
            if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                text_lines.append(self._kprint.pretty_print(c.args[1]))
            elif type(c) is KApply and c.label.name == '#Equals' and c.args[0] == FALSE:
                text_lines.append(self._kprint.pretty_print(notBool(c.args[1])))
            else:
                text_lines.append(self._kprint.pretty_print(c))
        return '\n'.join(text_lines)

    def compose(self) -> ComposeResult:
        yield Header()
        yield Horizontal(
            Vertical(
                Horizontal(Static(id='navigation'), id='navigation-view'),
                Horizontal(Static(id='behavior'), id='behavior-view'),
                id='left-pane-view',
            ),
            Vertical(
                Horizontal(Static(id='display'), id='display-view'),
                Horizontal(Static(id='node'), id='node-view'),
                Horizontal(Static(id='constraint'), id='constraint-view'),
                id='right-pane-view',
            ),
        )

    def update(self, components: Optional[Iterable[str]] = None) -> None:
        if components is None or 'navigation' in components:
            self.query_one('#navigation', Static).update(self._navigation_text())
        if components is None or 'behavior' in components:
            self.query_one('#behavior', Static).update(self._behavior_text())
        if components is None or 'display' in components:
            self.query_one('#display', Static).update(self._display_text())
        if components is None or 'node' in components:
            self.query_one('#node', Static).update(self._node_text())
        if components is None or 'constraint' in components:
            self.query_one('#constraint', Static).update(self._constraint_text())

    def on_mount(self) -> None:
        self.update()

    def action_keystroke(self, nid: str) -> None:
        nav_opts = self._navigation_options()
        if nid in nav_opts:
            _, next_node = nav_opts[nid]
            self._curr_node = next_node
            self.update(['navigation', 'node', 'constraint'])
        elif nid == 'm':
            self._minimize = not self._minimize
            self.update(['display', 'node'])
