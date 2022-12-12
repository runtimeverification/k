import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, List, Optional, Set, Tuple, Union, final

from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical
from textual.widgets import Header, Static, Tree, TreeNode

from ..cli_utils import check_file_path
from ..kcfg import KCFG
from ..utils import shorten_hash


class Terminal(ABC):
    @property
    @abstractmethod
    def label(self) -> str:
        ...


@final
@dataclass(frozen=True)
class Loop(Terminal):
    @property
    def label(self) -> str:
        return 'loop back'


@final
@dataclass(frozen=True)
class Stuck(Terminal):
    @property
    def label(self) -> str:
        return 'stuck'


@final
@dataclass(frozen=True)
class Cover(Terminal):
    cover: KCFG.Cover

    @property
    def label(self) -> str:
        short_hash = shorten_hash(self.cover.target.id)
        return f'covered by {short_hash}'


class NodeModel(ABC):
    @property
    @abstractmethod
    def node(self) -> KCFG.Node:
        ...

    @property
    @abstractmethod
    def terminal(self) -> Optional[Terminal]:
        ...

    @property
    def label(self) -> str:
        short_hash = shorten_hash(self.node.id)
        if self.terminal:
            return f'{short_hash} ({self.terminal.label})'
        return short_hash


@final
@dataclass(frozen=True)
class Init(NodeModel):
    _node: KCFG.Node

    def __init__(self, node: KCFG.Node):
        object.__setattr__(self, '_node', node)

    @property
    def node(self) -> KCFG.Node:
        return self._node

    @property
    def terminal(self) -> None:
        return None

    def __str__(self) -> str:
        return f'[Init] {self.label}'


@final
@dataclass(frozen=True)
class Step(NodeModel):
    in_edge: KCFG.Edge
    _terminal: Optional[Terminal] = None

    @property
    def node(self) -> KCFG.Node:
        return self.in_edge.target

    @property
    def terminal(self) -> Optional[Terminal]:
        return self._terminal

    def __str__(self) -> str:
        return f'[Step {self.in_edge.depth}] {self.label}'


@final
@dataclass(frozen=True)
class Branch(NodeModel):
    in_edge: KCFG.Edge
    _terminal: Optional[Terminal] = None

    @property
    def node(self) -> KCFG.Node:
        return self.in_edge.target

    @property
    def terminal(self) -> Optional[Terminal]:
        return self._terminal

    def __str__(self) -> str:
        return f'[Branch] {self.label}'


@final
@dataclass(frozen=True)
class Case(NodeModel):
    cover: KCFG.Cover
    _terminal: Optional[Terminal] = None

    @property
    def node(self) -> KCFG.Node:
        return self.cover.target

    @property
    def terminal(self) -> Optional[Terminal]:
        return self._terminal

    def __str__(self) -> str:
        return f'[Case] {self.label}'


def cfg_tree(cfg: KCFG, label: str, id: str) -> Tree[NodeModel]:
    tree: Tree[NodeModel] = Tree(label, id=id)
    root = tree.root

    indent_model = {Init, Branch, Case}

    waitlist: List[Tuple[TreeNode, NodeModel]] = [(root, Init(init)) for init in cfg.init]
    visited: Set[str] = set()
    while waitlist:
        parent, model = waitlist.pop(0)  # BFS

        allow_expand = type(model) in indent_model and not model.terminal
        current = parent.add(label=str(model), data=model, allow_expand=allow_expand)

        if model.terminal:
            continue

        next_parent = current if type(model) in indent_model else parent

        out_edges = cfg.edges(source_id=model.node.id)
        next_branch = len(out_edges) > 1
        for out_edge in out_edges:
            next_node = out_edge.target
            terminal: Optional[Terminal]
            if cfg.is_stuck(next_node.id):
                terminal = Stuck()
            elif cfg.is_covered(next_node.id):
                cover = cfg.covers(source_id=next_node.id)[0]
                terminal = Cover(cover)
            elif next_node.id in visited:
                terminal = Loop()
            else:
                terminal = None

            next_model: NodeModel
            if next_branch:
                next_model = Branch(in_edge=out_edge, _terminal=terminal)
            else:
                next_model = Step(in_edge=out_edge, _terminal=terminal)

            waitlist.append((next_parent, next_model))
            visited.add(next_node.id)

    return tree


class KcfgViewer(App):
    CSS_PATH = 'style.css'

    _kcfg_file: Path
    _cfg: KCFG
    _printer: Callable[[KCFG, KCFG.Node], str]

    def __init__(self, kcfg_file: Union[str, Path], printer: Optional[Callable[[KCFG, KCFG.Node], str]] = None) -> None:
        kcfg_file = Path(kcfg_file)
        check_file_path(kcfg_file)
        super().__init__()
        self._kcfg_file = kcfg_file
        self._cfg = KCFG.from_dict(json.loads(kcfg_file.read_text()))
        self._printer = printer if printer else lambda cfg, node: '\n'.join(cfg.node_short_info(node))

    def compose(self) -> ComposeResult:
        yield Header()
        yield Horizontal(
            cfg_tree(self._cfg, label=str(self._kcfg_file), id='tree-view'),
            Vertical(
                Static(id='text', expand=True),
                id='text-view',
            ),
        )

    def display_node(self, node: TreeNode) -> None:
        model = node.data
        static = self.query_one('#text', Static)

        if not model:
            static.update('')
            return

        text = self._printer(self._cfg, model.node)
        static.update(text)

    def on_tree_node_selected(self, event: Tree.NodeSelected) -> None:
        node = event.node
        self.display_node(node)
