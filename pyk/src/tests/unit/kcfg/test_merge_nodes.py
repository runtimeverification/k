from networkx import Graph, find_cliques


def test_networkx() -> None:
    g = Graph()
    edges = [['A', 'B'], ['A', 'C'], ['A', 'D'], ['B', 'C'], ['B', 'D']]
    g.add_edges_from(edges)

    cliques = list(find_cliques(g))
    sorted_cliques = sorted([sorted(clique) for clique in cliques])
    expected_cliques = sorted([sorted(['A', 'B', 'C']), sorted(['A', 'B', 'D'])])
    assert sorted_cliques == expected_cliques, sorted_cliques

    g.clear()
    edges = [['A', 'B'], ['A', 'C'], ['A', 'D'], ['B', 'C'], ['B', 'D'], ['C', 'D']]
    g.add_edges_from(edges)
    cliques = list(find_cliques(g))
    sorted_cliques = sorted([sorted(clique) for clique in cliques])
    expected_cliques = sorted([sorted(['A', 'B', 'C', 'D'])])
    assert sorted_cliques == expected_cliques, sorted_cliques
