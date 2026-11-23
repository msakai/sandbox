import random

import networkx as nx
from networkx.algorithms import isomorphism as iso

from vf3 import VF3, Graph


def build(
    n: int, p: float, directed: bool, nl: int, el: int, rng: random.Random
) -> tuple[Graph, nx.Graph]:
    g = Graph(n, directed, [rng.randrange(nl) for _ in range(n)])
    G: nx.Graph = (nx.DiGraph if directed else nx.Graph)()
    for i in range(n):
        G.add_node(i, l=g.labels[i])
    for a in range(n):
        for b in range(n):
            if (directed or a < b) and a != b and rng.random() < p:
                lab = rng.randrange(el)
                g.add_edge(a, b, lab)
                G.add_edge(a, b, l=lab)
        if rng.random() < 0.05:
            lab = rng.randrange(el)
            g.add_edge(a, a, lab)
            G.add_edge(a, a, l=lab)
    return g, G


def sub_pattern(
    G: nx.Graph, g_t: Graph, k, directed: bool, rng: random.Random
) -> tuple[Graph, nx.Graph]:
    nodes = rng.sample(range(g_t.n), k)
    idx = {v: i for i, v in enumerate(nodes)}
    p = Graph(k, directed, [g_t.labels[v] for v in nodes])
    P: nx.Graph = (nx.DiGraph if directed else nx.Graph)()
    for v in nodes:
        P.add_node(idx[v], l=g_t.labels[v])
    for a in nodes:
        for b, lab in g_t.out_adj[a].items():
            if b in idx:
                p.add_edge(idx[a], idx[b], lab)
                P.add_edge(idx[a], idx[b], l=lab)
    return p, P


rng = random.Random(1)
total = 0
for trial in range(600):
    directed = trial % 2 == 1
    n = rng.randint(1, 14)
    t, T = build(
        n,
        rng.choice([0.1, 0.3, 0.6]),
        directed,
        rng.randint(1, 3),
        rng.randint(1, 2),
        rng,
    )
    k = rng.randint(0, n)
    if rng.random() < 0.5:
        p, P = sub_pattern(T, t, k, directed, rng)
    else:
        p, P = build(
            k,
            rng.choice([0.2, 0.5]),
            directed,
            rng.randint(1, 3),
            rng.randint(1, 2),
            rng,
        )
    M = (iso.DiGraphMatcher if directed else iso.GraphMatcher)(
        T,
        P,
        node_match=lambda a, b: a["l"] == b["l"],
        edge_match=lambda a, b: a["l"] == b["l"],
    )
    ref = sorted(
        tuple(sorted((pu, tv) for tv, pu in m.items()))
        for m in M.subgraph_isomorphisms_iter()
    )
    got = sorted(tuple(sorted(m.items())) for m in VF3(p, t).match())
    assert ref == got, (trial, len(ref), len(got))
    total += len(ref)
print("OK, 600 cases, total mappings", total)
