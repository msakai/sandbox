"""
Downey-Sethi-Tarjan (1980) style congruence closure, based on a version
written by Claude (Sonnet 5) with minor modifications.

- no backtracking
- no explanation (proof) generation
- ground terms only (no variables / E-matching)

Complexity: amortized O(n log n) where n is the number of elements
  (union-by-size + the "small-to-large" trick of only rehashing the
  smaller side's use-list)

Term representation:
    Function symbol f : any hashable value, e.g. "a", 1, ("const", "zero")
    Atom              : Term.constant(f)
    Application f(t1..tn) : Term.apply(f, (t1, t2, ..., tn))
        e.g. Term.apply("f", Term.constant("a"))                  -> f(a)
             Term.apply("f", Term.apply("f", Term.constant("a"))) -> f(f(a))
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass

type NodeId = int


@dataclass(frozen=True)
class Term[F: Hashable]:
    functor: F
    subterms: tuple[Term[F], ...]

    @staticmethod
    def constant(c: F) -> Term[F]:
        return Term(c, ())

    @staticmethod
    def apply(f: F, *args: Term[F]) -> Term[F]:
        return Term(f, args)


class CongruenceClosure[F]:
    def __init__(self) -> None:
        # core union-find
        self._parent: list[NodeId] = []
        self._size: list[int] = []

        # structural info for every node (root or not)
        self._func: list[F] = []  # functor
        self._args: list[tuple[NodeId, ...]] = []  # () for atoms

        # auxiliary info that is only valid for root nodes
        self._uselist: list[list[NodeId]] = []
        self._members: list[list[NodeId]] = []

        # signature -> representative application node (need not be a root)
        self._sigtable: dict[tuple, NodeId] = {}

        # for hash-consing: original Term object -> node id
        self._node_of: dict[Term[F], NodeId] = {}

        self._pending: list[tuple[NodeId, NodeId]] = []

    # ------------------------------------------------------------------
    # Registering a term (builds internal nodes with hash-consing)
    # ------------------------------------------------------------------
    def add_term(self, term: Term[F]) -> NodeId:
        """Register term and return its node id. Returns the existing id if already registered."""
        existing = self._node_of.get(term)
        if existing is not None:
            return existing

        arg_ids = tuple(self.add_term(t) for t in term.subterms)

        nid = self._new_node(term.functor, arg_ids)
        self._node_of[term] = nid
        self._propagate()
        return nid

    def _new_node(self, functor: F, args: tuple[NodeId, ...]) -> NodeId:
        nid = len(self._parent)
        self._parent.append(nid)
        self._size.append(1)
        self._uselist.append([])
        self._members.append([nid])
        self._func.append(functor)
        self._args.append(args)

        # register this node in the use-list of each argument's current root
        for a in args:
            self._uselist[self.find(a)].append(nid)

        # for an application node, compute its signature and check for a collision
        if args:
            sig = self._signature(nid)
            existing = self._sigtable.get(sig)
            if existing is None:
                self._sigtable[sig] = nid
            elif existing != nid:
                self._pending.append((nid, existing))

        return nid

    def _signature(self, nid: NodeId) -> tuple:
        return (self._func[nid], tuple(self.find(a) for a in self._args[nid]))

    # ------------------------------------------------------------------
    # union-find core
    # ------------------------------------------------------------------
    def find(self, x: NodeId) -> NodeId:
        root = x
        while self._parent[root] != root:
            root = self._parent[root]
        while self._parent[x] != root:  # path compression
            self._parent[x], x = root, self._parent[x]
        return root

    def are_equal(self, a: NodeId, b: NodeId) -> bool:
        return self.find(a) == self.find(b)

    def class_members(self, x: NodeId) -> list[NodeId]:
        """List of all node ids in the same eclass as x."""
        return self._members[self.find(x)]

    def representative_term(self, x: NodeId) -> NodeId:
        """Node id of the representative of x's eclass (just the root)."""
        return self.find(x)

    # ------------------------------------------------------------------
    # Merging an equation (entry point for asserting a = b from outside)
    # ------------------------------------------------------------------
    def merge(self, a: NodeId, b: NodeId) -> None:
        self._pending.append((a, b))
        self._propagate()

    def _propagate(self) -> None:
        while self._pending:
            a, b = self._pending.pop()
            ra, rb = self.find(a), self.find(b)
            if ra == rb:
                continue

            # absorb the smaller class (rb) into the larger one (ra)
            if self._size[ra] < self._size[rb]:
                ra, rb = rb, ra

            self._parent[rb] = ra
            self._size[ra] += self._size[rb]
            self._members[ra].extend(self._members[rb])

            # --- This is the core DST trick: only rehash the use-list of ---
            # --- the absorbed side (rb). The use-list on the ra side is  ---
            # --- untouched since its keys (root ids) haven't changed.    ---
            moved = self._uselist[rb]
            self._uselist[rb] = []
            self._uselist[ra].extend(moved)

            for p in moved:
                sig = self._signature(p)
                q = self._sigtable.get(sig)
                if q is None:
                    self._sigtable[sig] = p
                elif self.find(p) != self.find(q):
                    self._pending.append((p, q))

    # ------------------------------------------------------------------
    # For debugging
    # ------------------------------------------------------------------
    def term_of(self, nid: NodeId) -> Term[F]:
        """Convert a NodeId back into a Term (for display)."""
        return Term(self._func[nid], tuple(self.term_of(a) for a in self._args[nid]))


if __name__ == "__main__":
    cc = CongruenceClosure[str]()

    def f(x: Term[str]) -> Term[str]:
        return Term.apply("f", x)

    a = Term.constant("a")
    cc.merge(cc.add_term(f(f(f(a)))), cc.add_term(a))
    cc.merge(cc.add_term(f(f(f(f(f(a)))))), cc.add_term(a))
    assert cc.are_equal(cc.add_term(f(a)), cc.add_term(a))
