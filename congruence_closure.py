"""
Claude (Sonnet 5) の書いた Downey-Sethi-Tarjan (1980) 型の congruence closure。

- backtracking なし
- explanation (proof) 生成なし
- ground term のみ(変数・E-matching は扱わない)

計算量: 要素数を n として amortized O(n log n)
  (union-by-size + "小さい方の use-list だけ再ハッシュする" small-to-large trick)

項の表現:
    アトム            :  "a", 1, ("const", "zero") など、任意のハッシュ可能な値
    関数適用 f(t1..tn) :  (functor, t1, t2, ..., tn) というタプル
        例: ("f", "a")            -> f(a)
            ("f", ("f", "a"))     -> f(f(a))
"""

from __future__ import annotations

from collections.abc import Hashable
from typing import Any

type NodeId = int


class CongruenceClosure:
    def __init__(self) -> None:
        # union-find 本体
        self._parent: list[NodeId] = []
        self._size: list[int] = []

        # ノードの構造情報(root/非root問わず全ノードに定義される)
        self._func: list[Any] = []  # アトムなら値そのもの、関数適用なら functor
        self._args: list[tuple[NodeId, ...]] = []  # アトムなら ()

        # root ノードについてのみ有効な補助情報
        self._uselist: list[list[NodeId]] = []
        self._members: list[list[NodeId]] = []

        # signature -> 代表項ノード(root である必要はない)
        self._sigtable: dict[tuple, NodeId] = {}

        # hash-consing 用: 元の term オブジェクト -> node id
        self._node_of: dict[Hashable, NodeId] = {}

        self._pending: list[tuple[NodeId, NodeId]] = []

    # ------------------------------------------------------------------
    # 項の登録(hash-consing しつつ内部ノードを構築)
    # ------------------------------------------------------------------
    def add_term(self, term: Hashable) -> NodeId:
        """term を登録し、その node id を返す。既出なら既存の id を返す。"""
        existing = self._node_of.get(term)
        if existing is not None:
            return existing

        if isinstance(term, tuple) and len(term) >= 1:
            functor, *subterms = term
            arg_ids = tuple(self.add_term(t) for t in subterms)
        else:
            functor, arg_ids = term, ()

        nid = self._new_node(functor, arg_ids)
        self._node_of[term] = nid
        self._propagate()
        return nid

    def _new_node(self, functor: Any, args: tuple[NodeId, ...]) -> NodeId:
        nid = len(self._parent)
        self._parent.append(nid)
        self._size.append(1)
        self._uselist.append([])
        self._members.append([nid])
        self._func.append(functor)
        self._args.append(args)

        # 自分自身を、各引数(の現在の root)の use-list に登録
        for a in args:
            self._uselist[self.find(a)].append(nid)

        # 関数適用ノードなら signature を計算し、既存と衝突するか確認
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
    # union-find コア
    # ------------------------------------------------------------------
    def find(self, x: NodeId) -> NodeId:
        root = x
        while self._parent[root] != root:
            root = self._parent[root]
        while self._parent[x] != root:  # 経路圧縮
            self._parent[x], x = root, self._parent[x]
        return root

    def are_equal(self, a: NodeId, b: NodeId) -> bool:
        return self.find(a) == self.find(b)

    def class_members(self, x: NodeId) -> list[NodeId]:
        """x と同じ eclass に属する全ノード id のリスト。"""
        return self._members[self.find(x)]

    def representative_term(self, x: NodeId) -> NodeId:
        """x の eclass の代表元ノード id(単なる root)。"""
        return self.find(x)

    # ------------------------------------------------------------------
    # 等式のマージ(外部から a = b を主張するときのエントリポイント)
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

            # サイズが小さい方 (rb) を大きい方 (ra) に吸収する
            if self._size[ra] < self._size[rb]:
                ra, rb = rb, ra

            self._parent[rb] = ra
            self._size[ra] += self._size[rb]
            self._members[ra].extend(self._members[rb])

            # --- ここが DST のキモ: 吸収される側 (rb) の use-list だけを ---
            # --- 再ハッシュする。ra 側の use-list はキー(root id)が   ---
            # --- 変化していないので触らなくてよい。                    ---
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
    # デバッグ用
    # ------------------------------------------------------------------
    def term_of(self, nid: NodeId) -> Any:
        """node id から (functor, arg-terms...) 形式に戻す(表示用)。"""
        if not self._args[nid]:
            return self._func[nid]
        return (self._func[nid], *(self.term_of(a) for a in self._args[nid]))


if __name__ == "__main__":
    cc = CongruenceClosure()

    def f(x: Hashable) -> Hashable:
        return ("f", x)

    a = "a"
    cc.merge(cc.add_term(f(f(f(a)))), cc.add_term(a))
    cc.merge(cc.add_term(f(f(f(f(f(a)))))), cc.add_term(a))
    assert cc.are_equal(cc.add_term(f(a)), cc.add_term(a))
