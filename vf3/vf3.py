"""
VF3 の簡易 Python 実装

参考文献:
  V. Carletti, P. Foggia, A. Saggese, M. Vento,
  "Introducing VF3: A New Algorithm for Subgraph Isomorphism",
  GbRPR 2017, LNCS 10310, pp. 128-139.

論文の定義 (Sect. 2.1) に従い、「誘導」部分グラフ同型を扱う:
  M: V1 -> V2 は単射で、辺の有無 (とラベル) を両方向とも保存する。

実装している論文の要素:
  * 探索順序 N_G1 の計算 (Sect. 2.2): d_M → P_f (式 (1)) → 次数 の順に比較
  * G1 側の状態空間の事前計算 (Sect. 3.1, Algorithm 1):
      - parent tree
      - 各ノードが T1 に属するレベルを区間 [enter, leave) として O(N1) で保持
      - 各レベルの候補 u_n について、先読み規則で使う近傍カウントも前計算
  * 候補選択 (Sect. 3.2, Algorithm 2, 式 (8)(9)):
      parent が写された G2 ノードの近傍のうち、未対応で同じクラスのもの
  * 実行可能性規則 (Sect. 2.3):
      F_s (ノード/辺ラベル), F_c (core rule, 式 (3)),
      F_la1 (式 (4)(5)), F_la2 (式 (6)(7))
      有向グラフでは入辺・出辺を分けて数える。
  * クラス分け関数 ψ はノードラベル。

簡略化している点:
  * 探索は Python のジェネレータ + 明示的スタックによる深さ優先探索。
  * T2 は「対応済みノードと隣接する未対応ノード」の集合を、隣接する対応済み
    ノード数のカウンタで動的に管理する。
  * 候補ノード v_n について、次数 (入・出) が u_n 以上であることを安価な
    事前フィルタとして追加で確認している (正当性には影響しない)。
"""

from __future__ import annotations

from collections import Counter, defaultdict
from collections.abc import Collection, Hashable, Iterator
from dataclasses import dataclass


class Graph[NodeLabel: Hashable, EdgeLabel: Hashable]:
    """ノードラベル・辺ラベル付きの単純グラフ (有向/無向)。

    ノードは 0..n-1 の整数。無向グラフでは辺を両方向に格納する。
    out_adj[u][v] / in_adj[v][u] に辺ラベルを持つ。
    """

    def __init__(
        self,
        n: int,
        directed: bool = False,
        labels: list[NodeLabel | None] | None = None,
    ) -> None:
        self.n = n
        self.directed = directed
        self.labels: list[NodeLabel | None] = (
            list(labels) if labels is not None else [None] * n
        )
        if len(self.labels) != n:
            raise ValueError("labels の長さがノード数と一致しません")
        self.out_adj: list[dict[int, EdgeLabel | None]] = [{} for _ in range(n)]
        self.in_adj: list[dict[int, EdgeLabel | None]] = [{} for _ in range(n)]

    def add_edge(self, u: int, v: int, label: EdgeLabel | None = None) -> None:
        self.out_adj[u][v] = label
        self.in_adj[v][u] = label
        if not self.directed:
            self.out_adj[v][u] = label
            self.in_adj[u][v] = label

    def neighbors(self, u: int) -> set[int]:
        """方向を無視した隣接ノード集合 (自己ループは除く)。"""
        s = set(self.out_adj[u]) | set(self.in_adj[u])
        s.discard(u)
        return s

    def out_degree(self, u: int) -> int:
        return len(self.out_adj[u])

    def in_degree(self, u: int) -> int:
        return len(self.in_adj[u])

    def degree(self, u: int) -> int:
        return len(self.neighbors(u))


# ---------------------------------------------------------------------------
# 前処理
# ---------------------------------------------------------------------------


def compute_order[NodeLabel: Hashable, EdgeLabel: Hashable](
    g1: Graph[NodeLabel, EdgeLabel], g2: Graph[NodeLabel, EdgeLabel]
) -> list[int]:
    """探索順序 N_G1 を計算する (Sect. 2.2)。

    1. d_M(u): 既に順序に入ったノードとの辺数 (大きい方を優先)
    2. P_f(u) = P_l(λ(u)) * Σ_{d' >= d(u)} P_d(d') (式 (1), 小さい=稀な方を優先)
    3. 次数 (大きい方を優先)
    残りの同点は決定的にノード番号で決める (論文ではランダム)。
    """
    n2 = max(g2.n, 1)
    label_freq = Counter(g2.labels)
    deg_freq = Counter(g2.degree(v) for v in range(g2.n))
    max_deg = max(deg_freq) if deg_freq else 0
    # 次数 d 以上の確率 (累積)
    tail = [0.0] * (max_deg + 2)
    for d in range(max_deg, -1, -1):
        tail[d] = tail[d + 1] + deg_freq.get(d, 0) / n2

    deg1 = [g1.degree(u) for u in range(g1.n)]

    def p_f(u: int) -> float:
        p_l = label_freq.get(g1.labels[u], 0) / n2
        d = deg1[u]
        p_d = tail[d] if d <= max_deg else 0.0
        return p_l * p_d

    pf = [p_f(u) for u in range(g1.n)]
    nbrs = [g1.neighbors(u) for u in range(g1.n)]
    d_m = [0] * g1.n
    in_seq = [False] * g1.n
    order: list[int] = []
    # 簡易実装: 毎回線形走査 (O(N1^2))
    for _ in range(g1.n):
        best = None
        best_key = None
        for u in range(g1.n):
            if in_seq[u]:
                continue
            key = (-d_m[u], pf[u], -deg1[u], u)
            if best_key is None or key < best_key:
                best, best_key = u, key
        assert best is not None
        order.append(best)
        in_seq[best] = True
        for w in nbrs[best]:
            if not in_seq[w]:
                d_m[w] += 1
    return order


type _Cls = int


@dataclass(slots=True)
class _Level[NodeLabel: Hashable, EdgeLabel: Hashable]:
    """レベル k (= 状態の対応数が k) で追加される u_n = N_G1[k] に関する前計算情報。"""

    cls: _Cls
    core_in: list[tuple[int, Hashable]]
    core_out: list[tuple[int, Hashable]]
    in_deg: int
    la1_in: dict[_Cls, int]
    la1_out: dict[_Cls, int]
    la2_in: dict[_Cls, int]
    la2_out: dict[_Cls, int]
    out_deg: int
    parent: int | None
    parent_is_pred: bool
    self_loop: tuple[int, Hashable]
    u: int


class VF3[NodeLabel: Hashable, EdgeLabel: Hashable]:
    def __init__(
        self, pattern: Graph[NodeLabel, EdgeLabel], target: Graph[NodeLabel, EdgeLabel]
    ) -> None:
        if pattern.directed != target.directed:
            raise ValueError("pattern と target の有向/無向が一致していません")
        self.g1 = pattern
        self.g2 = target
        self.directed = pattern.directed

        # クラス分け関数 ψ: ノードラベル → 整数クラス
        cls_of_label: dict[NodeLabel | None, _Cls] = {}
        for lab in list(pattern.labels) + list(target.labels):
            if lab not in cls_of_label:
                cls_of_label[lab] = len(cls_of_label)
        self.cls1 = [cls_of_label[l] for l in pattern.labels]
        self.cls2 = [cls_of_label[l] for l in target.labels]

        self.order = compute_order(pattern, target)
        self.levels = self._preprocess()

        # G2 のクラス別ノードリスト (R2 の列挙用)
        self.nodes2_by_cls: dict[_Cls, list[int]] = defaultdict(list)
        for v in range(target.n):
            self.nodes2_by_cls[self.cls2[v]].append(v)

    # -- Algorithm 1: PreprocessGraph -------------------------------------
    def _preprocess(self) -> list[_Level]:
        g1 = self.g1
        n1 = g1.n
        pos = [0] * n1
        for i, u in enumerate(self.order):
            pos[u] = i

        # parent tree と T1 の区間表現。
        # u は レベル k で T1 に属する  ⇔  t_enter[u] <= k <= pos[u]
        # (k <= pos[u] で未対応、t_enter[u] <= k で対応済みノードに隣接)
        parent: list[int | None] = [None] * n1
        t_enter = [n1 + 1] * n1
        for i, u in enumerate(self.order):
            for w in g1.neighbors(u):
                if pos[w] > i and t_enter[w] > n1:
                    t_enter[w] = i + 1  # レベル i+1 から T1 に入る
                    parent[w] = u
        self.t1_interval = [(t_enter[u], pos[u]) for u in range(n1)]
        self.parent = parent
        self.pos = pos

        levels: list[_Level[NodeLabel, EdgeLabel]] = []
        for k, u in enumerate(self.order):
            # 先読み規則用カウント: レベル k の状態 s_c に対して
            #   T1  : t_enter[w] <= k <= pos[w]  (かつ w != u)
            #   V1~ : k < t_enter[w] (つまり未対応かつ非隣接)
            la1_out, la1_in, la2_out, la2_in = (
                Counter[_Cls](),
                Counter[_Cls](),
                Counter[_Cls](),
                Counter[_Cls](),
            )
            for w in g1.out_adj[u]:
                if w == u or pos[w] < k:
                    continue
                if t_enter[w] <= k:
                    la1_out[self.cls1[w]] += 1
                else:
                    la2_out[self.cls1[w]] += 1
            if self.directed:
                for w in g1.in_adj[u]:
                    if w == u or pos[w] < k:
                        continue
                    if t_enter[w] <= k:
                        la1_in[self.cls1[w]] += 1
                    else:
                        la2_in[self.cls1[w]] += 1

            L = _Level[NodeLabel, EdgeLabel](
                u=u,
                cls=self.cls1[u],
                parent=parent[u],
                # u が parent の出辺先 (parent -> u) かどうか
                parent_is_pred=(p := parent[u]) is not None and u in g1.out_adj[p],
                out_deg=g1.out_degree(u),
                in_deg=g1.in_degree(u),
                self_loop=(u in g1.out_adj[u], g1.out_adj[u].get(u)),
                # core rule で使う「既に対応済みの近傍」(レベル k の状態では pos < k)
                core_out=[
                    (w, lab)
                    for w, lab in g1.out_adj[u].items()
                    if w != u and pos[w] < k
                ],
                core_in=[
                    (w, lab) for w, lab in g1.in_adj[u].items() if w != u and pos[w] < k
                ],
                la1_out=dict(la1_out),
                la1_in=dict(la1_in),
                la2_out=dict(la2_out),
                la2_in=dict(la2_in),
            )

            levels.append(L)

        return levels

    # -- マッチング ---------------------------------------------------------
    def match(self) -> Iterator[dict[int, int]]:
        """すべての (誘導) 部分グラフ同型写像 {pattern ノード: target ノード} を列挙する。"""
        g1, g2 = self.g1, self.g2
        n1 = g1.n
        if n1 == 0:
            yield {}
            return
        if n1 > g2.n:
            return

        core1 = [-1] * n1  # μ
        core2 = [-1] * g2.n  # μ^{-1}
        t2_cnt = [0] * g2.n  # 対応済み近傍の個数 (>0 かつ未対応 ⇒ T2)
        nbrs2 = [g2.neighbors(v) for v in range(g2.n)]

        def add_pair(u: int, v: int) -> None:
            core1[u] = v
            core2[v] = u
            for w in nbrs2[v]:
                t2_cnt[w] += 1

        def remove_pair(u: int, v: int) -> None:
            core1[u] = -1
            core2[v] = -1
            for w in nbrs2[v]:
                t2_cnt[w] -= 1

        # Algorithm 2: SelectCandidate (候補 v_n の列挙)
        def candidates(L: _Level) -> Iterator[int]:
            pool: Collection[int]
            if L.parent is None:
                pool = self.nodes2_by_cls.get(L.cls, ())  # 式 (8)
            else:
                v_tilde = core1[L.parent]  # μ(Parent(u_n))
                if L.parent_is_pred:
                    pool = g2.out_adj[v_tilde]  # 式 (9)
                else:
                    pool = g2.in_adj[v_tilde]
            for v in pool:
                if core2[v] == -1 and self.cls2[v] == L.cls:
                    yield v

        def feasible(L: _Level, v: int) -> bool:
            _u = L.u
            # 安価な次数フィルタ
            if g2.out_degree(v) < L.out_deg or g2.in_degree(v) < L.in_deg:
                return False
            # F_s: ノードラベル (クラス = ラベルなので候補選択で保証済み) と自己ループ
            has_loop, loop_lab = L.self_loop
            if has_loop != (v in g2.out_adj[v]):
                return False
            if has_loop and g2.out_adj[v][v] != loop_lab:
                return False
            # F_c (式 (3)) + 辺ラベルの F_s
            out2 = g2.out_adj[v]
            for w, lab in L.core_out:
                vw = core1[w]
                if vw not in out2 or out2[vw] != lab:
                    return False
            if self.directed:
                in2 = g2.in_adj[v]
                for w, lab in L.core_in:
                    vw = core1[w]
                    if vw not in in2 or in2[vw] != lab:
                        return False
            # 逆方向: v の対応済み近傍がすべて u の近傍の像であること。
            # 上で u 側の像が全部 v の近傍に含まれることを確認済みなので個数比較で十分。
            # 同時に先読み規則のための G2 側カウントもここで集計する。
            cnt_core_out = 0
            la1_out, la2_out = Counter[int](), Counter[int]()
            for w in out2:
                if w == v:
                    continue
                if core2[w] != -1:
                    cnt_core_out += 1
                elif t2_cnt[w] > 0:
                    la1_out[self.cls2[w]] += 1
                else:
                    la2_out[self.cls2[w]] += 1
            if cnt_core_out != len(L.core_out):
                return False
            if self.directed:
                cnt_core_in = 0
                la1_in, la2_in = Counter[int](), Counter[int]()
                for w in g2.in_adj[v]:
                    if w == v:
                        continue
                    if core2[w] != -1:
                        cnt_core_in += 1
                    elif t2_cnt[w] > 0:
                        la1_in[self.cls2[w]] += 1
                    else:
                        la2_in[self.cls2[w]] += 1
                if cnt_core_in != len(L.core_in):
                    return False
            # F_la1 (式 (4)(5)) と F_la2 (式 (6)(7))、クラスごと
            for c, k in L.la1_out.items():
                if la1_out.get(c, 0) < k:
                    return False
            for c, k in L.la2_out.items():
                if la2_out.get(c, 0) < k:
                    return False
            if self.directed:
                for c, k in L.la1_in.items():
                    if la1_in.get(c, 0) < k:
                        return False
                for c, k in L.la2_in.items():
                    if la2_in.get(c, 0) < k:
                        return False
            return True

        # 明示的スタックによる深さ優先探索 (再帰上限を避ける)
        levels = self.levels
        stack: list[
            tuple[int, Iterator[int], int]
        ] = []  # (level, 候補イテレータ, 現在の v)
        stack.append((0, candidates(levels[0]), -1))
        while stack:
            k, it, prev_v = stack.pop()
            L = levels[k]
            if prev_v != -1:
                remove_pair(L.u, prev_v)  # バックトラック
            for v in it:
                if feasible(L, v):
                    add_pair(L.u, v)
                    if k + 1 == n1:  # ゴール状態
                        yield {u: core1[u] for u in range(n1)}
                        remove_pair(L.u, v)
                        continue
                    stack.append((k, it, v))
                    stack.append((k + 1, candidates(levels[k + 1]), -1))
                    break


def subgraph_isomorphisms(pattern: Graph, target: Graph) -> Iterator[dict[int, int]]:
    """pattern から target への誘導部分グラフ同型をすべて列挙する。"""
    return VF3(pattern, target).match()


def has_subgraph_isomorphism(pattern: Graph, target: Graph) -> bool:
    return next(subgraph_isomorphisms(pattern, target), None) is not None


if __name__ == "__main__":
    # 例: 三角形 (ラベル A,B,C) を探す
    p = Graph[str, None](3, labels=["A", "B", "C"])
    p.add_edge(0, 1)
    p.add_edge(1, 2)
    p.add_edge(2, 0)

    t = Graph[str, None](6, labels=["A", "B", "C", "A", "B", "C"])
    for a, b in [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3), (0, 4)]:
        t.add_edge(a, b)

    vf3 = VF3(p, t)
    print("探索順序 N_G1:", vf3.order)
    print("parent tree :", vf3.parent)
    for m in vf3.match():
        print(m)
