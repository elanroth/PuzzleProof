"""Measure the proof tree for "the attacker cannot force mate within n" (the lower half of MateIn).

Untrusted tooling, outside the Lean build: it only counts.

Usage (from the library's root):
  python -I scripts/measure_minimality.py [--fen FEN] [--max-budget N] [--time-limit SECONDS]
      [--stockfish PATH] [--mate-depth J] [--out FILE.json]

For each budget n = 1, ..., N it builds a certificate for `¬ WinsIn a n p`, where a is the side to
move at p (Black, at the Gotham position), reading `WinsIn` as `Chess.Game.Forces` does:

  * at a node where a is to move with budget n (an attacker node), every legal move of a is
    refuted, each with budget n - 1 at the defender node it reaches; with budget 0 there is
    nothing to refute. Every move is searched here, whatever any engine thinks of it;
  * at a node where the defender is to move with budget k (a defender node), the attacker has won
    if the defender is checkmated. Otherwise one of these closes it:
      - the defender has no legal move (stalemate), or k = 0;
      - the defender forces mate itself within J moves (then the attacker cannot force mate:
        no position is a forced win for both sides, Game.not_wins_of_winsIn_other). That forced
        win is built here too, with every reply of the attacker searched;
      - one reply, after which the attacker node is refuted with budget k.

Stockfish (if given) only orders the defender's candidate moves and says which positions to try
the forced mate on. It cannot make anything pass: a reply it suggests is kept only if the search
above refutes every attacker move after it.

Positions are shared: a position refuted with budget n is refuted for every smaller budget, so a
certificate is a DAG. For each n the script prints the DAG's size (the positions a Lean file would
need, one theorem each), the size of the same certificate written out as a tree, how the leaves
close, how many legal moves the attacker nodes list in all (each is a `decide +kernel` fact in
Lean), and the time taken. The JSON written with --out has the same numbers and the positions with
the most parents in the DAG.
"""
import argparse, collections, json, time
import chess
import chess.engine

GOTHAM = "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"
INF = 10**6


class OutOfTime(Exception):
    pass


class Prover:
    """The search. Every proof is a node `(tag, position, budget)` whose proof is stored once and
    never changed: "a" the attacker to move, "d" the defender to move (both: the attacker does not
    win within the budget), "m" the defender, to move, mates within the budget. A node refers only
    to nodes completed before it, so the certificate is a DAG."""

    def __init__(self, deadline, engine, mate_depth):
        self.deadline, self.engine, self.mate_depth = deadline, engine, mate_depth
        self.calls = 0
        # Per position: the largest budget refuted so far (INF: every budget), the smallest found
        # not refutable, and the smallest forced-mate distance found.
        self.att_ok, self.dfd_ok, self.att_bad, self.dfd_bad, self.mate_best = {}, {}, {}, {}, {}
        # Per node: ("att", [(move, child)]), ("dfd", kind, [child], reply or None), or for "m"
        # nodes (move, [(reply, child)]).
        self.proof = {}
        self.hints = {}

    def tick(self):
        self.calls += 1
        if self.calls % 1000 == 0 and time.monotonic() > self.deadline:
            raise OutOfTime()

    def hint(self, b):
        """Stockfish's best move and mate distance (for the side to move), or (None, None)."""
        if self.engine is None:
            return None, None
        key = b.epd()
        if key not in self.hints:
            info = self.engine.analyse(b, chess.engine.Limit(depth=12))
            pv, score = info.get("pv"), info["score"].relative
            self.hints[key] = (pv[0] if pv else None, score.mate() if score.is_mate() else None)
        return self.hints[key]

    def finish(self, node, proof, table):
        self.proof[node] = proof
        table[node[1]] = max(table.get(node[1], -1), node[2])
        return node

    # The side to move forces mate within j of its own moves, every reply searched.
    def mate_within(self, b, j):
        self.tick()
        key = b.epd()
        if self.mate_best.get(key, INF) <= j:
            return ("m", key, self.mate_best[key])
        if j == 0:
            return None
        best, _ = self.hint(b) if j >= 2 else (None, None)
        for m in sorted(b.legal_moves, key=lambda m: (m != best, not b.gives_check(m))):
            b.push(m)
            if b.is_checkmate():
                b.pop()
                return self.record_mate(("m", key, 1), (m.uci(), []))
            ok, kids = j > 1 and any(True for _ in b.legal_moves), []
            if ok:
                for r in list(b.legal_moves):
                    b.push(r)
                    c = self.mate_within(b, j - 1)
                    b.pop()
                    if c is None:
                        ok = False
                        break
                    kids.append((r.uci(), c))
            b.pop()
            if ok:
                return self.record_mate(("m", key, j), (m.uci(), kids))
        return None

    def record_mate(self, node, proof):
        self.proof[node] = proof
        self.mate_best[node[1]] = min(self.mate_best.get(node[1], INF), node[2])
        return node

    def attacker(self, b, n):
        self.tick()
        key = b.epd()
        if self.att_ok.get(key, -1) >= n:
            return ("a", key, self.att_ok[key])
        if self.att_bad.get(key, INF) <= n:
            return None
        if n == 0:
            return self.finish(("a", key, 0), ("att", []), self.att_ok)
        kids = []
        for m in list(b.legal_moves):
            b.push(m)
            c = self.defender(b, n - 1)
            b.pop()
            if c is None:
                self.att_bad[key] = min(self.att_bad.get(key, INF), n)
                return None
            kids.append((m.uci(), c))
        return self.finish(("a", key, n), ("att", kids), self.att_ok)

    def defender(self, b, k):
        self.tick()
        key = b.epd()
        if self.dfd_ok.get(key, -1) >= k:
            return ("d", key, self.dfd_ok[key])
        if self.dfd_bad.get(key, INF) <= k:
            return None
        if b.is_checkmate():
            self.dfd_bad[key] = 0
            return None
        def done(kind, kids, budget=INF, move=None):
            return self.finish(("d", key, budget), ("dfd", kind, kids, move), self.dfd_ok)
        if not any(True for _ in b.legal_moves):
            return done("defender stalemated", [])
        if k == 0:
            return done("budget 0", [], 0)
        c = self.mate_within(b, 1)
        if c:
            return done("defender mates in 1", [c])
        best, mate = self.hint(b)
        if mate is not None and 0 < mate <= self.mate_depth:
            c = self.mate_within(b, mate)
            if c:
                return done(f"defender mates in {c[2]}", [c])
        for m in sorted(b.legal_moves, key=lambda m: (m != best, not b.gives_check(m))):
            b.push(m)
            c = self.attacker(b, k)
            b.pop()
            if c:
                return done("one reply", [c], k, m.uci())
        self.dfd_bad[key] = min(self.dfd_bad.get(key, INF), k)
        return None

    def kids(self, node):
        pr = self.proof[node]
        if node[0] == "m":
            return [c for _, c in pr[1]]
        return [c for _, c in pr[1]] if pr[0] == "att" else pr[2]

    def certificate(self, root):
        """The DAG reachable from the root: its nodes, tree size, leaves, listed moves, in-degrees."""
        seen, indeg, leaves, listed = set(), collections.Counter(), collections.Counter(), 0
        order, stack = [], [root]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            order.append(node)
            pr = self.proof[node]
            if node[0] == "m" or pr[0] == "att":
                listed += len(pr[1])
            else:
                leaves[pr[1]] += 1
            for c in self.kids(node):
                indeg[c] += 1
                stack.append(c)
        size = {}
        def tree(node):
            if node not in size:
                size[node] = 1 + sum(tree(c) for c in self.kids(node))
            return size[node]
        tree(root)
        return {"dag_nodes": len(seen), "dag_mate_nodes": sum(1 for s in seen if s[0] == "m"),
                "dag_positions": len({s[1] for s in seen}),
                "tree_nodes": size[root], "moves_listed": listed, "leaves": dict(leaves),
                "most_parents": [(c, k[0], k[1], k[2]) for k, c in indeg.most_common(8)]}


def measure(fen, n, limit, engine, mate_depth):
    p = Prover(time.monotonic() + limit, engine, mate_depth)
    t = time.monotonic()
    try:
        root = p.attacker(chess.Board(fen), n)
        ok = root is not None
    except OutOfTime:
        root, ok = None, None
    row = {"budget": n, "refuted": ok, "seconds": round(time.monotonic() - t, 1),
           "search_calls": p.calls}
    if ok:
        row.update(p.certificate(root))
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fen", default=GOTHAM)
    ap.add_argument("--max-budget", type=int, default=10)
    ap.add_argument("--time-limit", type=float, default=600)
    ap.add_argument("--stockfish")
    ap.add_argument("--mate-depth", type=int, default=4)
    ap.add_argument("--out")
    a = ap.parse_args()
    engine = chess.engine.SimpleEngine.popen_uci(a.stockfish) if a.stockfish else None
    rows = []
    try:
        for n in range(1, a.max_budget + 1):
            r = measure(a.fen, n, a.time_limit, engine, a.mate_depth)
            rows.append(r)
            print(f"n={n:2} refuted={r['refuted']} {r['seconds']:>7}s "
                  f"dag={r.get('dag_nodes')} (mate {r.get('dag_mate_nodes')}) tree={r.get('tree_nodes')} "
                  f"moves_listed={r.get('moves_listed')} leaves={r.get('leaves')}", flush=True)
            if a.out:
                json.dump({"fen": a.fen, "stockfish": bool(a.stockfish), "mate_depth": a.mate_depth,
                           "rows": rows}, open(a.out, "w"), indent=1)
            if r["refuted"] is not True:
                break
    finally:
        if engine:
            engine.quit()


if __name__ == "__main__":
    main()
