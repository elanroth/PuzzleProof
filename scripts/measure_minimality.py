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
    def __init__(self, deadline, engine, mate_depth):
        self.deadline, self.engine, self.mate_depth = deadline, engine, mate_depth
        self.calls = 0
        # Refutations: key -> budget refuted (INF when it holds for every budget), and the proof:
        # ("att", [child keys]) or ("dfd", kind, [child keys]).
        self.att_ok, self.dfd_ok, self.att_bad, self.dfd_bad = {}, {}, {}, {}
        self.proof = {}
        # The defender's own forced mates: key -> (j, [child keys]) or None.
        self.mates = {}
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

    # The side to move forces mate within j of its own moves (every reply searched).
    def mate_within(self, b, j):
        self.tick()
        key = ("m", b.epd())
        if key in self.mates and self.mates[key] is not None and self.mates[key][0] <= j:
            return True
        if j == 0:
            return False
        best, _ = self.hint(b) if j >= 2 else (None, None)
        moves = sorted(b.legal_moves, key=lambda m: (m != best, not b.gives_check(m)))
        for m in moves:
            b.push(m)
            if b.is_checkmate():
                b.pop()
                self.mates[key] = (1, [])
                return True
            ok, kids = j > 1 and any(True for _ in b.legal_moves), []
            if ok:
                for r in list(b.legal_moves):
                    b.push(r)
                    ok = self.mate_within(b, j - 1)
                    if ok:
                        kids.append(("m", b.epd()))
                    b.pop()
                    if not ok:
                        break
            b.pop()
            if ok:
                self.mates[key] = (j, kids)
                return True
        return False

    def attacker(self, b, n):
        self.tick()
        key = ("a", b.epd())
        if self.att_ok.get(key, -1) >= n:
            return True
        if self.att_bad.get(key, INF) <= n:
            return False
        if n == 0:
            self.att_ok[key], self.proof[key] = 0, ("att", [])
            return True
        kids = []
        for m in list(b.legal_moves):
            b.push(m)
            ok = self.defender(b, n - 1)
            kids.append(("d", b.epd()))
            b.pop()
            if not ok:
                self.att_bad[key] = min(self.att_bad.get(key, INF), n)
                return False
        self.att_ok[key], self.proof[key] = n, ("att", kids)
        return True

    def defender(self, b, k):
        self.tick()
        key = ("d", b.epd())
        if self.dfd_ok.get(key, -1) >= k:
            return True
        if self.dfd_bad.get(key, INF) <= k:
            return False
        if b.is_checkmate():
            self.dfd_bad[key] = 0
            return False
        def done(kind, kids, budget=INF):
            self.dfd_ok[key], self.proof[key] = budget, ("dfd", kind, kids)
            return True
        if not any(True for _ in b.legal_moves):
            return done("defender stalemated", [])
        if k == 0:
            return done("budget 0", [], 0)
        if self.mate_within(b, 1):
            return done("defender mates in 1", [("m", b.epd())])
        best, mate = self.hint(b)
        if mate is not None and 0 < mate <= self.mate_depth and self.mate_within(b, mate):
            return done(f"defender mates in {mate}", [("m", b.epd())])
        moves = sorted(b.legal_moves, key=lambda m: (m != best, not b.gives_check(m)))
        for m in moves:
            b.push(m)
            ok = self.attacker(b, k)
            child = ("a", b.epd())
            b.pop()
            if ok:
                return done("one reply", [child], k)
        self.dfd_bad[key] = min(self.dfd_bad.get(key, INF), k)
        return False

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
            if node[0] == "m":
                kids = self.mates[node][1]
                listed += len(kids)
            else:
                pr = self.proof[node]
                kids = pr[1] if pr[0] == "att" else pr[2]
                if pr[0] == "att":
                    listed += len(kids)
                else:
                    leaves[pr[1]] += 1
            for c in kids:
                indeg[c] += 1
                stack.append(c)
        size = {}
        for node in reversed(order):
            kids = self.mates[node][1] if node[0] == "m" else (
                self.proof[node][1] if self.proof[node][0] == "att" else self.proof[node][2])
            size[node] = 1 + sum(size.get(c, 1) for c in kids)
        return {"dag_nodes": len(seen), "dag_mate_nodes": sum(1 for s in seen if s[0] == "m"),
                "tree_nodes": size[root], "moves_listed": listed, "leaves": dict(leaves),
                "most_parents": [(c, k[0], k[1]) for k, c in indeg.most_common(8)]}


def measure(fen, n, limit, engine, mate_depth):
    p = Prover(time.monotonic() + limit, engine, mate_depth)
    t = time.monotonic()
    try:
        ok = p.attacker(chess.Board(fen), n)
    except OutOfTime:
        ok = None
    row = {"budget": n, "refuted": ok, "seconds": round(time.monotonic() - t, 1),
           "search_calls": p.calls}
    if ok:
        row.update(p.certificate(("a", chess.Board(fen).epd())))
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
