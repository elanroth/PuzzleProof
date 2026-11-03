"""Lower-bound certificate generator: untrusted, outside the Lean build.

Writes Lean files proving `¬ WinsIn a n R`: the side to move at the root R (the attacker a) cannot
force mate within n of its own moves. With the existing mate certificate this gives an exact
`MateIn`. The search is the one of `measure_minimality.py`: every move of the attacker is searched;
at the defender's turns one escape is chosen, or the defender's own forced mate, which the search
also builds with every reply searched. Stockfish, if given, only orders the defender's candidates
and says where to look for its forced mates.

The output is a directory of Lean files in namespace MODULE:

  * `Moves.lean`: one `Move` definition per move used, named by its UCI writing;
  * `Pos<k>.lean`: the checkpoints, one literal position each, in this library's conventions
    (written by `gen_cert.State`);
  * `N<h>_<k>.lean`: the node theorems, grouped by height in the DAG (children first), so that
    files of one height build in parallel. Each node theorem checks one position: its turn, its
    move list or one move, and one `play` equation per move, all by `decide +kernel`, chained by
    the glue of `Chess.Game.Cert` (sections `PerNode` and `Bounds`);
  * `Claim.lean`: `root_eq : R = p0` and the claim `notWinsIn : ¬ WinsIn a n R`.

Node names: `a<i>` attacker to move (`¬ WinsIn a k P`), `d<i>` defender to move (`¬ WinsIn a k P`,
or for every budget when the defender is stalemated or wins itself), `w<i>` and `b<i>` the
defender's own forced mate (`WinsIn a.other j P`), at its moves and at the attacker's replies.

Move lists come from this library's generator, compiled (`chess-perft --moves`), in the order of
`legalMoves`, and are checked against python-chess as sets. Nothing here is trusted: if the script
is wrong, a Lean file does not compile.

Usage (from the library's root):
  python -I scripts/gen_bound.py --fen FEN --budget N --root LEAN_EXPR --module NAME --out DIR
      [--import MODULE] [--perft PATH] [--stockfish PATH] [--mate-depth J] [--chunk K]
"""
import argparse, collections, os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chess
import chess.engine
from gen_cert import State, move_lean, wrap
from measure_minimality import Prover, INF


class Failure(Exception):
    pass


class Perft:
    """`legalMoves` in the generator's order, from one long-running `chess-perft --moves`."""

    def __init__(self, path):
        self.proc = subprocess.Popen([path, "--moves"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True, bufsize=1)
        self.cache = {}

    def moves(self, st):
        fen = st.fen()
        if fen not in self.cache:
            self.proc.stdin.write(fen + "\n")
            self.proc.stdin.flush()
            line = self.proc.stdout.readline().rstrip("\n")
            read, _, ucis = line.partition("\t")
            if read != fen:
                raise Failure(f"chess-perft read {read!r} for {fen}")
            ms = [chess.Move.from_uci(u) for u in ucis.split()]
            if sorted(m.uci() for m in ms) != sorted(m.uci() for m in st.board.legal_moves):
                raise Failure(f"generators disagree at {fen}")
            self.cache[fen] = ms
        return self.cache[fen]


class Emitter:
    def __init__(self, prover, perft, attacker):
        self.pr, self.perft, self.att = prover, perft, attacker
        self.positions, self.pos_names = [], {}
        self.moves = {}
        self.thms = {}          # name -> (deps, text)
        self.memo = {}          # (kind, state key, budget) -> (name, budget proved)
        self.count = collections.Counter()

    def side(self, white):
        return ".white" if white else ".black"

    def pos(self, st):
        k = st.key()
        if k not in self.pos_names:
            self.pos_names[k] = f"p{len(self.positions)}"
            self.positions.append((self.pos_names[k], st))
        return self.pos_names[k]

    def mv(self, m):
        self.moves.setdefault(m.uci(), move_lean(m))
        return m.uci()

    def new(self, kind, st, budget, deps, doc, claim, proof, key):
        name = f"{kind}{self.count[kind]}"
        self.count[kind] += 1
        self.thms[name] = (deps, f"/-- {doc} -/\ntheorem {name}{claim} :=\n  {proof}\n")
        self.memo[key] = (name, budget)
        return name, budget

    @staticmethod
    def ref(name, have, need):
        """A proof of the bound with budget `need` from node `name`, proved with budget `have`."""
        if have == INF:
            return f"({name} {need})"
        if have == need:
            return name
        return f"(Game.not_winsIn_mono {name} (by decide))"

    @staticmethod
    def wref(name, have, need):
        return name if have == need else f"(Game.Forces.mono {name} (by decide))"

    # The attacker to move: every move refuted. `node` is the search's ("a", epd, n).
    def attacker(self, st, node):
        n = node[2]
        mkey = ("a", st.key(), n)
        if mkey in self.memo:
            return self.memo[mkey]
        P, A = self.pos(st), self.side(self.att)
        claim = f" : ¬ WinsIn {A} {n} {P}"
        if n == 0:
            return self.new("a", st, 0, [], "No budget left.", claim,
                            "Game.not_winsIn_zero_of_turn (by decide +kernel)", mkey)
        kid = dict(self.pr.proof[node][1])
        steps, deps, ms = [], [], self.perft.moves(st)
        for m in ms:
            cst = st.play(m)
            c, have = self.defender(cst, kid[m.uci()])
            deps.append(c)
            steps.append(f"    Game.not_winsIn_forall_mem_cons (by decide +kernel : {P}.play "
                         f"{self.mv(m)} = {self.pos(cst)})\n      {self.ref(c, have, n - 1)} <|\n")
        lst = ", ".join(self.mv(m) for m in ms)
        return self.new(
            "a", st, n, deps, f"{'White' if self.att else 'Black'} to move: every move refuted.",
            claim,
            f"Game.not_winsIn_succ_of_moves_eq (by decide +kernel)\n"
            f"    (by decide +kernel : Game.chess.moves {P} = [{lst}]) <|\n"
            f"{''.join(steps)}    Game.not_winsIn_forall_mem_nil", mkey)

    # The defender to move: one escape, stalemate, no budget, or its own forced mate.
    def defender(self, st, node):
        k = node[2]
        mkey = ("d", st.key(), k)
        if mkey in self.memo:
            return self.memo[mkey]
        _, kind, kids, reply = self.pr.proof[node]
        P, A = self.pos(st), self.side(self.att)
        if kind == "budget 0":
            return self.new("d", st, 0, [], "No budget left for the attacker.",
                            f" : ¬ WinsIn {A} 0 {P}",
                            "Game.not_winsIn_zero_of_defender (by decide +kernel) "
                            "(by decide +kernel)", mkey)
        if kind == "defender stalemated":
            return self.new("d", st, INF, [], "Stalemate.", f" (n : Nat) : ¬ WinsIn {A} n {P}",
                            "Game.not_winsIn_of_stalemate (by decide +kernel)\n"
                            f"    (by decide +kernel : Game.chess.moves {P} = [])", mkey)
        if kind.startswith("defender mates"):
            w, _ = self.mate(st, kids[0])
            return self.new("d", st, INF, [w], "The defender forces mate itself.",
                            f" (n : Nat) : ¬ WinsIn {A} n {P}",
                            f"Game.not_winsIn_of_winsIn_other {w}", mkey)
        m = chess.Move.from_uci(reply)
        cst = st.play(m)
        c, have = self.attacker(cst, kids[0])
        return self.new(
            "d", st, k, [c], f"Escape: {st.board.san(m)}.", f" : ¬ WinsIn {A} {k} {P}",
            f"Game.not_winsIn_of_escape (by decide +kernel) (by decide +kernel)\n"
            f"    (mem_chess_moves.2 (by decide +kernel))\n"
            f"    (by decide +kernel : {P}.play {self.mv(m)} = {self.pos(cst)}) "
            f"{self.ref(c, have, k)}", mkey)

    # The defender's forced mate, at its own move: `WinsIn d j P`, d = the defender.
    def mate(self, st, node):
        j = node[2]
        mkey = ("w", st.key(), j)
        if mkey in self.memo:
            return self.memo[mkey]
        uci, kids = self.pr.proof[node]
        m = chess.Move.from_uci(uci)
        cst = st.play(m)
        b, _ = self.replies(cst, j - 1, dict(kids))
        P, D = self.pos(st), self.side(not self.att)
        return self.new(
            "w", st, j, [b], f"{'White' if not self.att else 'Black'} plays {st.board.san(m)}.",
            f" : WinsIn {D} {j} {P}",
            f"Game.Forces.move_of_play_eq (by decide +kernel) (mem_chess_moves.2 "
            f"(by decide +kernel))\n    (by decide +kernel : {P}.play {self.mv(m)} = "
            f"{self.pos(cst)}) {b}", mkey)

    # Inside that forced mate, the attacker to move: mated, or every reply answered.
    def replies(self, st, j, kid):
        mkey = ("b", st.key(), j)
        if mkey in self.memo:
            return self.memo[mkey]
        P, D = self.pos(st), self.side(not self.att)
        if st.board.is_checkmate():
            return self.new("b", st, j, [], "Checkmate.", f" : WinsIn {D} {j} {P}",
                            "Game.WinsIn.of_mated (by decide +kernel) (by decide +kernel)", mkey)
        steps, deps, ms = [], [], self.perft.moves(st)
        for r in ms:
            cst = st.play(r)
            w, have = self.mate(cst, kid[r.uci()])
            deps.append(w)
            steps.append(f"    Game.Forces.forall_mem_cons (Game.Forces.of_play_eq\n"
                         f"      (by decide +kernel : {P}.play {self.mv(r)} = {self.pos(cst)}) "
                         f"{self.wref(w, have, j)}) <|\n")
        lst = ", ".join(self.mv(r) for r in ms)
        return self.new(
            "b", st, j, deps, "Every reply answered.", f" : WinsIn {D} {j} {P}",
            f"Game.Forces.replies_of_moves_eq (by decide +kernel)\n"
            f"    (by decide +kernel : Game.chess.moves {P} = [{lst}]) <|\n"
            f"{''.join(steps)}    Game.Forces.forall_mem_nil", mkey)


def header(module, imports, doc):
    lines = [f"import {i}" for i in imports]
    return "\n".join(lines) + f"\n\n/-! {doc} -/\n\nnamespace {module}\n\nopen Chess\n\n"


def write(out_dir, module, em, root_name, root_have, root_budget, root_expr, root_imports, chunk,
          att):
    os.makedirs(out_dir, exist_ok=True)
    base = os.path.basename(os.path.normpath(out_dir))
    mod = lambda f: f"{module}.{f}"
    files = {}
    # Moves.
    text = header(module, ["Chess.ChessGame.Fide"], "Generated by `scripts/gen_bound.py`: the moves.")
    text += "".join(f"def {u} : Move := {lit}\n" for u, lit in sorted(em.moves.items()))
    files["Moves"] = text + f"\nend {module}\n"
    # Positions.
    pos_files = []
    for i in range(0, len(em.positions), 2000):
        name = f"Pos{i // 2000}"
        pos_files.append(name)
        text = header(module, ["Chess.ChessGame"],
                      "Generated by `scripts/gen_bound.py`: checkpoints.")
        for pname, st in em.positions[i:i + 2000]:
            text += f"/-- `{st.fen()}` -/\ndef {pname} : Position :=\n  {st.lean()}\n\n"
        files[name] = text + f"end {module}\n"
    # Nodes by height.
    height = {}
    def h(n):
        if n not in height:
            deps = em.thms[n][0]
            height[n] = 1 + max((h(d) for d in deps), default=0)
        return height[n]
    sys.setrecursionlimit(100000)
    for n in em.thms:
        h(n)
    by_h = collections.defaultdict(list)
    for n in em.thms:
        by_h[height[n]].append(n)
    file_of = {}
    node_files = []
    for hh in sorted(by_h):
        names = sorted(by_h[hh], key=lambda s: (s[0], int(s[1:])))
        for c in range(0, len(names), chunk):
            fname = f"N{hh}_{c // chunk}"
            node_files.append((fname, names[c:c + chunk]))
            for n in names[c:c + chunk]:
                file_of[n] = fname
    for fname, names in node_files:
        deps = sorted({file_of[d] for n in names for d in em.thms[n][0]})
        imports = [mod("Moves")] + [mod(p) for p in pos_files] + [mod(d) for d in deps]
        text = header(module, imports, "Generated by `scripts/gen_bound.py`: node theorems.")
        text += "\n".join(wrap(em.thms[n][1]) for n in names)
        files[fname] = text + f"\nend {module}\n"
    # The claim.
    A = ".white" if att else ".black"
    imports = root_imports + [mod(p) for p in pos_files] + [mod(file_of[root_name])]
    text = header(module, imports, "Generated by `scripts/gen_bound.py`: the claim.")
    text += (f"/-- The root is the first checkpoint. -/\ntheorem root_eq : {root_expr} = p0 := by "
             f"decide +kernel\n\n/-- `{root_expr}`: the side to move does not mate within "
             f"{root_budget}. -/\ntheorem notWinsIn : ¬ WinsIn {A} {root_budget} {root_expr} := "
             f"by\n  rw [root_eq]\n  exact {Emitter.ref(root_name, root_have, root_budget)}\n")
    files["Claim"] = text + f"\nend {module}\n"
    for f, text in files.items():
        with open(os.path.join(out_dir, f + ".lean"), "w") as fh:
            fh.write(text)
    return files, height, node_files


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fen", required=True)
    ap.add_argument("--budget", type=int, required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--module", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--import", dest="imports", action="append", default=[])
    ap.add_argument("--perft", default=".lake/build/bin/chess-perft")
    ap.add_argument("--stockfish")
    ap.add_argument("--mate-depth", type=int, default=4)
    ap.add_argument("--chunk", type=int, default=300)
    a = ap.parse_args()
    engine = chess.engine.SimpleEngine.popen_uci(a.stockfish) if a.stockfish else None
    t = time.monotonic()
    try:
        pr = Prover(time.monotonic() + 10**6, engine, a.mate_depth)
        board = chess.Board(a.fen)
        root_node = pr.attacker(board, a.budget)
        if root_node is None:
            sys.exit(f"no certificate: the side to move may mate within {a.budget}")
    finally:
        if engine:
            engine.quit()
    t_search = time.monotonic() - t
    st = State.from_fen(a.fen)
    em = Emitter(pr, Perft(a.perft), board.turn == chess.WHITE)
    em.pos(st)
    root, root_have = em.attacker(st, root_node)
    files, height, node_files = write(a.out, a.module, em, root, root_have, a.budget, a.root,
                                      a.imports or ["Chess.Puzzles"], a.chunk,
                                      board.turn == chess.WHITE)
    print(f"search {t_search:.1f}s; {len(em.thms)} node theorems {dict(em.count)}, "
          f"{len(em.positions)} positions, {len(em.moves)} moves, {len(node_files)} node files, "
          f"height {max(height.values())}; total {time.monotonic() - t:.1f}s")


if __name__ == "__main__":
    main()
