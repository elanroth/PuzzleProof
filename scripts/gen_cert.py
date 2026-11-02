"""Certificate generator for this library: untrusted, outside the Lean build.

Stockfish (through python-chess) proposes the attacker's moves and the refutations of alternative
moves; python-chess and this library's own generator (the compiled program `chess-perft`) list the
defender's replies, in the order of `legalMoves`. The output is one Lean file with

  * the certificate as data: one `Cert Move` value per node of the tree (`c0`, `c1`, ...) and the
    claim's certificate `cert` (a `Cert Move`, or an `OnlyMoveCert Move` for an only-move claim);
  * the checkpoints: one literal position per node, `⟨Board.unpack 0x…, turn, castling, ep⟩`,
    written in this library's conventions (the en passant target is set after every two-square
    advance; a castling right is lost when a move leaves or lands on the king's or that rook's home
    square);
  * one small theorem per node (`w0`, `w1`, ...), proved by `decide +kernel` on one move list, one
    move or one checkpoint at a time, and chained by the glue lemmas of `Chess.Game.Cert`;
  * the claims, about the position the caller names (for instance `Puzzles.gotham`): `winsIn`
    and, for an only-move claim, `refutations` (every other move is refuted by a forced mate) and
    `onlyWinningMove`, proved from it.

The file follows the frozen generated-file interface (`docs/spec/Game.md` §4.3,
`scripts/README.md`): it states its claims with `Chess.WinsIn` and `Chess.OnlyWinningMove`, writes
certificates as `Cert` and `OnlyMoveCert` values, names its moves by literal `Move` definitions
(which the file that restates a claim relates to `uci "…"`), and proves claims only with the
per-node glue (`Game.Forces.of_play_eq`,
`Game.Forces.move_of_play_eq`, `Game.Forces.replies_of_moves_eq`, `Game.Forces.forall_mem_cons`,
`Game.Forces.forall_mem_nil`, `Game.WinsIn.of_mated`, `Game.OnlyWinningMove.of_moves_eq`,
`Game.OnlyWinningMove.refuted_cons`, `Game.OnlyWinningMove.refuted_cons_self`,
`Game.OnlyWinningMove.refuted_nil`) and `mem_chess_moves`; at the root of an only-move claim it
moves between `Game.chess.moves R` and the root's explicit move list with `rw` and `▸` along the
equation `moves_root`. It never applies a constructor of `Forces` and names no lemma of core.
Nothing here is trusted: if the script is wrong, the Lean file does not compile.

Usage:
  python -I scripts/gen_cert.py --fen FEN --budget N --root LEAN_EXPR --module NAME --out FILE
      [--only-move UCI] [--import MODULE] [--perft PATH] [--stockfish PATH] [--depth D]
      [--check]

  --fen        the FEN of the root position, in this library's conventions
  --budget     the claim's budget: the attacker (the side to move) mates within N of its own moves
  --root       the Lean expression for the root position in the claims, e.g. Puzzles.gotham
  --module     the Lean namespace of the generated declarations, e.g. ChessDemo.GothamCert
  --only-move  also claim that this move is the only winning move, and refute every other move
  --perft      the compiled program chess-perft (default .lake/build/bin/chess-perft)
  --import     a module that defines the root (repeatable; default Chess.Puzzles)
  --check      after writing, evaluate the certificate with `firstFailureWin` or
               `firstFailureOnlyMove` (interpreted, via `lake env lean`) and print the result

Determinism: Stockfish runs with one thread and fixed-depth searches, so a rerun on the same
Stockfish build gives the same file.
"""
import argparse
import os
import subprocess
import sys
import tempfile

import chess
import chess.engine

# ---------------------------------------------------------------------------------------------
# This library's conventions

#: Piece codes of `Piece.code` (Chess/Position.lean): 1-6 white P N B R Q K, 7-12 black.
CODE = {chess.PAWN: 1, chess.KNIGHT: 2, chess.BISHOP: 3, chess.ROOK: 4, chess.QUEEN: 5,
        chess.KING: 6}
#: `Move.Revokes`: the squares whose leaving or landing costs a castling right, in FEN order
#: K Q k q.
RIGHT_SQUARES = [(chess.E1, chess.H1), (chess.E1, chess.A1), (chess.E8, chess.H8),
                 (chess.E8, chess.A8)]
PROMO = {chess.KNIGHT: ".knight", chess.BISHOP: ".bishop", chess.ROOK: ".rook",
         chess.QUEEN: ".queen"}


def pack(board: chess.Board) -> str:
    """`Board.pack`: the s.index-th hexadecimal digit is the code of what stands on s."""
    n = 0
    for sq in range(64):
        pc = board.piece_at(sq)
        if pc:
            n |= (CODE[pc.piece_type] + (0 if pc.color == chess.WHITE else 6)) << (4 * sq)
    return "0x%064X" % n


class State:
    """A position as this library stores it: the board and turn (a python-chess board, used for
    the engine and for SAN), the four castling flags (K, Q, k, q) and the en passant target."""

    def __init__(self, board: chess.Board, rights, ep):
        self.board = board
        self.rights = tuple(rights)
        self.ep = ep

    @staticmethod
    def from_fen(fen: str) -> "State":
        board = chess.Board(fen)
        fields = fen.split()
        rights = tuple(c in fields[2] for c in "KQkq")
        ep = None if fields[3] == "-" else chess.parse_square(fields[3])
        return State(board, rights, ep)

    def key(self):
        return (pack(self.board), self.board.turn, self.rights, self.ep)

    def fen(self) -> str:
        """The FEN of the position as this library writes it (`Position.toFEN`), clocks 0 1."""
        letters = "".join(c for c, held in zip("KQkq", self.rights) if held) or "-"
        ep = "-" if self.ep is None else chess.square_name(self.ep)
        turn = "w" if self.board.turn == chess.WHITE else "b"
        return f"{self.board.board_fen()} {turn} {letters} {ep} 0 1"

    def play(self, m: chess.Move) -> "State":
        """`Position.play`: the board after the move, castling rights revoked by squares
        (`Move.castlingAfter`), and the en passant target after every two-square advance
        (`Move.epTargetAfter`)."""
        board = self.board.copy(stack=False)
        pawn = board.piece_type_at(m.from_square) == chess.PAWN
        board.push(m)
        rights = tuple(held and m.from_square not in sqs and m.to_square not in sqs
                       for held, sqs in zip(self.rights, RIGHT_SQUARES))
        ep = None
        if pawn and abs(m.to_square - m.from_square) == 16:
            ep = (m.from_square + m.to_square) // 2
        return State(board, rights, ep)

    def lean(self) -> str:
        turn = ".white" if self.board.turn == chess.WHITE else ".black"
        if all(self.rights):
            rights = ".full"
        elif not any(self.rights):
            rights = ".none"
        else:
            rights = "⟨" + ", ".join("true" if r else "false" for r in self.rights) + "⟩"
        ep = "none" if self.ep is None else \
            f"some ⟨{chess.square_file(self.ep)}, {chess.square_rank(self.ep)}⟩"
        return f"⟨Board.unpack {pack(self.board)}, {turn}, {rights}, {ep}⟩"


def move_lean(m: chess.Move) -> str:
    """The move as a `Chess.Move` literal: source and destination as ⟨file, rank⟩."""
    s, t = m.from_square, m.to_square
    promo = "none" if m.promotion is None else f"some {PROMO[m.promotion]}"
    return (f"⟨⟨{chess.square_file(s)}, {chess.square_rank(s)}⟩, "
            f"⟨{chess.square_file(t)}, {chess.square_rank(t)}⟩, {promo}⟩")


# ---------------------------------------------------------------------------------------------
# The generator


class Failure(Exception):
    pass


class Generator:
    def __init__(self, engine, perft, depth):
        self.engine = engine
        self.perft = perft
        self.depth = depth
        self.order_cache = {}
        self.pos_names = {}      # state key -> position name
        self.node_names = {}     # (state key, attacker, budget) -> node index
        self.positions = []      # (name, state)
        self.nodes = []          # Lean text of node theorems, children first
        self.certs = []          # Lean text of certificate definitions, children first
        self.moves = {}          # uci -> literal
        self.stats = {"attacker": 0, "defender": 0, "mate": 0, "engine": 0, "orders": 0}

    # -- this library's generator, compiled ----------------------------------------------------

    def lean_moves(self, st: State):
        """`legalMoves` of the state, in the generator's order, from `chess-perft FEN 1`; checked
        against python-chess's legal moves as a set."""
        fen = st.fen()
        if fen in self.order_cache:
            return self.order_cache[fen]
        self.stats["orders"] += 1
        out = subprocess.run([self.perft, fen, "1"], capture_output=True, text=True, check=True)
        lines = out.stdout.splitlines()
        if lines[0] != f"fen {fen}":
            raise Failure(f"chess-perft read {lines[0]!r} for {fen}")
        ucis = [ln.split()[0] for ln in lines[1:-1]]
        py = sorted(m.uci() for m in st.board.legal_moves)
        if sorted(ucis) != py:
            raise Failure(f"generators disagree at {fen}: {ucis} vs {py}")
        ms = [chess.Move.from_uci(u) for u in ucis]
        self.order_cache[fen] = ms
        return ms

    # -- names -------------------------------------------------------------------------------

    def mv(self, m: chess.Move) -> str:
        u = m.uci()
        self.moves.setdefault(u, move_lean(m))
        return u

    def pos(self, st: State) -> str:
        k = st.key()
        if k not in self.pos_names:
            name = f"p{len(self.positions)}"
            self.pos_names[k] = name
            self.positions.append((name, st))
        return self.pos_names[k]

    # -- the engine ----------------------------------------------------------------------------

    def mating_moves(self, st: State, budget: int):
        """Moves after which the side to move mates within `budget` of its own moves (the move
        itself included), best first: immediate mates in generator order, then Stockfish's."""
        b = st.board
        for m in self.lean_moves(st):
            b.push(m)
            mate = b.is_checkmate()
            b.pop()
            if mate:
                yield m
                return
        seen = set()
        for depth in (2 * budget + 2, 2 * budget + 8, self.depth):
            self.stats["engine"] += 1
            infos = self.engine.analyse(b, chess.engine.Limit(depth=depth, mate=budget),
                                        multipv=3)
            for info in infos:
                s = info["score"].pov(b.turn)
                if s.is_mate() and 0 < s.mate() <= budget and info["pv"][0] not in seen:
                    seen.add(info["pv"][0])
                    yield info["pv"][0]
            if seen:
                return

    def mate_distance(self, st: State) -> int:
        """Stockfish's mate distance for the side to move, in its own moves (positive), or 0."""
        self.stats["engine"] += 1
        info = self.engine.analyse(st.board, chess.engine.Limit(depth=self.depth))
        s = info["score"].pov(st.board.turn)
        return s.mate() if s.is_mate() and s.mate() > 0 else 0

    # -- nodes ---------------------------------------------------------------------------------

    def attacker(self, st: State, a: bool, budget: int) -> int:
        """A node where the attacker `a` is to move and mates within `budget`; returns its index.
        Emits the node's theorem `w<i>` and certificate `c<i>`."""
        key = (st.key(), a, budget)
        if key in self.node_names:
            return self.node_names[key]
        if budget <= 0:
            raise Failure(f"no budget left: {st.fen()}")
        last = None
        for m in self.mating_moves(st, budget):
            child_st = st.play(m)
            try:
                child = self.defender(child_st, a, budget - 1)
            except Failure as e:
                last = e
                continue
            self.stats["attacker"] += 1
            P, Q, u = self.pos(st), self.pos(child_st), self.mv(m)
            i = self.emit(
                f"/-- {self.name(a)} to move plays {st.board.san(m)}. -/",
                f"WinsIn {self.side(a)} {budget} {P}",
                f"Game.Forces.move_of_play_eq (by decide +kernel) (mem_chess_moves.2 "
                f"(by decide +kernel))\n    (by decide +kernel : {P}.play {u} = {Q}) w{child}",
                f".move {u} c{child}")
            self.node_names[key] = i
            return i
        raise last or Failure(f"no mate in {budget} found: {st.fen()}")

    def defender(self, st: State, a: bool, budget: int) -> int:
        """A node where the defender (not `a`) is to move and `a` mates within `budget`."""
        key = (st.key(), a, budget)
        if key in self.node_names:
            return self.node_names[key]
        P = self.pos(st)
        if st.board.is_checkmate():
            self.stats["mate"] += 1
            i = self.emit(f"/-- {self.name(not a)} is checkmated. -/",
                          f"WinsIn {self.side(a)} {budget} {P}",
                          "Game.WinsIn.of_mated (by decide +kernel) (by decide +kernel)", ".goal")
            self.node_names[key] = i
            return i
        ms = self.lean_moves(st)
        if not ms:
            raise Failure(f"stalemate: {st.fen()}")
        children = []
        for m in ms:
            child_st = st.play(m)
            children.append((m, child_st, self.attacker(child_st, a, budget)))
        self.stats["defender"] += 1
        lst = ", ".join(self.mv(m) for m, _, _ in children)
        steps = "".join(
            f"    Game.Forces.forall_mem_cons (Game.Forces.of_play_eq\n"
            f"      (by decide +kernel : {P}.play {self.mv(m)} = {self.pos(cs)}) w{c}) <|\n"
            for m, cs, c in children)
        sans = ", ".join(st.board.san(m) for m, _, _ in children)
        i = self.emit(
            f"/-- {self.name(not a)} to move, with the replies {sans}. -/",
            f"WinsIn {self.side(a)} {budget} {P}",
            f"Game.Forces.replies_of_moves_eq (by decide +kernel)\n"
            f"    (by decide +kernel : Game.chess.moves {P} = [{lst}]) <|\n"
            f"{steps}    Game.Forces.forall_mem_nil",
            ".replies [" + ", ".join(f"({self.mv(m)}, c{c})" for m, _, c in children) + "]")
        self.node_names[key] = i
        return i

    def emit(self, doc, claim, proof, cert) -> int:
        i = len(self.nodes)
        self.nodes.append(f"{doc}\ntheorem w{i} : {claim} :=\n  {proof}\n")
        self.certs.append(f"def c{i} : Cert Move := {cert}\n")
        return i

    @staticmethod
    def side(a: bool) -> str:
        return ".white" if a == chess.WHITE else ".black"

    @staticmethod
    def name(a: bool) -> str:
        return "White" if a == chess.WHITE else "Black"


# ---------------------------------------------------------------------------------------------
# The file


def wrap(text: str, width: int = 100) -> str:
    """Breaks every line longer than `width` after a comma, continuing four columns further in."""
    out = []
    for line in text.split("\n"):
        indent = " " * (len(line) - len(line.lstrip()) + 4)
        while len(line) > width:
            cut = line.rfind(", ", 0, width - 1)
            if cut <= len(indent):
                break
            out.append(line[:cut + 1])
            line = indent + line[cut + 2:]
        out.append(line)
    return "\n".join(out)


def header(args, gen, sf_name):
    claim = (f"`{args.only_move}` is the only winning move and the side to move mates within "
             f"{args.budget}" if args.only_move else
             f"the side to move mates within {args.budget}")
    st = gen.stats
    imports = "\n".join(f"import {m}" for m in ["Chess.ChessGame.Fide"] + args.imports)
    return f"""{imports}

/-!
# Generated certificate: {args.module}

Generated by `scripts/gen_cert.py` (do not edit; regenerate) for the claim that in
`{args.root}`, the position with FEN
`{args.fen}`,
{claim}.

The engine was {sf_name}, with python-chess {chess.__version__}; neither is trusted. Every fact
below is checked by the kernel (`decide +kernel`), one move list, one move or one checkpoint at a
time.

Nodes: {st['attacker']} attacker, {st['defender']} defender and {st['mate']} mate leaves; \
{len(gen.positions)} positions.

## Contents

* One `Move` per move of the tree, named by its UCI writing.
* The checkpoints `p<i>`: each position of the tree as a literal, in this library's conventions.
* The theorems `w<i>`, one per node, children first: what the node claims, proved from its
  children with the glue lemmas of `Chess.Game.Cert`.
* The certificate as data: `c<i>` per node, and `cert` for the claim (for `firstFailureWin`,
  `firstFailureOnlyMove` and `checkWin`/`checkOnlyMove`).
* The claims `winsIn` (and, for an only-move claim, `moves_root`, `refutations` and
  `onlyWinningMove`), about `{args.root}`.
-/

namespace {args.module}

open Chess
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--fen", required=True)
    ap.add_argument("--budget", type=int, required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--module", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only-move")
    ap.add_argument("--perft", default=".lake/build/bin/chess-perft")
    ap.add_argument("--stockfish", default="stockfish")
    ap.add_argument("--depth", type=int, default=30)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--import", dest="imports", action="append", default=None)
    args = ap.parse_args()
    args.imports = args.imports or ["Chess.Puzzles"]

    engine = chess.engine.SimpleEngine.popen_uci(args.stockfish)
    engine.configure({"Threads": 1, "Hash": 64})
    sf_name = engine.id.get("name", "Stockfish")
    gen = Generator(engine, args.perft, args.depth)
    root = State.from_fen(args.fen)
    a = root.board.turn
    if root.fen() != " ".join(args.fen.split()[:4]) + " 0 1":
        sys.exit(f"the FEN is not in this library's canonical form: {root.fen()}")

    claims = []
    root_ms = gen.lean_moves(root)
    R, N = args.root, args.budget
    if args.only_move:
        best = chess.Move.from_uci(args.only_move)
        if best not in root_ms:
            sys.exit(f"{args.only_move} is not legal")
    else:
        best = next(iter(gen.mating_moves(root, N)))
    p0 = gen.pos(root)  # the root as a literal, for the interpreted check
    after = root.play(best)
    w_after = gen.defender(after, a, N - 1)
    P1, B = gen.pos(after), gen.mv(best)
    claims.append(
        f"/-- Playing `{B}` ({root.board.san(best)}) at `{R}` gives the checkpoint `{P1}`. -/\n"
        f"theorem play_best : {R}.play {B} = {P1} := by decide +kernel\n\n"
        f"/-- `{R}`: {gen.name(a)} mates within {N}. -/\n"
        f"theorem winsIn : WinsIn {gen.side(a)} {N} {R} :=\n"
        f"  Game.Forces.move_of_play_eq (by decide +kernel) "
        f"(mem_chess_moves.2 (by decide +kernel))\n"
        f"    play_best w{w_after}\n")
    refs = []
    if args.only_move:
        steps = []
        for m in root_ms:
            if m == best:
                steps.append("    Game.OnlyWinningMove.refuted_cons_self <|\n")
                continue
            st = root.play(m)
            k = gen.mate_distance(st)
            if k == 0:
                sys.exit(f"{root.board.san(m)} is not refuted by a forced mate")
            w = gen.attacker(st, not a, k)
            refs.append((m, w, k))
            u = gen.mv(m)
            claims.append(
                f"/-- After `{u}` ({root.board.san(m)}), {gen.name(not a)} mates within {k}. -/\n"
                f"theorem refutes_{u} : WinsIn {gen.side(not a)} {k} ({R}.play {u}) :=\n"
                f"  Game.Forces.of_play_eq (by decide +kernel : {R}.play {u} = {gen.pos(st)}) "
                f"w{w}\n")
            steps.append(f"    Game.OnlyWinningMove.refuted_cons refutes_{u} <|\n")
        lst = ", ".join(gen.mv(m) for m in root_ms)
        claims.append(
            f"/-- The moves available at `{R}`, in the order of `legalMoves`. -/\n"
            f"theorem moves_root : Game.chess.moves {R} = [{lst}] := by decide +kernel\n")
        claims.append(
            f"/-- `{R}`: after every move other than `{B}`, {gen.name(not a)} forces mate. -/\n"
            f"theorem refutations : ∀ m ∈ Game.chess.moves {R}, m ≠ {B} →\n"
            f"    ∃ k, WinsIn {gen.side(not a)} k ({R}.play m) := by\n"
            f"  rw [moves_root]\n"
            f"  exact\n"
            + "".join(steps) + "    Game.OnlyWinningMove.refuted_nil\n")
        claims.append(
            f"/-- `{R}`: `{B}` is the only winning move. -/\n"
            f"theorem onlyWinningMove : OnlyWinningMove {R} {B} :=\n"
            f"  Game.OnlyWinningMove.of_moves_eq (by decide +kernel) moves_root "
            f"(by decide +kernel)\n"
            f"    (Game.Forces.of_play_eq play_best w{w_after}) (moves_root ▸ refutations)\n")
        ref_budget = max(k for _, _, k in refs)
        cert = (f"/-- The only-move certificate: the win after `{B}` and the refutations. -/\n"
                f"def cert : OnlyMoveCert Move where\n  next := c{w_after}\n"
                f"  refBudget := {ref_budget}\n  refs := ["
                + ", ".join(f"({gen.mv(m)}, c{w})" for m, w, _ in refs) + "]\n")
    else:
        cert = (f"/-- The win certificate of the claim. -/\n"
                f"def cert : Cert Move := .move {B} c{w_after}\n")

    moves = "".join(f"def {u} : Move := {lit}\n" for u, lit in sorted(gen.moves.items()))
    positions = "".join(f"/-- `{st.fen()}` -/\ndef {name} : Position :=\n  {st.lean()}\n\n"
                        for name, st in gen.positions)
    text = (header(args, gen, sf_name)
            + "\n/-! ## Moves -/\n\n" + moves
            + "\n/-! ## Checkpoints -/\n\n" + positions
            + "/-! ## Nodes, children first -/\n\n" + "\n".join(gen.nodes)
            + "\n/-! ## The certificate as data -/\n\n" + "".join(gen.certs) + "\n" + cert
            + "\n/-! ## The claims -/\n\n" + "\n".join(claims)
            + f"\nend {args.module}\n")
    text = wrap(text)
    with open(args.out, "w") as f:
        f.write(text)
    print(f"wrote {args.out}: {gen.stats}, {len(gen.positions)} positions, "
          f"{len(gen.moves)} moves", file=sys.stderr)
    engine.quit()

    if args.check:
        check(args, text, p0, B)


def check(args, text, p0, best):
    """Evaluates the certificate with the untrusted diagnostics, interpreted: `none` means the
    checker accepts it. Runs on the literal root `p0`, not on the claim's expression, because a
    board read from a FEN is slow to read in interpreted code."""
    body = text.split("/-! ## Nodes, children first -/")[0]
    certs = text.split("/-! ## The certificate as data -/")[1].split("/-! ## The claims -/")[0]
    if args.only_move:
        ev = (f"#eval Game.chess.firstFailureOnlyMove {args.budget} {p0} {best} cert")
    else:
        side = ".white" if chess.Board(args.fen).turn == chess.WHITE else ".black"
        ev = f"#eval Game.chess.firstFailureWin {side} {args.budget} {p0} cert"
    src = body + certs + ev + f"\n\nend {args.module}\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(src)
    out = subprocess.run(["lake", "env", "lean", f.name], capture_output=True, text=True)
    os.unlink(f.name)
    print("check:", (out.stdout + out.stderr).strip(), file=sys.stderr)


if __name__ == "__main__":
    main()
