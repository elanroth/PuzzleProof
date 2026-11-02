"""Job files for perft_diff.py. Untrusted tooling, outside the Lean build.

  python perft_jobs.py std DEPTH OUT.tsv            the six standard positions (and Position 4
                                                     mirrored) at depths 1..DEPTH
  python perft_jobs.py stdat DEPTH OUT.tsv [LABEL..] the same positions at depth DEPTH only, or
                                                     only those named (labels as in STD)
  python perft_jobs.py named DEPTH OUT.tsv          the 16 named test positions of ChessTest/Rules
                                                     and ChessTest/MoveGen (see NAMED)
  python perft_jobs.py rand N DEPTH SEED OUT.tsv    N positions reached by random play from the
                                                     initial position (1 to 120 plies), half
                                                     written with every en passant target
  python perft_jobs.py ep N DEPTH SEED OUT.tsv      N positions just after a double push, half
                                                     with an en passant capture available
  python perft_jobs.py special N DEPTH SEED OUT.tsv N positions with a promotion or castling move
"""

import random, sys
import chess
STD = [
 ("initial", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"),
 ("kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"),
 ("position3", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1"),
 ("position4", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1"),
 ("position4mirrored", "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1"),
 ("position5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"),
 ("position6", "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10"),
]
# The named test positions of ChessTest/Rules.lean and ChessTest/MoveGen.lean (castleRookPos at
# files 3 and 4), as written by this library's Position.toFEN: the output of
#   #eval IO.println <| "\n".intercalate <| ([("foolsMate", foolsMate), ...] :
#     List (String × Position)).map fun (n, p) => s!"{n}\t{p.toFEN}"
# in a file importing ChessTest.MoveGen and Chess.ChessGame (regenerated 2026-11-02).
NAMED = [
 ("foolsMate", "rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 0 1"),
 ("castlePos", "1r2kr2/8/8/8/8/8/8/R3K2R w KQ - 0 1"),
 ("blackCastlePos", "4k2r/8/8/8/8/8/8/4K3 b k - 0 1"),
 ("castleRookPos3", "1k6/3r4/8/8/8/8/8/R3K2R w KQ - 0 1"),
 ("castleRookPos4", "1k6/4r3/8/8/8/8/8/R3K2R w KQ - 0 1"),
 ("epPos", "4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 1"),
 ("epPinPos", "7k/8/8/KPp4r/8/8/8/8 w - c6 0 1"),
 ("kingsPos", "8/8/8/8/8/4k3/8/4K3 w - - 0 1"),
 ("promoPos", "r3k2r/1P6/8/8/8/8/8/4K3 w kq - 0 1"),
 ("blackPromoPos", "4k2K/8/8/8/8/8/p7/8 b - - 0 1"),
 ("pinPos", "k3r3/8/8/8/8/8/4B3/4K3 w - - 0 1"),
 ("blackEpPos", "4k3/8/8/8/3pP3/8/8/4K3 b - e3 0 1"),
 ("rookAttackedPos", "k6r/8/8/8/8/8/8/4K2R w K - 0 1"),
 ("defendedPos", "4k3/8/8/7b/8/8/4r3/4K3 w - - 0 1"),
 ("epCheckPos", "k7/8/8/3pP3/4K3/8/8/8 w - d6 0 1"),
 ("promoKnightPos", "N3k2r/8/8/8/8/8/8/4K3 b k - 0 1"),
]

def std(depth, out):
    with open(out, "w") as f:
        for d in range(1, depth + 1):
            for label, fen in STD:
                f.write(f"{label}\t{fen}\t{d}\tfen\n")

def stdat(depth, out, labels):
    with open(out, "w") as f:
        for label, fen in STD:
            if not labels or label in labels:
                f.write(f"{label}\t{fen}\t{depth}\tfen\n")

def named(depth, out):
    with open(out, "w") as f:
        for label, fen in NAMED:
            f.write(f"{label}\t{fen}\t{depth}\tfen\n")

def rand(n, depth, seed, out):
    rng = random.Random(seed)
    with open(out, "w") as f:
        k = 0
        while k < n:
            b = chess.Board()
            plies = rng.randint(1, 120)
            for _ in range(plies):
                moves = list(b.legal_moves)
                if not moves:
                    break
                b.push(rng.choice(moves))
            mode = "fen" if k % 2 == 0 else "legal"
            f.write(f"random{k:03d}_ply{b.ply()}\t{b.fen(en_passant=mode)}\t{depth}\t{mode}\n")
            k += 1

def gen(kind, n, depth, seed, out):
    rng = random.Random(seed)
    with open(out, "w") as f:
        k = tries = 0
        while k < n:
            tries += 1
            b = chess.Board()
            for _ in range(rng.randint(2, 150)):
                moves = list(b.legal_moves)
                if not moves:
                    break
                b.push(rng.choice(moves))
                if kind == "ep":
                    want_capture = (k % 2 == 0)
                    if b.ep_square is not None and b.has_legal_en_passant() == want_capture:
                        break
                else:
                    lm = list(b.legal_moves)
                    if any(m.promotion for m in lm) or any(b.is_castling(m) for m in lm):
                        break
            ok = (b.ep_square is not None) if kind == "ep" else any(
                m.promotion or b.is_castling(m) for m in b.legal_moves)
            if not ok:
                continue
            f.write(f"{kind}{k:03d}_ply{b.ply()}\t{b.fen(en_passant='fen')}\t{depth}\tfen\n")
            k += 1

if __name__ == "__main__":
    kind = sys.argv[1]
    if kind == "std":
        std(int(sys.argv[2]), sys.argv[3])
    elif kind == "stdat":
        unknown = set(sys.argv[4:]) - {label for label, _ in STD}
        if unknown:
            sys.exit(f"unknown labels: {sorted(unknown)}")
        stdat(int(sys.argv[2]), sys.argv[3], sys.argv[4:])
    elif kind == "named":
        named(int(sys.argv[2]), sys.argv[3])
    elif kind == "rand":
        rand(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    else:
        gen(kind, int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
