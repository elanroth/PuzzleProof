"""Untrusted certificate generator: Stockfish picks the attacker's moves, python-chess
enumerates every defender reply, and the result is written as a Lean `Cert` term.

Nothing here is trusted. Lean's `check` re-derives every legal move and every mate itself.

usage: gen_cert.py <out.lean> <name> <fen> <budget> [--only-move]
"""
import sys, chess, chess.engine

ENGINE = chess.engine.SimpleEngine.popen_uci("stockfish")
stats = {"nodes": 0, "attacker": 0, "defender": 0, "mates": 0, "engine_calls": 0}
cache = {}


def lean_move(m: chess.Move) -> str:
    return f"⟨{m.from_square}, {m.to_square}, {m.promotion or 0}⟩"


def mating_move(b: chess.Board, budget: int) -> chess.Move:
    """A move that mates within `budget` attacker moves (immediate mates first)."""
    for m in b.legal_moves:
        b.push(m)
        mate = b.is_checkmate()
        b.pop()
        if mate:
            return m
    for depth in (2 * budget + 2, 2 * budget + 8, 40):
        stats["engine_calls"] += 1
        info = ENGINE.analyse(b, chess.engine.Limit(depth=depth, mate=budget, time=20))
        s = info["score"].pov(b.turn)
        if s.is_mate() and 0 < s.mate() <= budget:
            return info["pv"][0]
    raise RuntimeError(f"no mate in {budget} found: {b.fen()}")


def attacker(b: chess.Board, budget: int, ind: int) -> str:
    """Cert for a position where the attacker is to move."""
    key = (b.fen(), budget)
    if key in cache:
        return cache[key]
    m = mating_move(b, budget)
    stats["nodes"] += 1
    stats["attacker"] += 1
    san = b.san(m)
    b.push(m)
    rest = defender(b, budget - 1, ind + 1)
    b.pop()
    pad = "  " * ind
    out = f"/- {san} -/ .att {lean_move(m)}\n{pad}  ({rest})"
    cache[key] = out
    return out


def defender(b: chess.Board, budget: int, ind: int) -> str:
    stats["nodes"] += 1
    if b.is_checkmate():
        stats["mates"] += 1
        return ".mate"
    if budget <= 0 or not any(True for _ in b.legal_moves):
        raise RuntimeError(f"line fails: {b.fen()}")
    stats["defender"] += 1
    pad = "  " * ind
    items = []
    for m in b.legal_moves:
        san = b.san(m)
        b.push(m)
        items.append(f"(/- {san} -/ {lean_move(m)},\n{pad}  {attacker(b, budget, ind + 1)})")
        b.pop()
    return ".dfd [\n" + pad + ("\n" + pad + ", ").join(items) + "]"


def main():
    out, name, fen, budget = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    only = "--only-move" in sys.argv
    b = chess.Board(fen)
    lines = ["import ChessProof.Cert", "", "namespace ChessProof", "set_option maxRecDepth 100000", ""]
    if not only:
        lines.append(f"def {name} : Cert :=\n  {attacker(b, budget, 1)}\n")
    else:
        best = mating_move(b, budget)
        print("best:", b.san(best))
        b.push(best)
        lines.append(f"def {name}_move : Move := {lean_move(best)}\n")
        lines.append(f"def {name}_cert : Cert :=\n  {defender(b, budget - 1, 1)}\n")
        b.pop()
        refs = []
        for m in b.legal_moves:
            if m == best:
                continue
            san = b.san(m)
            b.push(m)
            info = ENGINE.analyse(b, chess.engine.Limit(depth=24, time=20))
            s = info["score"].pov(b.turn)
            if not (s.is_mate() and s.mate() > 0):
                raise RuntimeError(f"{san} is not refuted by a forced mate (score {s})")
            refs.append(f"(/- {san} -/ {lean_move(m)},\n    {attacker(b, s.mate(), 2)})")
            b.pop()
        lines.append(f"def {name}_refutations : List (Move × Cert) := [\n    "
                     + "\n  , ".join(refs) + "]\n")
    lines.append("end ChessProof\n")
    open(out, "w").write("\n".join(lines))
    print(stats)
    ENGINE.quit()


main()
