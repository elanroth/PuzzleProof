"""Differential perft test: the program chess-perft (this library, compiled) against python-chess.

Untrusted tooling, outside the Lean build. Build the program first: lake build chess-perft.

For each (FEN, depth) job: run `chess-perft FEN depth`, parse the FEN line, the divide and the
total; compute the same divide with python-chess; compare
  * the four position fields of the FEN line against python-chess's
    board.fen(en_passant="fen") (only when the input FEN was written that way),
  * the set of moves in the divide, and each move's count,
  * the total (which chess-perft prints as the sum of its divide).
Usage: python perft_diff.py .lake/build/bin/chess-perft JOBS.tsv OUT.jsonl
JOBS.tsv lines: label<TAB>fen<TAB>depth<TAB>epmode, where epmode is "fen" when the FEN writes every
en passant target (python-chess's board.fen(en_passant="fen"), this library's convention) and
"legal" otherwise; the FEN fields are compared only in the first case. Make job files with
perft_jobs.py. Prints each disagreement and a final count; exit code 1 if any.
"""
import json, subprocess, sys, time
import chess

def perft(board, depth):
    if depth == 0:
        return 1
    if depth == 1:
        return board.legal_moves.count()
    n = 0
    for m in board.legal_moves:
        board.push(m)
        n += perft(board, depth - 1)
        board.pop()
    return n

def py_divide(fen, depth):
    board = chess.Board(fen)
    out = {}
    for m in board.legal_moves:
        board.push(m)
        out[m.uci()] = perft(board, depth - 1)
        board.pop()
    return out

def lean_run(exe, fen, depth):
    t = time.time()
    r = subprocess.run([exe, fen, str(depth)], capture_output=True, text=True)
    dt = time.time() - t
    if r.returncode != 0:
        return None, r.stderr.strip(), dt
    lines = r.stdout.strip().split("\n")
    assert lines[0].startswith("fen ")
    fen_out = lines[0][4:]
    tot_line = lines[-1].split()
    assert tot_line[0] == "perft" and int(tot_line[1]) == depth
    div = {}
    for ln in lines[1:-1]:
        u, c = ln.split()
        if u in div:
            return None, f"move listed twice: {u}", dt
        div[u] = int(c)
    return (fen_out, div, int(tot_line[2])), None, dt

def main():
    exe, jobs, outp = sys.argv[1:4]
    n_ok = n_bad = 0
    with open(jobs) as f, open(outp, "w") as out:
        for line in f:
            if not line.strip():
                continue
            label, fen, depth, epmode = line.rstrip("\n").split("\t")
            depth = int(depth)
            res, err, dt_lean = lean_run(exe, fen, depth)
            t = time.time()
            pyd = py_divide(fen, depth)
            dt_py = time.time() - t
            pytot = sum(pyd.values())
            rec = {"label": label, "fen": fen, "depth": depth, "py_total": pytot,
                   "lean_s": round(dt_lean, 3), "py_s": round(dt_py, 3)}
            problems = []
            if res is None:
                problems.append("lean error: " + err)
            else:
                fen_out, div, tot = res
                rec["lean_total"] = tot
                if tot != pytot:
                    problems.append(f"total {tot} != {pytot}")
                if set(div) != set(pyd):
                    problems.append(f"moves only in lean {sorted(set(div)-set(pyd))}, "
                                    f"only in python {sorted(set(pyd)-set(div))}")
                for u in set(div) & set(pyd):
                    if div[u] != pyd[u]:
                        problems.append(f"divide {u}: {div[u]} != {pyd[u]}")
                py4 = " ".join(chess.Board(fen).fen(en_passant="fen").split()[:4])
                rec["fen_fields_equal"] = fen_out.split()[:4] == py4.split()
                if epmode == "fen" and not rec["fen_fields_equal"]:
                    problems.append(f"fen fields {fen_out} vs {py4}")
            rec["ok"] = not problems
            rec["problems"] = problems
            out.write(json.dumps(rec) + "\n")
            out.flush()
            if problems:
                n_bad += 1
                print("MISMATCH", label, fen, depth, problems, flush=True)
            else:
                n_ok += 1
    print(f"agree: {n_ok}, disagree: {n_bad}")
    sys.exit(1 if n_bad else 0)

if __name__ == "__main__":
    main()
