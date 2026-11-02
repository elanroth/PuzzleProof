# scripts/

Untrusted tooling, outside the Lean build. Nothing here is trusted: a wrong script produces a Lean
file that does not compile, or a test that fails, never a false theorem.

| Script | What it does |
|---|---|
| `gen_cert.py` | Writes a certificate file for a forced-win or only-move claim (Stockfish proposes, Lean checks). |
| `perft_jobs.py`, `perft_diff.py` | The differential perft test of `chess-perft` against python-chess (`docs/process/ChessTest.md`). |
| `check_docstrings.py` | Checks that the docstring of every definition and instance under `Chess/` appears word for word in its `docs/spec/` file; reports theorem docstrings that do not (Rules review C8). |
| `build_viewer.py` | Builds `viewer/gotham.html`, a page that steps through the Gotham proof, from `ChessDemo/GothamCert.lean`. |

Python: any Python 3 with python-chess 1.11 (`pip install chess`); run scripts with `python -I`.
`gen_cert.py` also needs Stockfish and the compiled program `chess-perft`
(`lake build chess-perft`).

## gen_cert.py

```
python -I scripts/gen_cert.py --fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1" \
  --budget 11 --only-move b7b2 --root Puzzles.gotham --module ChessDemo.GothamCert \
  --stockfish /opt/homebrew/bin/stockfish --out ChessDemo/GothamCert.lean --check
```

This regenerates `ChessDemo/GothamCert.lean` (about 25 s). Run it from the library's root.

Who does what:

* **Stockfish** (through python-chess, one thread, fixed-depth searches, so reruns give the same
  file) proposes the attacker's move at each attacker node and the mate distance after each
  alternative to the best move. It is asked again, with more depth and three lines, if its first
  proposal does not lead to a mate within the budget.
* **python-chess** plays the moves, writes SAN for comments, and lists the defender's replies.
* **This library's generator**, compiled (`chess-perft FEN 1`), lists the moves of every position in
  the order of `legalMoves`, which the per-node proofs need (Game spec §4.1). The script checks that
  the two generators list the same moves, and that `chess-perft` reads the script's FEN back
  unchanged.
* **The script** writes each position as a checkpoint literal in this library's conventions:
  `Board.pack`'s hexadecimal digits, the en passant target after **every** two-square advance (not
  python-chess's default, which drops targets no pawn can use), and castling rights revoked by
  squares (`Move.castlingAfter`).
* **Lean** checks everything, one node per theorem, with `decide +kernel`.

For an only-move claim the file ends with `moves_root` (the root's moves, in the order of
`legalMoves`), `refutations` (after every other move, the opponent forces mate: more than
`OnlyWinningMove` says, so it is a claim of its own) and `onlyWinningMove`, proved from the two.

`--check` evaluates the certificate value with the diagnostic `firstFailureOnlyMove` (or
`firstFailureWin`), interpreted, on the literal root; `none` means the checker accepts it, and
otherwise it prints the path to the first rejecting node and the reason.

## The generated-file interface (Game spec §4.3)

A generated file

* states its claims with `Chess.WinsIn` and `Chess.OnlyWinningMove`, about a position the caller
  names (`--root`, for instance a name from `Chess.Puzzles`);
* names its moves by literal `Move` definitions named by their UCI writing (`def b7b2 : Move :=
  ⟨⟨1, 6⟩, ⟨1, 1⟩, none⟩`), not by `uci "…"`; the file that restates a claim proves
  `uci "…" = lit` by `decide +kernel`, as `ChessDemo.uci_b7b2` does;
* writes its certificates as values of `Cert` and `OnlyMoveCert`;
* proves its claims only with `Game.Forces.of_play_eq`, `Game.Forces.move_of_play_eq`,
  `Game.Forces.replies_of_moves_eq`, `Game.Forces.forall_mem_cons`, `Game.Forces.forall_mem_nil`,
  `Game.WinsIn.of_mated`, `Game.OnlyWinningMove.of_moves_eq`, `Game.OnlyWinningMove.refuted_cons`,
  `Game.OnlyWinningMove.refuted_cons_self`, `Game.OnlyWinningMove.refuted_nil`, `mem_chess_moves`,
  `checkWin_sound` and `checkOnlyMove_sound`, with `decide +kernel` for every fact about one
  position, and at an only-move root the move-list equation `moves_root` used by `rw` and `▸`;
* never applies a constructor of `Forces` and names no lemma of core.

`ChessTest/Interface.lean` records the signatures of these names, so a change to one of them fails
`lake build ChessTest` before it breaks a generated file.

Two details are forced by Lean's elaborator, not by the kernel (Game spec §4.1): a defender's move
list is stated as `Game.chess.moves p = […]`, not `legalMoves p = […]`, and an attacker's move is
shown available with `mem_chess_moves.2 (by decide +kernel)`, not `mem_legalMoves.2`. Written the
other way, the elaborator unfolds `legalMoves p` while unifying and starts to evaluate it, which
runs out of heartbeats on positions with many moves.

## check_docstrings.py

```
python -I scripts/check_docstrings.py            # every file under Chess/
python -I scripts/check_docstrings.py Chess/Rules/Defs.lean
```

Run it from the library's root. It needs no package. The spec of `Chess/A/B.lean` is
`docs/spec/A.B.md` if that file exists, else `docs/spec/A.md`, so the split modules `Chess.Game`
and `Chess.Rules` are checked against their one spec each. Whitespace is normalised and table
pipes are ignored. A missing definition or instance docstring makes the exit status 1; a missing
theorem docstring is only listed, because some specs (Basic's, Game's) state a lemma's English in a
table cell that merges several lemmas.

## build_viewer.py

```
python -I scripts/build_viewer.py
```

Run it from the library's root after regenerating `ChessDemo/GothamCert.lean`. It needs no package
and no engine: it reads the checkpoints, the node theorems (`wN`), the best move's node and the
`refutes_…` theorems straight from the generated file, so the page shows the tree the kernel
checked, and stops if any node theorem, move or checkpoint fails to parse. The data is inlined into
`viewer/template.html` with the cburnett piece images of `viewer/pieces/` (GPLv2+, credited in
`viewer/pieces/README.md`), giving `viewer/gotham.html`, one self-contained page (it loads only its
fonts). Open it in a browser: a wood board, the main line with a button for each other White reply,
White's mate after each of Black's other 33 moves, and for each position the theorem that proves it.
