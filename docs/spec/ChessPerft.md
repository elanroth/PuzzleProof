# Specification of the program `chess-perft`

Role: test-library implementer (one overnight round, ROADMAP step 3).
Date: 2026-11-02.
Status: Round 2, matched to the Lean of `ChessPerft.lean` (see `docs/process/ChessTest.md`).

File: `ChessPerft.lean`, the root of the `lean_exe` `chess-perft` in `lakefile.toml`. Depends on:
`Chess.ChessGame` (for `parseFEN`, `Position.toFEN`, `Move.toUCI`, and through it `perft` and
`perftDivide` of `Chess.MoveGen`) and `ChessTest.Tabulate` (for `Position.tabulate`). Core only.

What a reader must trust from this file: **nothing.** The program proves nothing and states
nothing. It exists so that anyone can compare this library's move generator with another program
(python-chess, Stockfish's `go perft`, any perft tool that prints a divide) on any position, and so
localize a disagreement to one move.

## 0. Usage

```
lake build chess-perft
.lake/build/bin/chess-perft "<FEN>" <depth>      # or: lake exe chess-perft "<FEN>" <depth>
```

The FEN may be one argument or several (all arguments but the last are joined by single spaces), so
`chess-perft rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 3` works unquoted. It is read
by `parseFEN`: canonical FEN of a sane position (castling letters in `KQkq` order, single spaces,
two numeral clock fields or none). Output, one item per line:

```
fen <the position written back by Position.toFEN>
<uci> <count>          -- the divide: one line per entry of legalMoves, in the generator's order
...
perft <depth> <count>
```

At depth 0 there is no divide. A bad command line (not a FEN of a sane position, or a depth that is
not a natural number, or fewer than two arguments) prints a message and the usage to standard error
and exits with code 1.

With the single argument `--moves` (added 2026-11-03 for `scripts/gen_bound.py`), the program reads
one FEN per line from standard input and prints one line per FEN: the position written back by
`Position.toFEN`, a tab, and its `legalMoves` in the generator's order as UCI separated by spaces
(nothing after the tab when there is no legal move). A line that is not a canonical FEN of a sane
position prints `error`. It stops at the end of the input.

## 1. Definitions

### D1.1 `usage : String`

Docstring: "The text printed for a bad command line."

### D1.1a `movesMode : IO UInt32`

Docstring: "The `--moves` mode: for each FEN read from standard input, the position written back and
its legal moves in the generator's order."

### D1.2 `perftReport (p : Position) (n : Nat) : List String`

```lean
def perftReport (p : Position) (n : Nat) : List String :=
  let d := match n with
    | 0 => []
    | k + 1 => perftDivide k p
  let total := if n = 0 then 1 else (d.map (·.2)).sum
  [s!"fen {p.toFEN}"] ++ d.map (fun (m, c) => s!"{m.toUCI} {c}") ++ [s!"perft {n} {total}"]
```

Docstring: "The lines printed for position `p` at depth `n`: the FEN as read, the divide when `n` is
at least 1, then the total."

The total is the sum of the divide, which is `perft n p` by `sum_perftDivide`. (Round 1 computed
`perft n p` again for the total, which ran the whole search twice and checked nothing that
`sum_perftDivide` does not already prove.)

### D1.3 `main (args : List String) : IO UInt32`

Docstring: "Reads the FEN (all arguments but the last, joined by spaces) and the depth (the last
argument), and prints `perftReport` of the tabulated position; exits with code 1 on a bad command
line."

## 2. Design choices, with reasons

1. **The position is tabulated** (`Position.tabulate`, `docs/spec/ChessTest.Perft.md` §1) before
   perft runs. A board read by `parseFEN` is a function whose compiled code re-reads the FEN text on
   every square read (profiled: the time goes to `splitOn`, `readBoard` and `Piece.ofLetter?`).
   Measured on this machine (one search, Round 2): perft 3 of the initial position read from its
   FEN takes 10.9 s untabulated and 0.38 s tabulated; perft 4, 234 s untabulated and 9.0 s
   tabulated.
   `Position.tabulate_eq` proves that tabulating changes nothing.
2. **The FEN line is printed** so that a differential test also checks the reader and the writer:
   for an input written with every en passant target (python-chess's
   `board.fen(en_passant="fen")`), the four position fields printed must equal the input's.
   The clocks are always written `0 1`, since a position records none.
3. **The divide is in the generator's order**, which is not part of any contract (MoveGen design
   choice 6). Comparisons are by move, not by line.
4. **No `#eval`-only tool.** Interpreted perft is about 20 times slower than compiled here
   (depth 3: 8.0 s against 0.38 s for the initial position, 92 s against 4.2 s for Kiwipete), and
   a compiled program can be called from any language. For scale: python-chess, a bitboard
   generator in Python, counts the same perft about 80 times faster than this program (Kiwipete
   depth 3: 0.05 s against 4.2 s; depth 4: 2.5 s against 190 s); the library's generator is built
   to be read and proved, not to be fast (DESIGN §3.3).
