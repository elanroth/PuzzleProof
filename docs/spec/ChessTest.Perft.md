# Specification of the perft suite (`ChessTest.Tabulate`, `ChessTest.Perft`, `ChessTest.PerftDeep`)

Role: test-library implementer (one overnight round, ROADMAP step 3, THEOREMS M7).
Date: 2026-11-02.
Status: Round 2, matched to the Lean of `ChessTest/Tabulate.lean`, `ChessTest/Perft.lean` and
`ChessTest/PerftDeep.lean` (see `docs/process/ChessTest.md`). Everything below is in the test
library, with no `sorry` and no `native_decide`.

Library: `ChessTest`, the second `lean_lib` of `lakefile.toml`, not a default target. Built by
`lake build ChessTest`; `lake build` builds `Chess` alone. Depends on `Chess.ChessGame` (for `fen`
and, through it, `perft` of `Chess.MoveGen`). Core only.

What a reader must trust from these files: **nothing**, for the library's claims. The perft counts
are evidence about the specification, not part of it: a count that agrees with the published one is
evidence that `Legal` and `Position.play` read the FIDE Laws as the chess-programming community
does, at that position and depth (THEOREMS M7). They prove nothing about other positions.

## 0. Conventions

As in `docs/spec/MoveGen.md` §0: each definition has an ID, its Lean name and type, its Lean body
and a docstring in quotation marks that the Lean carries word for word; each theorem has an ID, its
docstring and its Lean statement. Everything is in `namespace Chess`; the five positions are in
`namespace Chess.Perft`.

## Contents, in order

1. `ChessTest/Tabulate.lean`: `Position.tabulate`, `Position.tabulate_eq`.
2. `ChessTest/Perft.lean`, the positions: `Perft.kiwipete`, `Perft.position3` to `Perft.position6`.
3. `ChessTest/Perft.lean`, the checks: eight kernel theorems, seven `#guard`s.
4. `ChessTest/PerftDeep.lean`: four deeper `#guard`s.
5. The published counts.
6. Design choices, with reasons.

---

## 1. `ChessTest/Tabulate.lean`

### D1.1 `Position.tabulate (p : Position) : Position`

```lean
def Position.tabulate (p : Position) : Position :=
  let a : Array (Option Piece) := (Square.all.map p.board).toArray
  { p with board := fun s => a[s.index.val]! }
```

Docstring: "The position `p` with its board read once into an array of the 64 squares, in index
order, and served from that array. It is the same position (`Position.tabulate_eq`), but a square of
its board is then read in constant time, however the board was built."

### L1.1 `Position.tabulate_eq (p : Position) : p.tabulate = p`

Docstring: "Tabulating a position gives back the same position."

Proof: function extensionality on the board; the `s.index`-th entry of `Square.all` is
`Square.ofIndex s.index`, which is `s` by R1 (`Square.ofIndex_index`). About eight lines, standard
axioms (ledger).

**Why it exists.** A `Board` is a function. The code compiled for `readBoard cs` (in
`Chess.ChessGame`) re-reads the FEN text on every square read: a profile of the compiled
`chess-perft` on an untabulated position spends its time in `splitOn`, `readBoard`,
`Piece.ofLetter?` and `emptyCount?`, all called from inside the search. Measured on this machine
(compiled, one search): perft 3 of the initial position read from its FEN, 10.9 s untabulated,
0.38 s tabulated; perft 4, 234 s and 9.0 s. Interpreted (`#guard`): `perft 2 Perft.kiwipete`, 37 s
and 1.6 s. The same position built as `Position.initial` needs no tabulation (compiled perft 3 in
0.39 s, perft 4 in 9.4 s).
`Position.tabulate` returns a `Position`, a structure, so its array is built once per call. A first
version that returned a `Board` (`fun s => a[s.index.val]!` as the result of a `Board`-valued
definition) was slower than no tabulation at all (perft 3 did not finish in 10 minutes): the
compiled code evidently rebuilt the array at every square read, as if the square were a second
argument. This is the trap of Position review C1, met from the reading side.

---

## 2. The positions (`ChessTest/Perft.lean`, `namespace Chess.Perft`)

Each is `fen "…"` of the FEN published on chessprogramming.org (*Perft Results*), so the parse is
checked in the kernel when the file is elaborated. Position 1 is `Position.initial` itself
(`fen` of its FEN is `Position.initial`, checked in `ChessTest/ChessGame.lean`). None of the six
FENs has an en passant target, so the library's en passant convention plays no part. Position 5's
clocks (`1 8`) are ignored, as `fen` always does.

### D2.1 `Perft.kiwipete : Position`

`fen "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"`

Docstring: "Position 2 of the chessprogramming.org perft suite, "Kiwipete" (Peter McKenzie): a
middlegame in which both sides hold both castling rights, with many captures and pins."

### D2.2 `Perft.position3 : Position`

`fen "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1"`

Docstring: "Position 3 of the chessprogramming.org perft suite: a rook-and-pawn endgame whose lines
include en passant captures that would expose a king along the fifth rank."

### D2.3 `Perft.position4 : Position`

`fen "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1"`

Docstring: "Position 4 of the chessprogramming.org perft suite: White to move and in check, with
pawns about to promote on both sides and Black's two castling rights."

(Checked with python-chess: White is in check, from the bishop on b6.)

### D2.4 `Perft.position5 : Position`

`fen "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"`

Docstring: "Position 5 of the chessprogramming.org perft suite: White's pawn on d7 can promote by
capturing on c8, and White holds both castling rights."

(Checked with python-chess: the only promotions are d7c8 to each of the four pieces.)

### D2.5 `Perft.position6 : Position`

`fen "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10"`

Docstring: "Position 6 of the chessprogramming.org perft suite (Steven Edwards): a middlegame with
no castling rights."

---

## 3. The checks (`ChessTest/Perft.lean`)

### Kernel checks, each `by decide +kernel`, each [kernel] (axioms ledger)

| ID | Lean | Docstring |
|---|---|---|
| L3.1 | `perft_initial_1 : perft 1 Position.initial = 20` | "Perft 1 of the initial position is 20, the published count. [kernel]" |
| L3.2 | `perft_initial_2 : perft 2 Position.initial = 400` | "Perft 2 of the initial position is 400, the published count. [kernel]" |
| L3.3 | `perft_kiwipete_1 : perft 1 Perft.kiwipete = 48` | "Perft 1 of Kiwipete is 48, the published count. [kernel]" |
| L3.4 | `perft_position3_1 : perft 1 Perft.position3 = 14` | "Perft 1 of Position 3 is 14, the published count. [kernel]" |
| L3.5 | `perft_position3_2 : perft 2 Perft.position3 = 191` | "Perft 2 of Position 3 is 191, the published count. [kernel]" |
| L3.6 | `perft_position4_1 : perft 1 Perft.position4 = 6` | "Perft 1 of Position 4 is 6, the published count. [kernel]" |
| L3.7 | `perft_position5_1 : perft 1 Perft.position5 = 44` | "Perft 1 of Position 5 is 44, the published count. [kernel]" |
| L3.8 | `perft_position6_1 : perft 1 Perft.position6 = 46` | "Perft 1 of Position 6 is 46, the published count. [kernel]" |

Measured kernel cost after ROADMAP step 6 (this machine, 2026-11-02, `lake env lean
-Dprofiler=true ChessTest/Perft.lean`, no other Lean job running): depth 1 is 0.7 to 2.2 s per
position (initial 0.7 s, Kiwipete 2.2 s, Position 3 0.8 s, Position 4 1.5 s, Position 5 1.8 s,
Position 6 1.8 s); depth 2 is 9.8 s for the initial position and 5.6 s for Position 3; the whole
module took 39 s wall clock with a 3.7 GB maximum resident set size. Step 6's Boolean king-safety
filter (`kingSafeAfter`) is what made the kernel checks faster.

Measured kernel cost before step 6 (this machine, `decide +kernel`, scratch files): depth 1 is 1.5 s (initial),
4.7 s (Kiwipete), 1.2 s (Position 3), 2.9 s (Position 4), 4.1 s (Position 5), 4.2 s (Position 6),
21 s and 2.5 GB peak for all six. Depth 2: initial 42 s of CPU and 3.9 GB; Position 3, 13 s and
4.0 GB; Position 4, 26 s but 6.6 GB; Position 5 had not finished after 10 minutes, with the machine
swapping, and was stopped; Kiwipete and Position 6 were not tried (each has about as many depth-1
moves as Position 5). Depth 2 is therefore kept in the kernel for the initial position and Position
3 only. The module built in 214 s wall clock (91 s of CPU) with a 4.9 GB peak, on a machine that
was already swapping.

### Interpreted checks, on tabulated positions

```lean
-- Depth 2 of the four positions whose depth 2 is not checked in the kernel (about 1.5 s each).
#guard perft 2 Perft.kiwipete.tabulate == 2039
#guard perft 2 Perft.position4.tabulate == 264
#guard perft 2 Perft.position5.tabulate == 1486
#guard perft 2 Perft.position6.tabulate == 2079
-- Depth 3 of the three cheapest positions (about 2 to 10 s each).
#guard perft 3 Position.initial == 8902
#guard perft 3 Perft.position3.tabulate == 2812
#guard perft 3 Perft.position4.tabulate == 9467
```

A `#guard` is evaluated by the interpreter when the file is elaborated, and the build fails if it
is false. It is not a theorem: nothing in the environment records it.

---

## 4. `ChessTest/PerftDeep.lean`

```lean
#guard perft 3 Perft.kiwipete.tabulate == 97862
#guard perft 3 Perft.position5.tabulate == 62379
#guard perft 3 Perft.position6.tabulate == 89890
#guard perft 4 Perft.position3.tabulate == 43238
```

Measured: the module builds in about 2 to 2.5 minutes, single-threaded, 0.4 GB (119 s on an idle
machine, 137 to 146 s with other jobs running; the four checks take 24 to 39 s each). These times
are after the king-safety filter of ROADMAP step 6; before it the module took 263 s (4.4 minutes).
It is its own module so that it runs in parallel with the rest of `ChessTest`. Depth 4 and beyond of
the other positions is left to the compiled program and the differential test (§6, choice 3).

---

## 5. The published counts

From chessprogramming.org, *Perft Results* (the counts below are the ones the checks use; each was
also reproduced by python-chess 1.11.2 and by `chess-perft` on this machine,
`docs/process/ChessTest.md`):

| Position | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| initial | 20 | 400 | 8 902 | 197 281 | 4 865 609 |
| Kiwipete | 48 | 2 039 | 97 862 | 4 085 603 | |
| Position 3 | 14 | 191 | 2 812 | 43 238 | 674 624 |
| Position 4 | 6 | 264 | 9 467 | 422 333 | |
| Position 5 | 44 | 1 486 | 62 379 | 2 103 487 | |
| Position 6 | 46 | 2 079 | 89 890 | 3 894 594 | |

Where the Lean checks them: depth 1 of all six and depth 2 of the initial position and Position 3 in
the kernel; depth 2 of the rest and depth 3 of the initial position and Positions 3 and 4 by
`#guard` in `ChessTest.Perft`; depth 3 of Kiwipete and Positions 5 and 6 and depth 4 of Position 3
by `#guard` in `ChessTest.PerftDeep`. Depth 4 of all six and depth 5 of the initial position and
Position 3: by the compiled `chess-perft` in the differential test only, outside the build.

---

## 6. Design choices, with reasons

1. **Named theorems for the kernel checks, not `example`s**, so that the axioms ledger can print
   their axioms and THEOREMS M7's sketch (`perft_initial_3 … [kernel]`) has a counterpart. Depth 3
   in the kernel (THEOREMS M7's sketch) was out of reach when this choice was made: depth 2 of the
   initial position then cost 42 s and 3.9 GB. Since step 6 it costs 9.8 s (§3); depth 3, with
   about 22 times as many leaves, has not been tried since, so whether it now fits in time and
   memory is open (ROADMAP §5).
2. **`fen` literals, not `Board.unpack` checkpoints.** A scratch comparison for Kiwipete at depth 1:
   4.7 s through `fen`, 3.9 s through a packed literal. The `fen` form is the one a reader can check
   against the published FEN, and the difference is small.
3. **No `native_decide`.** DESIGN §7.3 allows `_native` theorems in the test library; none was
   needed. Deeper counts are checked outside the build, by the compiled program
   (`docs/spec/ChessPerft.md`) against python-chess, and recorded in the process log.
4. **The bug-class positions of DESIGN §8.4** are the named positions of `ChessTest/Rules.lean` and
   `ChessTest/MoveGen.lean` (`promoPos`, `epPinPos`, `epCheckPos`, `promoKnightPos` and the rest),
   checked there by `agreesWithLegal` and named moves, and also run to depth 3 through
   `chess-perft` against python-chess (process log).
