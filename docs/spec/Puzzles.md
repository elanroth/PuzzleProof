# Specification of `Chess.Puzzles`

Role: English specification writer and translator (one overnight round, ROADMAP step 5); review
fixes (Round 2).
Date: 2026-11-02.
Status: Round 2, matched to the Lean of `Chess/Puzzles.lean` and `ChessTest/Puzzles.lean` (see
`docs/process/Puzzles.md`). Every definition below is in the library, with no `sorry`.

Files: `Chess/Puzzles.lean`; its tests, since Round 2, in `ChessTest/Puzzles.lean` (§2). Depends
on: `Chess.ChessGame` (for `fen`; the tests also use `uci`, `legalMoves` and `Position.toFEN`);
core only. Carries out ROADMAP step 5's "name headline positions once".

What a reader must trust from this module: **all of it**, which is one FEN string per position. A
headline theorem stated about `Puzzles.gotham` means what it would mean stated about
`fen "…"` with that string, and `fen_eq_iff` of `Chess.ChessGame` says what that is.

## 0. How to read this document

The conventions of `docs/spec/ChessGame.md` §0 apply unchanged: each definition has an ID, its Lean
name and type, its Lean body, and a **docstring** in quotation marks that the Lean carries word for
word; `autoImplicit = false`. Everything lives in `namespace Chess.Puzzles`.

### The idea of the module

A headline theorem names its position. Writing the FEN string inside every statement repeats it
in the theorem, in each generated certificate file and in the demo, and a reader then has to check
that the copies agree. This file names each headline position once. The demonstration of ROADMAP
step 7 and its generated files import it.

### Contents of the file, in order

1. Module docstring, text below.
2. D1.1 `gotham`.

The tests T1–T3 are in `ChessTest/Puzzles.lean` (§2).

### The module docstring, word for word

```
# Puzzles

The positions of headline theorems, each named once, so that a theorem reads
`WinsIn .black 11 Puzzles.gotham` and its reader checks the FEN in one place. Specification:
`docs/spec/Puzzles.md`; every definition below carries the docstring given there.

## Main definitions

* `Puzzles.gotham`: the GothamChess "checkmate in 11" position, Black to move.

## Implementation notes

* Each position is written `fen "…"`, so a name means exactly what its FEN string means
  (`fen_eq_iff`): a reader compares the string with the source of the puzzle.
* The FEN conventions are those of `Chess.ChessGame`: the en passant target is written after every
  two-square advance, and the clock fields must be numerals but are otherwise ignored.
* The tests are in `ChessTest.Puzzles`, so that a library build does not pay for them.
```

---

## 1. Positions

### D1.1 `def Puzzles.gotham : Position`

```lean
def gotham : Position := fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"
```
*(checked)*

Docstring: "The GothamChess "checkmate in 11" position, Black to move, from the game Leo vs. Casim
as shown in https://youtube.com/shorts/KqSqHs6QYJE and transcribed in the prototype `chess-lean`.
White threatens `Rh8#`. The puzzle's claim, proved in the prototype and the target of this
library's Stage 1 demonstration, is that `Rxb2+` (`b7b2`) is Black's only winning move and that
Black mates within 11 moves of its own. There is no en passant target: had White just played
`e2e4`, Black could capture en passant on `e3`, and every FEN convention would write `e3`. The
clock fields `0 1` are ignored."

**Where the string comes from, and how it was checked** (2026-11-02).

- The string is the one of the prototype, `chess-lean/ChessProof/Gotham.lean`, character for
  character. The same string appears in the prototype's write-up (`chess-lean/artifact/`), whose
  main line starts `Rxb2+ Kc1 Rb1+ Kxb1 Qb5+` and lists 34 legal moves at the root.
  `chess-lean/README.md` describes the position ("the GothamChess mate-in-11 position") but does
  not repeat the FEN.
- python-chess 1.11.2 reads it as a valid position: Black to move, one king each, White (not to
  move) not in check, 34 legal moves, `b7b2` legal and written `Rxb2+`. Writing it back gives the
  same string.
- **En passant.** This library writes the en passant target after every two-square advance
  (`Position.epTarget`; Stockfish and Lichess write it only when a capture is possible). The two
  conventions differ only when the target is written by one and not by the other. Here the only
  White pawn that could have just advanced two squares is the one on `e4` (`e2` and `e3` are
  empty); after `e2e4`, Black's pawn on `f4` could capture on `e3`, and python-chess confirms that
  `f4e3` would then be legal (35 legal moves). So under either convention the string would carry
  `e3`; its `-` says that White's last move was not `e2e4`, and both conventions read it the same
  way.
- **Castling.** `-` is forced: neither king is on its home square.
- **Clocks.** `0 1` are numerals, so `fen` accepts them, and ignores them (`ChessGame` spec,
  clock fields). The position has no clock, so a headline about it says nothing about the fifty-
  or seventy-five-move rules.

## 2. Tests

Three `#guard`s, interpreted, in `ChessTest/Puzzles.lean` (test library `ChessTest`, built by
`lake build ChessTest`, not by `lake build`; imported from `ChessTest.lean`). Round 1 had them in
`Chess/Puzzles.lean` under `/-! ## Tests -/`, where they cost about 1.4 s of the module's 2.0 s on
every library build (`lake env lean`, 2026-11-02; about 0.6 s is the definition, the `fen` parse
by `decide +kernel`). Round 2 moved them, following the convention of ROADMAP step 3 that tests
live in `ChessTest`. The parse itself stays in the library build, since `fen`'s default argument
checks it in the kernel. A first version also had `gotham.turn = .black`,
`gotham.castling = .none` and `gotham.epTarget = none` by `rfl`; those cost about 2 s more in the
kernel and say nothing T1 does not, so they were dropped.

The module docstring of `ChessTest/Puzzles.lean`, word for word:

```
# Tests of `Chess.Puzzles`

The tests of `Chess.Puzzles`, moved out of the library module so that a library build does not pay
for them (`lake build ChessTest`). Specification: `docs/spec/Puzzles.md` §2.

## Implementation notes

* The `#guard`s are interpreted: they are evidence about the generator, not kernel facts. No
  `native_decide`.
```

| ID | Statement | What it tests |
|---|---|---|
| T1 | `gotham.toFEN == "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"` | the position writes back to its string: Black to move, no castling right, no en passant target (`toFEN` always writes the clocks `0 1`) |
| T2 | `(legalMoves gotham).length == 34` | the move count agrees with python-chess |
| T3 | `(legalMoves gotham).contains (uci "b7b2")` | the claimed best move is listed |

T2 and T3 evaluate the generator. T3 is evidence, not a proof, that `Legal gotham (uci "b7b2")`
(via `mem_legalMoves`, M4); the kernel fact comes with the certificates of ROADMAP step 7. All three
passed *(checked)*.

## 3. Design choices

1. **A separate module, in the library.** The position belongs to the headline, which the default
   build should check, so it is in `Chess`, not in `ChessTest`. Its tests are not part of the
   headline, so they are in `ChessTest` (Round 2). It is not in `Chess.ChessGame`,
   which is notation: a named position is a statement's data, and keeping it apart keeps the
   trusted text of each headline short and easy to find.
2. **The name `Puzzles`.** `Positions` would be confused with `Chess.Position`. The headline
   positions of Stages 1–3 are puzzles in the chess sense (a claim about the best move); the
   namespace keeps their short names (`gotham`) from colliding with the library's.
3. **The docstring states the claim, not that it is proved here.** As of this round the library
   has not proved anything about the position; the demonstration is ROADMAP step 7.

## 4. Not in this module

- The certificates for the Gotham claims and the demonstration theorems (ROADMAP step 7).
- Further headline positions (the short mates of step 7) are added here, each with its source and
  its FEN checked the same way.
