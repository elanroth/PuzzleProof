# Specification of `ChessDemo.Gotham`

Role: demo implementer (one overnight round, ROADMAP steps 6 and 7).
Date: 2026-11-02.
Status: Round 2 (2026-11-02, review of Round 1: DG3's docstring now says only what
`OnlyWinningMove` says; the refutations are stated as DG7 and DG8), and Round 3 (2026-11-02,
finding gotham-1: the trust note names the definitions of `Chess.ChessGame` that `fen_eq_iff` and
`uci_eq_iff` bring in, instead of saying "not the game layer"), matched to
`ChessDemo/Gotham.lean` (see `docs/process/ChessDemo.md`). Every theorem below is proved, kernel
only, with no `sorry`.

Library: `ChessDemo` (`lake build ChessDemo`, not a default target). File: `ChessDemo/Gotham.lean`.
Imports: `ChessDemo.GothamCert` (the generated certificate file, `docs/spec/ChessDemo.GothamCert.md`),
and through it `Chess.Puzzles` and `Chess.ChessGame.Fide`.

What a reader of the headline must trust: the statements below, and the definitions they mention.
For the three `spec` theorems that is `Chess.Rules` (with `Chess.Basic` and `Chess.Position`),
`Chess.Spec.Winning`, the FEN string of `Puzzles.gotham`, and the notation `fen "…"` and
`uci "…"` through the statements of `fen_eq_iff` and `uci_eq_iff`. Those two statements bring in
definitions of `Chess.ChessGame` that are trusted as well: the predicates `Position.Sane`, `IsFEN`,
`ClockFields` and `IsNumeral` (its section "Accepting"), and the FEN writer `Position.fenFields`
with the definitions of its section "Writing" that it uses (`Board.fenChars`, `rowChars`,
`emptyRun`, `Board.row`, `Color.fenChar`, `epChars`). The UCI writer `Move.toUCI` is in
`Chess.Position`. Not trusted: the generated file, the generator `legalMoves`, the game instance
`Game.chess`, Stockfish and python-chess, which only make the proofs, and the parsers `parseFEN`
and `parseUCI`, which `fen_eq_iff` and `uci_eq_iff` characterise.

## 0. How to read this document

The conventions of `docs/spec/ChessGame.md` §0 apply: each theorem has an ID, an English statement
that is its Lean docstring word for word, and its Lean statement. Everything lives in
`namespace ChessDemo`, with `open Chess`.

### The idea of the module

THEOREMS §7 closes Stage 1 with "the Gotham puzzle, `WinsIn` and `OnlyWinningMove`, [kernel]". The
proofs are in the generated file, one theorem per node of a certificate tree that Stockfish
proposed; this module states the two claims with their final names, in the notation a reader
checks (`Puzzles.gotham`, `uci "b7b2"`), and reads them through G8 as statements about the rules
alone. It also states the stronger fact that the proof of the only move establishes: after each
other legal move of Black, White has a forced mate.

### The module docstring, word for word

```
# The Gotham puzzle

The Stage 1 closing demonstration (THEOREMS §7): in the GothamChess "checkmate in 11" position
`Puzzles.gotham`, Black to move, Black mates within 11 moves of its own, and `1...Rxb2+` (`b7b2`)
is Black's only winning move. Specification: `docs/spec/ChessDemo.Gotham.md`; every theorem below
carries the docstring given there.

## Main statements

* `gotham_winsIn`, `gotham_onlyWinningMove`: the two claims, about the chess game of
  `Chess.ChessGame` (moves listed by `legalMoves`, mate as `Game.chess.Mated`).
* `gotham_specWinsIn`, `gotham_specOnlyWinningMove`: the same two claims about FIDE chess as
  `Chess.Spec.Winning` states it with the rules alone (`Legal`, `Position.play`, `Checkmate`),
  through G8 (`Chess.ChessGame.Fide`).
* `gotham_not_wins_white`: White has no forced win.
* `gotham_refuted`, `gotham_specRefuted`: what the proof of the only move shows, more than
  `OnlyWinningMove` says: after each of Black's other legal moves, White mates within some number
  of moves, in the chess game and read through G8.

## Implementation notes

* Kernel only. The proofs are the per-node theorems of the generated file `ChessDemo.GothamCert`
  (`scripts/gen_cert.py`, Stockfish and python-chess), each checked by `decide +kernel`; there is no
  `native_decide`. `ChessDemo.Axioms` records that every theorem here uses only the standard
  axioms.
* What a reader of `gotham_specWinsIn`, `gotham_specOnlyWinningMove` and `gotham_specRefuted`
  trusts: the rules (`Chess.Rules`, with `Chess.Basic` and `Chess.Position`),
  `Chess.Spec.Winning`, the FEN string of `Puzzles.gotham`, and the notation `fen "…"` and
  `uci "…"` through the statements of `fen_eq_iff` and `uci_eq_iff`. Those statements mention
  definitions of `Chess.ChessGame`, trusted too: the predicates `Position.Sane`, `IsFEN`,
  `ClockFields` and `IsNumeral`, and the FEN writer `Position.fenFields` with the definitions of
  section "Writing" it uses (`Move.toUCI`, the UCI writer, is in `Chess.Position`). Not the
  generator `legalMoves`, not the game instance `Game.chess`, not the parsers, not the generated
  file, not the engine.
* No claim says anything about the fifty-move or repetition rules (THEOREMS G15), and none says
  that 11 is the shortest mate: `MateIn` is not claimed.
```

## 1. Theorems

| ID | English (= Lean docstring) | Lean statement and proof |
|---|---|---|
| DG1 | **The Gotham puzzle, the win.** In `Puzzles.gotham`, Black mates within 11 moves of its own, whatever White plays. | `theorem gotham_winsIn : WinsIn .black 11 Puzzles.gotham := GothamCert.winsIn` |
| DG2 | The move written `uci "b7b2"` is the move `GothamCert.b7b2` of the generated file. | `theorem uci_b7b2 : uci "b7b2" = GothamCert.b7b2 := by decide +kernel` |
| DG3 | **The Gotham puzzle, the only move.** In `Puzzles.gotham`, `1...Rxb2+` (`b7b2`) is Black's only winning move: Black wins after it, and after none of its other 33 legal moves. | `theorem gotham_onlyWinningMove : OnlyWinningMove Puzzles.gotham (uci "b7b2")`, by `rw [uci_b7b2]` and `GothamCert.onlyWinningMove` |
| DG4 | **The Gotham puzzle, the win, read with the rules alone (G8).** In `Puzzles.gotham`, Black can force FIDE checkmate within 11 moves of its own, every move being `Legal`. | `theorem gotham_specWinsIn : SpecWinsIn .black 11 Puzzles.gotham := winsIn_iff_specWinsIn.mp gotham_winsIn` |
| DG5 | **The Gotham puzzle, the only move, read with the rules alone (G8).** In `Puzzles.gotham`, `b7b2` is legal, Black can force FIDE checkmate after it, and after every other legal move of Black it cannot. | `theorem gotham_specOnlyWinningMove : SpecOnlyWinningMove Puzzles.gotham (uci "b7b2") := onlyWinningMove_iff_specOnlyWinningMove.mp gotham_onlyWinningMove` |
| DG6 | White has no forced win in `Puzzles.gotham`: no position is a forced win for both sides. | `theorem gotham_not_wins_white : ¬ Wins .white Puzzles.gotham := Game.not_wins_of_winsIn_other gotham_winsIn` |
| DG7 | **The Gotham puzzle, the refutations.** In `Puzzles.gotham`, after each of Black's legal moves other than `1...Rxb2+` (`b7b2`), White mates within some number of moves of its own, whatever Black plays. | `theorem gotham_refuted : ∀ m ∈ Game.chess.moves Puzzles.gotham, m ≠ uci "b7b2" → ∃ k, WinsIn .white k (Puzzles.gotham.play m)`, by `rw [uci_b7b2]` and `GothamCert.refutations` |
| DG8 | **The Gotham puzzle, the refutations, read with the rules alone (G8).** In `Puzzles.gotham`, after each legal move of Black other than `b7b2`, White can force FIDE checkmate within some number of moves of its own, every move being `Legal`. | `theorem gotham_specRefuted : ∀ m, Legal Puzzles.gotham m → m ≠ uci "b7b2" → ∃ k, SpecWinsIn .white k (Puzzles.gotham.play m) := fun m hm hne => (gotham_refuted m (mem_chess_moves.2 hm) hne).imp fun _ => winsIn_iff_specWinsIn.mp` |

Notes.
- DG3 says what `OnlyWinningMove` says: Black does not win after the other moves. The proof shows
  more, a forced mate for White after each of them (one `refutes_…` theorem per alternative in the
  generated file, each with its own budget, at most 5: 30 mates in 1, two in 2, one in 5), and
  DG7 states it: the generated file gathers the 33 refutations into `GothamCert.refutations`, from
  which it proves `GothamCert.onlyWinningMove` (Game L4.19 and L2.19). Round 1's DG3 docstring
  claimed the forced mates without a theorem stating them (review of Round 1).
  `OnlyWinningMove` counts every *listed* move: 34 in `Puzzles.gotham` (`ChessTest.Puzzles` T2).
  The number 33 in DG3 and the 34 listed moves are facts about the position, checked by the
  generated file's move-list equation; neither statement mentions a count.
- DG7 quantifies over `Game.chess.moves`, as `OnlyWinningMove` does; DG8 quantifies over `Legal`
  (the two agree by `mem_chess_moves`). The budget `k` depends on the move; the largest is 5.
- DG2 exists because the generated file names its moves by literals (`def b7b2 : Move :=
  ⟨⟨1, 6⟩, ⟨1, 1⟩, none⟩`), which are cheap for the kernel and the elaborator, while a headline
  is written in UCI.
- DG6 is G4 (`WinsIn.not_both`) applied to DG1, the prototype's `gotham_white_cannot_win`.

## 2. Cost

`lake build ChessDemo.Gotham` after `ChessDemo.GothamCert`: under a second (the module checks only
DG2 and the G8 rewrites). The cost is in the generated file: about 165 s and 1.1 GB, sequential
elaboration (`docs/spec/ChessDemo.GothamCert.md` §3).
