import ChessDemo.GothamCert

/-!
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
-/

namespace ChessDemo

open Chess

/-- **The Gotham puzzle, the win.** In `Puzzles.gotham`, Black mates within 11 moves of its own,
whatever White plays. -/
theorem gotham_winsIn : WinsIn .black 11 Puzzles.gotham :=
  GothamCert.winsIn

/-- The move written `uci "b7b2"` is the move `GothamCert.b7b2` of the generated file. -/
theorem uci_b7b2 : uci "b7b2" = GothamCert.b7b2 := by decide +kernel

/-- **The Gotham puzzle, the only move.** In `Puzzles.gotham`, `1...Rxb2+` (`b7b2`) is Black's only
winning move: Black wins after it, and after none of its other 33 legal moves. -/
theorem gotham_onlyWinningMove : OnlyWinningMove Puzzles.gotham (uci "b7b2") := by
  rw [uci_b7b2]
  exact GothamCert.onlyWinningMove

/-- **The Gotham puzzle, the win, read with the rules alone (G8).** In `Puzzles.gotham`, Black can
force FIDE checkmate within 11 moves of its own, every move being `Legal`. -/
theorem gotham_specWinsIn : SpecWinsIn .black 11 Puzzles.gotham :=
  winsIn_iff_specWinsIn.mp gotham_winsIn

/-- **The Gotham puzzle, the only move, read with the rules alone (G8).** In `Puzzles.gotham`,
`b7b2` is legal, Black can force FIDE checkmate after it, and after every other legal move of
Black it cannot. -/
theorem gotham_specOnlyWinningMove : SpecOnlyWinningMove Puzzles.gotham (uci "b7b2") :=
  onlyWinningMove_iff_specOnlyWinningMove.mp gotham_onlyWinningMove

/-- White has no forced win in `Puzzles.gotham`: no position is a forced win for both sides. -/
theorem gotham_not_wins_white : ¬ Wins .white Puzzles.gotham :=
  Game.not_wins_of_winsIn_other gotham_winsIn

/-- **The Gotham puzzle, the refutations.** In `Puzzles.gotham`, after each of Black's legal moves
other than `1...Rxb2+` (`b7b2`), White mates within some number of moves of its own, whatever Black
plays. -/
theorem gotham_refuted : ∀ m ∈ Game.chess.moves Puzzles.gotham, m ≠ uci "b7b2" →
    ∃ k, WinsIn .white k (Puzzles.gotham.play m) := by
  rw [uci_b7b2]
  exact GothamCert.refutations

/-- **The Gotham puzzle, the refutations, read with the rules alone (G8).** In `Puzzles.gotham`,
after each legal move of Black other than `b7b2`, White can force FIDE checkmate within some number
of moves of its own, every move being `Legal`. -/
theorem gotham_specRefuted : ∀ m, Legal Puzzles.gotham m → m ≠ uci "b7b2" →
    ∃ k, SpecWinsIn .white k (Puzzles.gotham.play m) :=
  fun m hm hne =>
    (gotham_refuted m (mem_chess_moves.2 hm) hne).imp fun _ => winsIn_iff_specWinsIn.mp

end ChessDemo
