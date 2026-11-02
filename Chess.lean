import Chess.Basic
import Chess.Position
import Chess.Rules
import Chess.MoveGen
import Chess.Game
import Chess.ChessGame
import Chess.Spec.Winning
import Chess.ChessGame.Fide
import Chess.Puzzles

/-!
# Chess

Root of the `Chess` library: the rules of chess as a readable specification, and executable code
(a move generator, a bounded search, certificate checkers) linked to it by proved theorems, so that
facts about chess positions are checked by the Lean kernel. Each module is imported here once it
exists. The README gives the reading order and a file map; `docs/ROADMAP.md` §2 gives the state of
each module.

## Trusted base of a chess headline

A headline such as `OnlyWinningMove Puzzles.gotham (uci "b7b2") ∧ WinsIn .black 11 Puzzles.gotham`
is believed by checking, besides the kernel:

* `Chess.Basic` and `Chess.Position`: squares, pieces, boards, moves and positions.
* `Chess.Rules`, its definitions only (`Chess/Rules/Defs.lean`): attacks, check, the legal moves,
  playing a move, checkmate and stalemate.
* `Chess.Spec.Winning`: `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecMateIn` and
  `SpecOnlyWinningMove`, written with the rules alone.
* The notation of `Chess.ChessGame`: the writers, `IsNumeral`, `ClockFields`, `IsFEN`,
  `Position.Sane`, and the statements of `fen_eq_iff` and `uci_eq_iff`; and the FEN string of the
  position (for `Puzzles.gotham`, one line of `Chess.Puzzles`).

The headline's `WinsIn` and `OnlyWinningMove` are the abbreviations of `Chess.ChessGame`, and
`Chess.ChessGame.Fide` proves them equivalent to `SpecWinsIn` and `SpecOnlyWinningMove`
(THEOREMS G8), so their definitions need not be trusted.

## Not trusted: how claims are computed

* `Chess.MoveGen`: the move generator, proved sound and complete (M4, `mem_legalMoves`).
* `Chess.Game`: abstract two-player games (`Game.WinsIn`, `Game.MateIn`, `Game.OnlyWinningMove`),
  their laws, the bounded search and the certificate checkers, each proved correct.
* `Game.chess` and the four abbreviations of `Chess.ChessGame`, the readers of FEN and UCI, and the
  lemmas of `Chess.Rules` (`Laws`, `Castling`).
* `Chess.ChessGame.Fide`: the equivalences above.

## Implementation notes

* FIDE's draw rules are absent: FEN clocks are read and ignored, so a `WinsIn` may still be a draw
  under the fifty- or seventy-five-move rule (THEOREMS G15). `Position.Sane` admits some
  unreachable positions; the rules re-check everything, so this does not affect `WinsIn`.
-/
