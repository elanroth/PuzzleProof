import Chess.ChessGame

/-!
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
-/

namespace Chess

namespace Puzzles

/-- The GothamChess "checkmate in 11" position, Black to move, from the game Leo vs. Casim as
shown in https://youtube.com/shorts/KqSqHs6QYJE and transcribed in the prototype `chess-lean`.
White threatens `Rh8#`. The puzzle's claim, proved in the prototype and the target of this
library's Stage 1 demonstration, is that `Rxb2+` (`b7b2`) is Black's only winning move and that
Black mates within 11 moves of its own. There is no en passant target: had White just played
`e2e4`, Black could capture en passant on `e3`, and every FEN convention would write `e3`. The
clock fields `0 1` are ignored. -/
def gotham : Position := fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"

end Puzzles

end Chess
