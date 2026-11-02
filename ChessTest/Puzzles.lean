import Chess.Puzzles

/-!
# Tests of `Chess.Puzzles`

The tests of `Chess.Puzzles`, moved out of the library module so that a library build does not pay
for them (`lake build ChessTest`). Specification: `docs/spec/Puzzles.md` §2.

## Implementation notes

* The `#guard`s are interpreted: they are evidence about the generator, not kernel facts. No
  `native_decide`.
-/

namespace Chess

namespace Puzzles

-- T1. The position writes back to the same FEN: Black to move, no castling right, no en passant
-- target (and the clocks `0 1`, which `toFEN` always writes).
#guard gotham.toFEN == "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"
-- T2. Black has 34 legal moves (python-chess 1.11.2 agrees).
#guard (legalMoves gotham).length == 34
-- T3. `b7b2` is one of them.
#guard (legalMoves gotham).contains (uci "b7b2")

end Puzzles

end Chess
