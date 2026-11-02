import Chess.ChessGame
import ChessTest.MoveGen

/-!
# Tests of `Chess.ChessGame`

The tests of `Chess.ChessGame`, moved out of the library module so that a library build, and every
file that imports `Chess.ChessGame`, does not pay for them (`lake build ChessTest`). Specification:
`docs/spec/ChessGame.md` §6.

## Implementation notes

* Kernel checks are `decide +kernel`; the `#guard`s are interpreted. No `native_decide`.
-/

namespace Chess

-- Reading and writing the initial position.
example : fen "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1" = Position.initial := by
  decide +kernel
#guard Position.initial.toFEN == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
-- Four fields are accepted; the position is sane.
#guard readFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -" == some Position.initial
example : Position.initial.Sane := by decide +kernel
-- Writing and reading back the test positions of `Chess.MoveGen` (L5.20 on examples).
#guard [Position.initial, foolsMate, epCheckPos, promoKnightPos].all
  fun p => readFEN p.toFEN == some p
#guard epCheckPos.toFEN == "k7/8/8/3pP3/4K3/8/8/8 w - d6 0 1"
-- Rejected: not canonical FEN.
#guard (parseFEN "rnbqkbnr/pppppppp/44/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone   -- 44
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KqQk - 0 1").isNone   -- order
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0").isNone     -- 5 fields
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR  w KQkq - 0 1").isNone  -- 2 spaces
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 ").isNone  -- trailing
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBN w KQkq - 0 1").isNone    -- 7 files
-- Rejected: not sane.
#guard (parseFEN "rnbqqbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone   -- no k
#guard (parseFEN "4k3/8/8/8/8/8/4R3/4K3 w - - 0 1").isNone   -- Black, not to move, in check
#guard (parseFEN "4k3/8/8/8/8/8/4R3/4K3 b - - 0 1").isSome
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq e3 0 1").isNone  -- ep rank
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1").isSome
-- The clock fields are ignored: both strings denote the same position (THEOREMS G15).
example : fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 149 80" = fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1" :=
  by decide +kernel
-- UCI.
#guard parseUCI "e7e8q" == some ⟨⟨4, 6⟩, ⟨4, 7⟩, some .queen⟩  -- e7, e8
#guard (parseUCI "e7e8Q").isNone
#guard (parseUCI "e2e9").isNone
#guard (parseUCI "0000").isNone
#guard (parseUCI "e2e4 ").isNone
#guard (parseUCI "Nf3").isNone
-- Chess as a game: mate is a win, stalemate is not, and the headline vocabulary works.
example : WinsIn .black 0 (fen "rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 1 3") :=
  winsIn_zero_iff.2 ⟨rfl, by decide +kernel⟩                       -- Fool's mate
example : MateIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") := by decide +kernel
example : WinsIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") :=
  Game.checkWin_sound (c := .move (uci "a1a8") .goal) (by decide +kernel)
example : ¬ Wins .white (fen "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1") :=  -- stalemate
  not_wins_of_stalemate (by decide +kernel) (by decide +kernel)
-- The diagnostic: nothing fails in the certificate above; `a1a7` is legal but does not mate, so
-- the leaf after it is not in the target; `a1h8` is not legal.
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1a8") .goal) == none
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1a7") .goal) == some ([uci "a1a7"], .notInTarget)
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1h8") .goal) == some ([], .unavailable (uci "a1h8"))

end Chess
