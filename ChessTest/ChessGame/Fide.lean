import Chess.ChessGame.Fide

/-!
# Tests of `Chess.ChessGame.Fide`

The tests of `Chess.ChessGame.Fide`, moved out of the library module so that a library build does
not pay for them (`lake build ChessTest`). Specification: `docs/spec/ChessGame.Fide.md` §2.

## Implementation notes

* Kernel checks are `decide +kernel`. No `native_decide`.
-/

namespace Chess

-- A certificate checked through `Chess.Game` proves a mate in one under the FIDE rules.
example : SpecWinsIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") :=
  winsIn_iff_specWinsIn.1 <|
    Game.checkWin_sound (c := .move (uci "a1a8") .goal) (by decide +kernel)
-- Stalemate, decided through the generator (`Stalemate.decidableByGen`), is a win for nobody.
example : ¬ SpecWins .white (fen "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1") :=
  not_specWins_of_stalemate (by decide +kernel)

end Chess
