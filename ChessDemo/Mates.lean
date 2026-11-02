import Chess.ChessGame

/-!
# Small exact mates

Exact `MateIn` claims about three small positions. That no shorter mate exists is decided by the
bounded search of `Chess.Game.Search` (`searchForces`, through the instances `Forces.decidable` and
`MateIn.decidable`) and evaluated by the kernel; so is the mate itself in 1 and in 2, while the
mate in 3 is proved by a checked certificate. Specification: `docs/spec/ChessDemo.Mates.md`;
every definition and theorem below carries the docstring given there.

## Main definitions

* `foolsMate`, `rookMate2`, `rookMate3`: the three positions.

## Main statements

* `foolsMate_mateIn`: after 1. f3 e5 2. g4, Black mates in exactly 1 (`Qh4#`).
* `rookMate2_mateIn`: White mates in exactly 2 (1. Rc6 Kh8 2. Rh6#).
* `rookMate3_mateIn`: White mates in exactly 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#).

## Implementation notes

* The search tries every move at every attacker node, in the order of `legalMoves`, and its kernel
  cost and memory grow quickly with the number of nodes it visits (measured: a mate in 2 whose
  search visits about 300 defender nodes took 7 GB). The positions were chosen, with a cost model
  that replays the search in this order, so that it visits few nodes.
* `rookMate3_mateIn` is split by `Game.mateIn_succ_iff` into a win within 3, proved by a
  certificate (`Game.checkWin_sound`), and no win within 2, proved by search. Deciding
  `MateIn .white 3 rookMate3` by search alone also works but took 48 s and 5.9 GB.
* Kernel only (`decide +kernel`); no `native_decide`.
-/

namespace ChessDemo

open Chess

/-- The position after 1. f3 e5 2. g4, Black to move. The en passant target `g3` is written, as
this library writes it after every two-square advance. -/
def foolsMate : Position := fen "rnbqkbnr/pppp1ppp/8/4p3/6P1/5P2/PPPPP2P/RNBQKBNR b KQkq g3 0 2"

/-- White: king f7, rook f6, pawn b4; Black: king h7. White to move. -/
def rookMate2 : Position := fen "8/5K1k/5R2/8/1P6/8/8/8 w - - 0 1"

/-- White: king f8, rook e2, pawn h6; Black: king h8, pawn h7. White to move. -/
def rookMate3 : Position := fen "5K1k/7p/7P/8/8/8/4R3/8 w - - 0 1"

/-- **Fool's mate.** After 1. f3 e5 2. g4, Black mates in exactly 1 (`Qh4#`). -/
theorem foolsMate_mateIn : MateIn .black 1 foolsMate := by decide +kernel

/-- **A mate in 2.** White mates in exactly 2 (1. Rc6 Kh8 2. Rh6#), and not in 1. -/
theorem rookMate2_mateIn : MateIn .white 2 rookMate2 := by decide +kernel

/-- White mates within 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#), by a checked certificate. -/
theorem rookMate3_winsIn : WinsIn .white 3 rookMate3 :=
  Game.checkWin_sound (c := .move (uci "f8e8") (.replies [(uci "h8g8",
    .move (uci "e2f2") (.replies [(uci "g8h8", .move (uci "f2f8") .goal)]))])) (by decide +kernel)

/-- White cannot mate within 2, by search. -/
theorem rookMate3_not_winsIn_two : ¬ WinsIn .white 2 rookMate3 := by decide +kernel

/-- **A mate in 3.** White mates in exactly 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#), and not in 2. -/
theorem rookMate3_mateIn : MateIn .white 3 rookMate3 :=
  Game.mateIn_succ_iff.mpr ⟨rookMate3_winsIn, rookMate3_not_winsIn_two⟩

end ChessDemo
