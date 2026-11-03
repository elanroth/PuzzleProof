import ChessDemo.Gotham
import ChessDemoBound.Gotham10.Claim

/-!
# The Gotham puzzle: mate in exactly 11

`ChessDemo.Gotham` proves that Black mates within 11. This file adds the other half: Black cannot
mate within 10. Together they give `MateIn .black 11 Puzzles.gotham`, mate in exactly 11, and its
reading with the rules alone (`SpecMateIn`, G8).

## Implementation notes

* The lower bound is the generated certificate `ChessDemoBound.Gotham10`, written by
  `scripts/gen_bound.py`: 24,994 node theorems over 21,417 positions. At every Black turn it lists
  every legal Black move (`Game.chess.moves p = [...]`, by `decide +kernel`) and refutes each one;
  at every White turn it closes the branch by one escape, by a forced mate of White's own (checked
  with every Black reply), by stalemate, or because Black has no moves left in the budget.
  Stockfish guided only White's side (which escape to try, where to look for White's mates);
  every Black move is covered whatever it suggested. The method and its measurements are in
  `docs/research/minimality.md`.
* Kernel only, like the rest of the demo: the axioms are `propext`, `Classical.choice` and
  `Quot.sound`, checked below.
-/

namespace ChessDemo

open Chess

/-- **The Gotham puzzle, no faster mate.** In `Puzzles.gotham`, Black cannot force mate within 10
moves of its own. -/
theorem gotham_not_winsIn_ten : ¬ WinsIn .black 10 Puzzles.gotham :=
  ChessDemoBound.Gotham10.notWinsIn

/-- **The Gotham puzzle, exactly.** In `Puzzles.gotham`, Black mates in exactly 11: within 11
moves of its own, and not within 10. -/
theorem gotham_mateIn : MateIn .black 11 Puzzles.gotham :=
  Game.MateIn.of_winsIn_of_not gotham_winsIn gotham_not_winsIn_ten

/-- **The Gotham puzzle, exactly, read with the rules alone (G8).** In `Puzzles.gotham`, Black can
force FIDE checkmate within 11 moves of its own and not within 10, every move being `Legal`. -/
theorem gotham_specMateIn : SpecMateIn .black 11 Puzzles.gotham :=
  mateIn_iff_specMateIn.mp gotham_mateIn

end ChessDemo

/-! ### Axioms -/

/--
info: 'ChessDemo.gotham_not_winsIn_ten' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_not_winsIn_ten
/-- info: 'ChessDemo.gotham_mateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.gotham_mateIn
/--
info: 'ChessDemo.gotham_specMateIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_specMateIn
