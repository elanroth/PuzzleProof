import ChessDemoBound.Tests.NoMoves.Claim
import ChessDemoBound.Tests.Stalemate.Claim

/-!
# Tests of the lower-bound generator

Two small certificates written by `scripts/gen_bound.py` for the two kinds of node that the Gotham
certificate never produces, so that a change to the generator or to the glue of `Chess.Game.Cert`
section `Bounds` that breaks them fails `lake build ChessDemoBound`:

* `Tests.NoMoves`: `k7/8/1Q6/8/8/8/8/7K b - - 0 1`, Black to move with no legal move (stalemated),
  does not mate within 1. The attacker node has an empty move list.
* `Tests.Stalemate`: `7k/8/8/8/8/8/4q3/7K b - - 0 1`, Black to move does not mate within 1. After
  `Qf2` White is stalemated, which closes that branch for every budget (`not_winsIn_of_stalemate`).

Regenerate with `scripts/gen_bound.py --budget 1 --root '(fen "<FEN>")' --import Chess.ChessGame
--module ChessDemoBound.Tests.<Name> --out ChessDemoBound/Tests/<Name>`.
-/

/--
info: 'ChessDemoBound.Tests.NoMoves.notWinsIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemoBound.Tests.NoMoves.notWinsIn
/--
info: 'ChessDemoBound.Tests.Stalemate.notWinsIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemoBound.Tests.Stalemate.notWinsIn
