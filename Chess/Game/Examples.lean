import Chess.Game.Search
import Chess.Game.Cert

/-!
# Game: examples

Two take-away games on which every definition of `Chess.Game` runs instantly under `decide`, and
tests of the search, the checkers and the diagnostics on them. Specification: `docs/spec/Game.md`
§5.

## Main definitions

* `Game.Toy.takeAway`, `Game.Toy.takeAwayStalemate`: take one or two counters from a pile.

## Main statements

* `Game.Toy.takeAway_onlyWinningMove`: an only winning move, proved through the only-move checker.
-/

namespace Chess

namespace Game

/-! ## Examples -/

namespace Toy

/-- The take-away game: a state is the side to move and a pile of counters; a move takes one or two
counters; the side to move facing an empty pile has lost. -/
abbrev takeAway : Game where
  State := Color × Nat
  Move := Nat
  turn x := x.1
  moves x := [1, 2].filter (· ≤ x.2)
  play x t := (x.1.other, x.2 - t)
  Mated x := x.2 = 0
  turn_play _ := rfl
  moves_eq_nil_of_mated {x} h := by simp [h]

/-- The take-away game in which an empty pile with White to move is a loss for White; with Black to
move it is a stalemate. -/
abbrev takeAwayStalemate : Game where
  State := Color × Nat
  Move := Nat
  turn x := x.1
  moves x := [1, 2].filter (· ≤ x.2)
  play x t := (x.1.other, x.2 - t)
  Mated x := x.2 = 0 ∧ x.1 = .white
  turn_play _ := rfl
  moves_eq_nil_of_mated {x} h := by simp [h.1]

-- T1. From a pile of 4, White to move: White takes 1, and whatever Black takes, White takes the
-- rest. Two White moves, the mating one included.
example : takeAway.WinsIn .white 2 (.white, 4) := by decide

-- T2. Exact distance: two, and not fewer.
example : takeAway.MateIn .white 2 (.white, 4) := by decide

-- T3. A negative fact by search: from 3, White cannot force a win at any budget up to 5.
example : ¬ takeAway.WinsIn .white 5 (.white, 3) := by decide

-- T4. A mate leaf at budget 0: Black to move with an empty pile.
example : takeAway.WinsIn .white 0 (.black, 0) := by decide

-- T5. `not_both`: from 3 Black wins within 1, so White does not win at all.
example : ¬ takeAway.Wins .white (.white, 3) :=
  not_wins_of_winsIn_other (by decide : takeAway.WinsIn .black 1 (.white, 3))

-- T6. The checker accepts a correct certificate, in the kernel and by evaluation.
example : takeAway.checkWin .white 2 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) = true := by decide +kernel
example : takeAway.checkWin .white 2 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) = true := rfl

-- T7. The budget is enforced: the same certificate fails with budget 1.
example : takeAway.checkWin .white 1 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) = false := by decide

-- T8. A missing defender reply is rejected.
example : takeAway.checkWin .white 2 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal)])) = false := by decide

-- T9. The only-move checker accepts: taking 1 wins, and after taking 2 Black takes both and wins.
example : takeAway.checkOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [(2, .move 2 .goal)] } = true := by
  decide +kernel

-- T10. An unrefuted alternative is rejected.
example : takeAway.checkOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [] } = false := by
  decide

/-- Taking one counter is the only winning move from a pile of 4 with White to move, proved through
the only-move checker (T11). -/
theorem takeAway_onlyWinningMove : takeAway.OnlyWinningMove (.white, 4) 1 :=
  (checkOnlyMove_sound (by decide +kernel : takeAway.checkOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [(2, .move 2 .goal)] } = true)).1

-- T12. A stalemated defender has not lost.
example : ¬ takeAwayStalemate.Wins .white (.black, 0) :=
  not_wins_of_stalemate (by decide) rfl

-- T13. The search agrees on stalemate.
example : ¬ takeAwayStalemate.WinsIn .white 3 (.black, 0) := by decide

-- T14. The variant still has mates.
example : takeAwayStalemate.WinsIn .black 1 (.black, 1) := by decide

-- T15. The diagnostic finds nothing wrong with the certificate of T6.
example : takeAway.firstFailureWin .white 2 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) = none := by decide

-- T16. T7's rejection: after 1 and Black's 1, White has no budget left.
example : takeAway.firstFailureWin .white 1 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) =
      some ([1, 1], .noBudget) := by decide

-- T17. T8's rejection: after 1, Black's available move 2 has no pair.
example : takeAway.firstFailureWin .white 2 (.white, 4)
    (.move 1 (.replies [(1, .move 2 .goal)])) = some ([1], .missingReply 2) := by decide

-- T18. The other rejections of `checkForces`, one node each.
example : takeAway.firstFailureWin .white 2 (.white, 4) .goal = some ([], .notInTarget) := by
  decide
example : takeAway.firstFailureWin .white 2 (.black, 4) (.move 1 .goal) =
    some ([], .notAttackerTurn) := by decide
example : takeAway.firstFailureWin .white 2 (.white, 4) (.move 3 .goal) =
    some ([], .unavailable 3) := by decide
example : takeAway.firstFailureWin .white 2 (.white, 4) (.replies []) =
    some ([], .notDefenderTurn) := by decide
example : takeAwayStalemate.firstFailureWin .white 2 (.black, 0) (.replies []) =
    some ([], .noDefenderMove) := by decide

-- T19. The diagnostic of the only-move checker: nothing wrong with T9, T10's missing
-- refutation, and a refutation that fails after the refuted move 2.
example : takeAway.firstFailureOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [(2, .move 2 .goal)] } = none := by decide
example : takeAway.firstFailureOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [] } = some ([], .unrefuted 2) := by decide
example : takeAway.firstFailureOnlyMove 2 (.white, 4) 1
    { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)]
      refBudget := 1
      refs := [(2, .goal)] } = some ([2], .notInTarget) := by decide

-- T20. The glue of per-node proofs alone proves T1, one `have` per node as a generated file has
-- one theorem per node: the mate leaf, White's two finishing moves, Black's two replies, and
-- White's first move.
example : takeAway.WinsIn .white 2 (.white, 4) :=
  have w0 : takeAway.WinsIn .white 0 (.black, 0) := WinsIn.of_mated rfl rfl
  have w1 : takeAway.WinsIn .white 1 (.white, 1) :=
    Forces.move_of_play_eq rfl (by decide)
      (by decide : takeAway.play (.white, 1) 1 = (.black, 0)) w0
  have w2 : takeAway.WinsIn .white 1 (.white, 2) :=
    Forces.move_of_play_eq rfl (by decide)
      (by decide : takeAway.play (.white, 2) 2 = (.black, 0)) w0
  have w3 : takeAway.WinsIn .white 1 (.black, 3) :=
    Forces.replies_of_moves_eq rfl (by decide : takeAway.moves (.black, 3) = [1, 2]) <|
      Forces.forall_mem_cons (Forces.of_play_eq (by decide) w2) <|
        Forces.forall_mem_cons (Forces.of_play_eq (by decide) w1) Forces.forall_mem_nil
  Forces.move_of_play_eq rfl (by decide)
    (by decide : takeAway.play (.white, 4) 1 = (.black, 3)) w3

/-- From a pile of 4 with White to move, White does not win within 1, proved node by node with the
lower-bound glue alone (T21): White's two moves are listed, and after each one Black, to move and
not mated, has the budget 0 against it. -/
theorem takeAway_not_winsIn_one : ¬ takeAway.WinsIn .white 1 (.white, 4) :=
  not_winsIn_succ_of_moves_eq rfl (by decide : takeAway.moves (.white, 4) = [1, 2]) <|
    not_winsIn_forall_mem_cons (by decide : takeAway.play (.white, 4) 1 = (.black, 3))
      (not_winsIn_zero_of_defender rfl (by decide)) <|
    not_winsIn_forall_mem_cons (by decide : takeAway.play (.white, 4) 2 = (.black, 2))
      (not_winsIn_zero_of_defender rfl (by decide)) not_winsIn_forall_mem_nil

-- T22. With T1, the two halves give the exact distance T2.
example : takeAway.MateIn .white 2 (.white, 4) :=
  MateIn.of_winsIn_of_not (by decide) takeAway_not_winsIn_one

-- T23. One escape: from 4 with Black to move, Black takes 1, and from 3 White does not win within
-- 1 (by search); so White does not win within 1.
example : ¬ takeAway.WinsIn .white 1 (.black, 4) :=
  not_winsIn_of_escape rfl (by decide) (by decide : 1 ∈ takeAway.moves (.black, 4))
    (by decide : takeAway.play (.black, 4) 1 = (.white, 3)) (by decide)

-- T24. The defender's own win: White wins from 4 (T1), so Black does not win within any budget.
example (n : Nat) : ¬ takeAway.WinsIn .black n (.white, 4) :=
  not_winsIn_of_winsIn_other (a := .black) (by decide : takeAway.WinsIn .white 2 (.white, 4))

-- T25. Stalemate: Black to move facing an empty pile is not mated in `takeAwayStalemate`, so
-- nobody wins, at any budget; the budget can be lowered (`not_winsIn_mono`); and an attacker to
-- move with no budget left does not win (`not_winsIn_zero_of_turn`).
example (n : Nat) : ¬ takeAwayStalemate.WinsIn .white n (.black, 0) :=
  not_winsIn_of_stalemate (by decide) (by decide)
example (n : Nat) : ¬ takeAwayStalemate.WinsIn .black n (.black, 0) :=
  not_winsIn_of_stalemate (by decide) (by decide)
example : ¬ takeAway.WinsIn .white 0 (.white, 1) := not_winsIn_zero_of_turn rfl
example : ¬ takeAway.WinsIn .white 0 (.white, 4) :=
  not_winsIn_mono takeAway_not_winsIn_one (by decide)

end Toy

end Game

end Chess
