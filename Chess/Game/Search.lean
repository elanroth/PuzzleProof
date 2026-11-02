import Chess.Game.Laws

/-!
# Game: search

A bounded search that decides forcing for any decidable target, by structural recursion on the
budget, and its correctness. Specification: `docs/spec/Game.md` §3.

## Main definitions

* `Game.defenderStep`: the defender rule, given a test for the attacker nodes below it.
* `Game.attackerForces`, `Game.defenderForced`: the search for the side to move, as attacker and
  as defender.
* `Game.searchForces`: the search for a given attacker.

## Main statements

* `searchForces_iff` (G5): the search decides forcing.
* `Forces.decidable`, `MateIn.decidable`: hence forcing within a budget, and mating in exactly a
  budget, are decidable, and `decide` proves small claims.

## Implementation notes

* The search branches over every attacker move at every attacker node, so it is feasible only for
  small budgets. Long wins are proved by certificates (`Chess.Game.Cert`), which do not depend on
  this file.
-/

namespace Chess

namespace Game

/-! ## Search -/

section Search

/-- The rule at a defender node, given a test `atk` for the attacker nodes below it: `x` is in the
target, or the defender at `x` has an available move and every available move leads to a state
that passes `atk`. -/
def defenderStep (G : Game) (T : G.State → Prop) [DecidablePred T] (atk : G.State → Bool)
    (x : G.State) : Bool :=
  decide (T x) || (!(G.moves x).isEmpty && (G.moves x).all fun m => atk (G.play x m))

/-- Bounded search for the side to move: can the side to move at `x`, as attacker, force the target
within `n` moves of its own? With no budget, only if `x` is in the target; with budget `n + 1`, if
`x` is in the target or some available move leads to a state where the opponent, now to move, is
forced within `n`. -/
def attackerForces (G : Game) (T : G.State → Prop) [DecidablePred T] : Nat → G.State → Bool
  | 0, x => decide (T x)
  | n + 1, x => decide (T x) ||
      (G.moves x).any fun m => G.defenderStep T (G.attackerForces T n) (G.play x m)

/-- Bounded search for the opponent of the side to move: is the side to move at `x`, as defender,
forced into the target within `n` moves of the attacker? -/
def defenderForced (G : Game) (T : G.State → Prop) [DecidablePred T] (n : Nat) (x : G.State) :
    Bool :=
  G.defenderStep T (G.attackerForces T n) x

/-- Bounded search: decides whether the attacker `a` forces the target `T` within `n` moves of its
own from `x` (`searchForces_iff`). -/
def searchForces (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] (n : Nat)
    (x : G.State) : Bool :=
  if G.turn x = a then G.attackerForces T n x else G.defenderForced T n x

variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat} {x : G.State}

/-- At an attacker node with budget `n + 1`, the search asks whether `x` is in the target or some
move leads to a defender node that is forced within `n`. -/
theorem attackerForces_succ (n : Nat) (x : G.State) :
    G.attackerForces T (n + 1) x =
      (decide (T x) || (G.moves x).any fun m => G.defenderForced T n (G.play x m)) :=
  rfl

/-- If `atk` answers correctly for budget `n` at every attacker node, then the defender rule answers
correctly for budget `n` at every defender node. -/
theorem defenderStep_iff {atk : G.State → Bool}
    (hatk : ∀ y, G.turn y = a → (atk y = true ↔ G.Forces a T n y)) (ht : G.turn x = a.other) :
    G.defenderStep T atk x = true ↔ G.Forces a T n x := by
  rw [forces_defender_iff ht]
  simp only [defenderStep, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true]
  -- Every child of a defender node is an attacker node, where `atk` is correct.
  have hchild : ∀ m ∈ G.moves x, (atk (G.play x m) = true ↔ G.Forces a T n (G.play x m)) :=
    fun m hm => hatk _ (by rw [G.turn_play hm, ht, Color.other_other])
  exact or_congr Iff.rfl
    (and_congr_right fun _ => forall_congr' fun m => imp_congr_right (hchild m))

/-- At every state, the attacker search decides forcing for the side to move. -/
theorem attackerForces_iff : G.attackerForces T n x = true ↔ G.Forces (G.turn x) T n x := by
  induction n generalizing x with
  | zero => simp [attackerForces, forces_attacker_zero_iff rfl]
  | succ n ih =>
    rw [forces_attacker_succ_iff rfl]
    simp only [attackerForces, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
    -- Every child of an attacker node is a defender node, and below it the search is correct by
    -- the induction hypothesis.
    have hatk : ∀ y, G.turn y = G.turn x →
        (G.attackerForces T n y = true ↔ G.Forces (G.turn x) T n y) :=
      fun y hy => by rw [ih, hy]
    exact or_congr Iff.rfl (exists_congr fun _ =>
      and_congr_right fun hm => defenderStep_iff hatk (G.turn_play hm))

/-- At every state, the defender search decides forcing for the opponent of the side to move. -/
theorem defenderForced_iff :
    G.defenderForced T n x = true ↔ G.Forces (G.turn x).other T n x :=
  defenderStep_iff (fun _ hy => by rw [attackerForces_iff, hy]) (Color.other_other _).symm

/-- The search is correct at every state. THEOREMS G5. -/
theorem searchForces_iff : G.searchForces a T n x = true ↔ G.Forces a T n x := by
  unfold searchForces
  split
  · next ht => rw [attackerForces_iff, ht]
  · next ht => rw [defenderForced_iff, Color.eq_other_iff_ne.2 ht, Color.other_other]

/-- Forcing within a budget is decidable, by the bounded search `searchForces`. -/
instance Forces.decidable : Decidable (G.Forces a T n x) :=
  decidable_of_iff _ searchForces_iff

/-- Mating in exactly `n` is decidable, by searching each budget from 0 to `n`. -/
instance MateIn.decidable : Decidable (G.MateIn a n x) :=
  inferInstanceAs (Decidable (G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x))

end Search

end Game

end Chess
