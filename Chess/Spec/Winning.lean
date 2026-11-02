import Chess.Rules

/-!
# Winning

Forced wins in chess, stated with the rules alone: the legal moves (`Legal`), the effect of a move
(`Position.play`) and checkmate (`Checkmate`) of `Chess.Rules`. No move generator and no abstract
game appear, so a reader who has checked `Chess.Rules` against the FIDE Laws can read a headline
theorem through these definitions. Specification: `docs/spec/Spec.Winning.md`; every definition
below carries the docstring given there.

## Main definitions

* `SpecForces a T n p`: from `p`, the side `a` forces play into the target `T` using at most `n`
  moves of its own. Three rules: the position is in the target; `a` is to move and has a legal move
  to a forced position; the other side is to move, has a legal move, and every legal move leads to a
  forced position.
* `SpecWinsIn`, `SpecWins`, `SpecMateIn`: forcing checkmate of the other side within a budget,
  within some budget, and in exactly a budget.
* `SpecOnlyWinningMove p m`: `m` is legal, the side to move wins after it, and after no other legal
  move.

## Main statements

* `specWinsIn_zero_iff`, `not_specWins_of_stalemate` (THEOREMS G2): checkmate is a win, and
  stalemate is a win for nobody. Both are proved from the definitions, without the generator.

## Implementation notes

* From Stage 2 on, these definitions are the trusted reading of a chess headline.
  `Chess.ChessGame.Fide` proves `Chess.WinsIn`, `Chess.Wins`, `Chess.MateIn` and
  `Chess.OnlyWinningMove`, which are computed through `legalMoves` and `Chess.Game`, equivalent to
  `SpecWinsIn`, `SpecWins`, `SpecMateIn` and `SpecOnlyWinningMove` (THEOREMS G8).
* The definitions are those of `Chess.Game` for `Game.chess`, written out: 'listed by
  `legalMoves`' becomes `Legal`, and 'in check with no listed move' becomes `Checkmate`. The rule
  for the other side demands a legal move, so a stalemated defender has not lost; budgets count the
  moves of `a` only, the mating move included.
* This is chess under FIDE's rules of movement and checkmate (Articles 3 and 5.1) only. There is no
  clock, no fifty- or seventy-five-move rule, no repetition rule and no dead-position rule.
* No decision procedure is given here. Claims are decided or certified through `Chess.Game` and
  carried over by the equivalences of `Chess.ChessGame.Fide`.
-/

namespace Chess

/-! ## Winning under the FIDE rules -/

/-- `SpecForces a T n p`: from position `p`, the side `a` can force play into the target `T` using
at most `n` moves of its own, whatever the other side does, the moves of both sides being the legal
moves of `Chess.Rules`. Moves of the other side cost nothing. `T` is tested at every position, `p`
included. The other side, to move with no legal move, escapes unless the position is in `T`, and
play that never reaches `T` is never forced. -/
inductive SpecForces (a : Color) (T : Position → Prop) : Nat → Position → Prop
  /-- A position in the target is forced, within any budget. -/
  | goal {n : Nat} {p : Position} : T p → SpecForces a T n p
  /-- If `a` is to move and some legal move leads to a position forced within `n`, the position is
  forced within `n + 1`. -/
  | move {n : Nat} {p : Position} (m : Move) : p.turn = a → Legal p m →
      SpecForces a T n (p.play m) → SpecForces a T (n + 1) p
  /-- If the other side is to move, has at least one legal move, and every legal move leads to a
  position forced within `n`, the position is forced within `n`. This rule never applies to a side
  with no legal move, so for `SpecWinsIn` a stalemated defender has not lost. -/
  | replies {n : Nat} {p : Position} : p.turn = a.other → (∃ m, Legal p m) →
      (∀ m, Legal p m → SpecForces a T n (p.play m)) → SpecForces a T n p

/-- `SpecWinsIn a n p`: from position `p`, whichever side is to move there, the side `a` can force
checkmate (FIDE 5.1.1) of the other side using at most `n` moves of its own, the mating move
included, whatever the other side plays, the moves of both sides being FIDE-legal moves. There is no
move-count, repetition or dead-position rule. -/
abbrev SpecWinsIn (a : Color) (n : Nat) (p : Position) : Prop :=
  SpecForces a (fun q => q.turn = a.other ∧ Checkmate q) n p

/-- `SpecWins a p`: from position `p`, the side `a` can force checkmate of the other side within
some number of its own moves, a bound fixed in advance (`∃ n, SpecWinsIn a n p`). -/
def SpecWins (a : Color) (p : Position) : Prop :=
  ∃ n, SpecWinsIn a n p

/-- `SpecMateIn a n p`: from position `p`, the side `a` mates in exactly `n`: it can force
checkmate of the other side within `n` moves of its own, and not within fewer. -/
def SpecMateIn (a : Color) (n : Nat) (p : Position) : Prop :=
  SpecWinsIn a n p ∧ ∀ k < n, ¬ SpecWinsIn a k p

/-- `SpecOnlyWinningMove p m`: `m` is legal at `p`, the side to move wins after `m`, and after
every other legal move it does not win. 'Other' means a different move value: promotions to
different pieces are different moves. An alternative that wins only slowly still counts as winning,
so it makes this false. -/
def SpecOnlyWinningMove (p : Position) (m : Move) : Prop :=
  Legal p m ∧ SpecWins p.turn (p.play m) ∧
    ∀ m', Legal p m' → m' ≠ m → ¬ SpecWins p.turn (p.play m')

/-! ## Checkmate and stalemate (THEOREMS G2) -/

section Laws

variable {a : Color} {p : Position}

/-- `SpecWinsIn a 0 p` holds exactly when the other side is to move at `p` and is checkmated: `a`
has already won. -/
theorem specWinsIn_zero_iff : SpecWinsIn a 0 p ↔ p.turn = a.other ∧ Checkmate p := by
  refine ⟨fun w => ?_, fun h => .goal h⟩
  cases w with
  | goal h => exact h
  | replies ht hl hw =>
    -- After a legal reply `a` is to move with no budget left, so the position reached would
    -- already have to be in the target, where the other side is to move.
    obtain ⟨m, hm⟩ := hl
    have hc : (p.play m).turn = a := by rw [play_turn, ht, Color.other_other]
    have w := hw m hm
    generalize p.play m = q at hc w
    cases w with
    | goal h => exact absurd (hc.symm.trans h.1) (Color.self_ne_other a)
    | replies ht' _ _ => exact absurd (hc.symm.trans ht') (Color.self_ne_other a)

/-- In a stalemate (FIDE 5.2.1), neither side wins. -/
theorem not_specWins_of_stalemate (h : Stalemate p) : ¬ SpecWins a p := by
  rintro ⟨n, w⟩
  cases w with
  | goal h' => exact h.1 h'.2.1
  | move m _ hm _ => exact h.2 m hm
  | replies _ hl _ => exact hl.elim h.2

end Laws

end Chess
