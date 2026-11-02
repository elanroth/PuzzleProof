import Chess.Game.Defs

/-!
# Game: laws

What follows from the definitions of `Chess.Game.Defs`: one step of forcing read backwards,
monotonicity in the budget and composition of forcing, that no state is won by both sides, that
stalemate is no loss, exact distance to mate, and the only winning move. Specification:
`docs/spec/Game.md` §2.

## Main statements

* `Forces.mono` (G3), `Forces.trans` (O8), `WinsIn.not_both` and `Wins.not_both` (G4),
  `winsIn_zero_iff` and `not_wins_of_stalemate` (G2), `MateIn.unique` (G6),
  `OnlyWinningMove.wins_iff` (O2).
* `forces_attacker_zero_iff`, `forces_attacker_succ_iff`, `forces_defender_iff`: one step of
  forcing, read backwards.
* `wins_attacker_iff`, `wins_defender_iff`: one step of winning, read backwards (for G9, G10).
* `OnlyWinningMove.of_refuted`: a move is the only winning move when it wins and the opponent wins
  after every other move. `OnlyWinningMove.winsIn_play`: a fastest win starts with it.

## Implementation notes

* Every proof goes by cases or induction on `Forces`; nothing here computes.
-/

namespace Chess

namespace Game

/-! ## Laws -/

section Laws

variable {G : Game} {a : Color} {T U : G.State → Prop} {n n' k : Nat} {x y : G.State}
  {m m' : G.Move} {ms : List G.Move}

/-! ### One step of forcing, read backwards -/

/-- The side to move is never both the attacker and the defender. -/
theorem turn_ne_both (ht : G.turn x = a) (ht' : G.turn x = a.other) : False :=
  Color.self_ne_other a (ht.symm.trans ht')

/-- With no budget left and the attacker to move, the attacker forces the target exactly when the
state is already in it. -/
theorem forces_attacker_zero_iff (ht : G.turn x = a) : G.Forces a T 0 x ↔ T x := by
  constructor
  · intro w
    cases w with
    | goal h => exact h
    | replies ht' _ _ => exact (turn_ne_both ht ht').elim
  · exact .goal

/-- With budget `n + 1` and the attacker to move, the attacker forces the target exactly when the
state is in it or some available move leads to a state forced within `n`. -/
theorem forces_attacker_succ_iff (ht : G.turn x = a) :
    G.Forces a T (n + 1) x ↔ T x ∨ ∃ m ∈ G.moves x, G.Forces a T n (G.play x m) := by
  constructor
  · intro w
    cases w with
    | goal h => exact .inl h
    | move m _ hm w => exact .inr ⟨m, hm, w⟩
    | replies ht' _ _ => exact (turn_ne_both ht ht').elim
  · rintro (h | ⟨m, hm, w⟩)
    · exact .goal h
    · exact .move m ht hm w

/-- With the defender to move, the attacker forces the target within `n` exactly when the state is
in it, or the defender has an available move and every available move leads to a state forced
within `n`. -/
theorem forces_defender_iff (ht : G.turn x = a.other) :
    G.Forces a T n x ↔
      T x ∨ (G.moves x ≠ [] ∧ ∀ m ∈ G.moves x, G.Forces a T n (G.play x m)) := by
  constructor
  · intro w
    cases w with
    | goal h => exact .inl h
    | move _ ht' _ _ => exact (turn_ne_both ht' ht).elim
    | replies _ hne hw => exact .inr ⟨hne, hw⟩
  · rintro (h | ⟨hne, hw⟩)
    · exact .goal h
    · exact .replies ht hne hw

/-! ### Budgets and targets -/

/-- More budget never hurts. THEOREMS G3. -/
theorem Forces.mono (w : G.Forces a T n x) (hn : n ≤ n') : G.Forces a T n' x := by
  induction w generalizing n' with
  | goal h => exact .goal h
  | move m ht hm _ ih =>
    obtain ⟨n', rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .move m ht hm (ih (by omega))
  | replies ht hne _ ih => exact .replies ht hne fun m hm => ih m hm hn

/-- If the attacker forces `T` within `n`, and from every state of `T` forces `U` within `k`, then
it forces `U` within `n + k`. THEOREMS O8. -/
theorem Forces.trans (w : G.Forces a T n x) (hT : ∀ y, T y → G.Forces a U k y) :
    G.Forces a U (n + k) x := by
  induction w with
  | goal h => exact (hT _ h).mono (Nat.le_add_left k _)
  | move m ht hm _ ih => rw [Nat.add_right_comm]; exact .move m ht hm ih
  | replies ht hne _ ih => exact .replies ht hne ih

/-- If after each move of the finite list `ms` the target is forced within some budget, then it is
forced after all of them within one budget, the largest. -/
theorem forces_common_budget (h : ∀ m ∈ ms, ∃ n, G.Forces a T n (G.play x m)) :
    ∃ n, ∀ m ∈ ms, G.Forces a T n (G.play x m) := by
  induction ms with
  | nil => exact ⟨0, fun _ hm => absurd hm List.not_mem_nil⟩
  | cons m ms ih =>
    obtain ⟨n, w⟩ := h m (List.mem_cons_self ..)
    obtain ⟨k, hk⟩ := ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    refine ⟨max n k, fun m' hm' => ?_⟩
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact w.mono (Nat.le_max_left n k)
    · exact (hk m' hm').mono (Nat.le_max_right n k)

/-! ### Winning -/

/-- With no budget, the attacker wins exactly when the defender is to move and has already been
mated. THEOREMS G2. -/
theorem winsIn_zero_iff : G.WinsIn a 0 x ↔ G.turn x = a.other ∧ G.Mated x := by
  by_cases ht : G.turn x = a
  · exact forces_attacker_zero_iff ht
  · have ht' : G.turn x = a.other := Color.eq_other_iff_ne.2 ht
    refine (forces_defender_iff ht').trans ⟨?_, .inl⟩
    rintro (h | ⟨hne, hw⟩)
    · exact h
    · -- The defender has a move; after it the attacker is to move with no budget, so it would
      -- already have to be the defender's turn there.
      obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
      have hc : G.turn (G.play x m) = a := by rw [G.turn_play hm, ht', Color.other_other]
      obtain ⟨hc', _⟩ := (forces_attacker_zero_iff hc).1 (hw m hm)
      exact (turn_ne_both hc hc').elim

/-- In a state with no available move, `a` wins exactly when the defender is to move and has been
mated. (This covers a mated attacker, a stalemated attacker and a stalemated defender.) -/
theorem wins_iff_of_moves_eq_nil (hl : G.moves x = []) :
    G.Wins a x ↔ G.turn x = a.other ∧ G.Mated x := by
  constructor
  · rintro ⟨n, w⟩
    cases w with
    | goal h => exact h
    | move _ _ hm _ => simp [hl] at hm
    | replies _ hne _ => exact absurd hl hne
  · exact fun h => ⟨0, .goal h⟩

/-- If the side to move has not been mated and has no available move (it is stalemated), the
attacker does not win, whichever side it is. THEOREMS G2. -/
theorem not_wins_of_stalemate (hnm : ¬ G.Mated x) (hl : G.moves x = []) : ¬ G.Wins a x :=
  fun h => hnm ((wins_iff_of_moves_eq_nil hl).1 h).2

/-- With the attacker to move, it wins exactly when some available move leads to a state it wins. -/
theorem wins_attacker_iff (ht : G.turn x = a) :
    G.Wins a x ↔ ∃ m ∈ G.moves x, G.Wins a (G.play x m) := by
  constructor
  · rintro ⟨n, w⟩
    cases w with
    | goal h => exact (turn_ne_both ht h.1).elim
    | move m _ hm w => exact ⟨m, hm, _, w⟩
    | replies ht' _ _ => exact (turn_ne_both ht ht').elim
  · rintro ⟨m, hm, n, w⟩
    exact ⟨n + 1, .move m ht hm w⟩

/-- With the defender to move, the attacker wins exactly when the defender has been mated, or the
defender has an available move and the attacker wins after every available move. -/
theorem wins_defender_iff (ht : G.turn x = a.other) :
    G.Wins a x ↔ G.Mated x ∨ (G.moves x ≠ [] ∧ ∀ m ∈ G.moves x, G.Wins a (G.play x m)) := by
  constructor
  · rintro ⟨n, w⟩
    rcases (forces_defender_iff ht).1 w with h | ⟨hne, hw⟩
    · exact .inl h.2
    · exact .inr ⟨hne, fun m hm => ⟨n, hw m hm⟩⟩
  · rintro (h | ⟨hne, hw⟩)
    · exact ⟨0, .goal ⟨ht, h⟩⟩
    · obtain ⟨n, w⟩ := forces_common_budget hw
      exact ⟨n, .replies ht hne w⟩

/-- No state is a forced win for both sides, whatever the two budgets. THEOREMS G4. -/
theorem WinsIn.not_both (w : G.WinsIn a n x) (w' : G.WinsIn a.other k x) : False := by
  induction w generalizing k with
  | goal h =>
    obtain ⟨ht, hmated⟩ := h
    cases w' with
    | goal h' => exact turn_ne_both (Color.other_other a ▸ h'.1) ht
    | move _ _ hm _ => simp [G.moves_eq_nil_of_mated hmated] at hm
    | replies ht' _ _ => exact turn_ne_both (Color.other_other a ▸ ht') ht
  | move m ht hm _ ih =>
    cases w' with
    | goal h' => simp [G.moves_eq_nil_of_mated h'.2] at hm
    | move _ ht' _ _ => exact turn_ne_both ht ht'
    | replies _ _ hw' => exact ih (hw' m hm)
  | replies ht _ _ ih =>
    cases w' with
    | goal h' => exact turn_ne_both (Color.other_other a ▸ h'.1) ht
    | move m' _ hm' w' => exact ih m' hm' w'
    | replies ht' _ _ => exact turn_ne_both (Color.other_other a ▸ ht') ht

/-- No state is won by both sides. THEOREMS G4. -/
theorem Wins.not_both (h : G.Wins a x) (h' : G.Wins a.other x) : False := by
  obtain ⟨n, w⟩ := h
  obtain ⟨k, w'⟩ := h'
  exact w.not_both w'

/-- If the opponent of `a` wins within some budget, then `a` does not win. -/
theorem not_wins_of_winsIn_other (w : G.WinsIn a.other k x) : ¬ G.Wins a x :=
  fun ⟨_, w'⟩ => w'.not_both w

/-! ### Exact distance -/

/-- Mating in exactly `n` and in exactly `k` from the same state forces `n = k`. THEOREMS G6. -/
theorem MateIn.unique (h : G.MateIn a n x) (h' : G.MateIn a k x) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | rfl | hlt
  · exact absurd h.1 (h'.2 n hlt)
  · rfl
  · exact absurd h'.1 (h.2 k hlt)

/-- Mating in exactly `n + 1` is winning within `n + 1` and not within `n`. THEOREMS G6. -/
theorem mateIn_succ_iff : G.MateIn a (n + 1) x ↔ G.WinsIn a (n + 1) x ∧ ¬ G.WinsIn a n x :=
  ⟨fun h => ⟨h.1, h.2 n (Nat.lt_succ_self n)⟩,
   fun h => ⟨h.1, fun _ hk w => h.2 (w.mono (by omega))⟩⟩

/-- Mating in exactly 0 is winning within 0. -/
theorem mateIn_zero_iff : G.MateIn a 0 x ↔ G.WinsIn a 0 x :=
  ⟨And.left, fun h => ⟨h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩⟩

/-- A side that wins mates in some exact number of moves. THEOREMS G6. -/
theorem Wins.exists_mateIn (h : G.Wins a x) : ∃ n, G.MateIn a n x := by
  obtain ⟨n, w⟩ := h
  induction n with
  | zero => exact ⟨0, mateIn_zero_iff.2 w⟩
  | succ n ih =>
    by_cases hn : G.WinsIn a n x
    · exact ih hn
    · exact ⟨n + 1, mateIn_succ_iff.2 ⟨w, hn⟩⟩

/-- Mating in exactly `n` implies winning. -/
theorem MateIn.wins (h : G.MateIn a n x) : G.Wins a x :=
  ⟨n, h.1⟩

/-! ### The only winning move -/

/-- If `m` is the only winning move at `x`, then for every available move `m'`, the side to move
wins after `m'` exactly when `m' = m`. THEOREMS O2. -/
theorem OnlyWinningMove.wins_iff (h : G.OnlyWinningMove x m) (hm' : m' ∈ G.moves x) :
    G.Wins (G.turn x) (G.play x m') ↔ m' = m :=
  ⟨fun hw => Decidable.byContradiction fun hdiff => h.2.2 m' hm' hdiff hw,
   fun he => he ▸ h.2.1⟩

/-- If `m` is the only winning move at `x`, the side to move wins at `x`. -/
theorem OnlyWinningMove.wins (h : G.OnlyWinningMove x m) : G.Wins (G.turn x) x :=
  let ⟨n, w⟩ := h.2.1
  ⟨n + 1, .move m rfl h.1 w⟩

/-- A state has at most one only winning move. -/
theorem OnlyWinningMove.unique (h : G.OnlyWinningMove x m) (h' : G.OnlyWinningMove x m') :
    m = m' :=
  (h'.wins_iff h.1).1 h.2.1

/-- If `m` is the only winning move at `x` and the side to move wins within `n + 1`, then it wins
within `n` after `m`: a fastest win starts with `m`. -/
theorem OnlyWinningMove.winsIn_play (h : G.OnlyWinningMove x m)
    (w : G.WinsIn (G.turn x) (n + 1) x) : G.WinsIn (G.turn x) n (G.play x m) := by
  rcases (forces_attacker_succ_iff rfl).1 w with h0 | ⟨m', hm', w'⟩
  · exact (turn_ne_both rfl h0.1).elim
  · exact (h.wins_iff hm').1 ⟨n, w'⟩ ▸ w'

/-- If `m` is available at `x`, the side to move wins within `n` after it, and after every other
available move the opponent wins within some budget, then `m` is the only winning move. -/
theorem OnlyWinningMove.of_refuted (hm : m ∈ G.moves x) (w : G.WinsIn (G.turn x) n (G.play x m))
    (hr : ∀ m' ∈ G.moves x, m' ≠ m → ∃ k, G.WinsIn (G.turn x).other k (G.play x m')) :
    G.OnlyWinningMove x m :=
  ⟨hm, ⟨n, w⟩, fun m' hm' hdiff =>
    let ⟨_, w'⟩ := hr m' hm' hdiff
    not_wins_of_winsIn_other w'⟩

end Laws

end Game

end Chess
