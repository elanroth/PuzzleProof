import Chess.Basic

/-!
# Game

Two-player games with alternating turns, forced play into a target, forced wins, a bounded search
that decides them, and a certificate checker whose acceptance proves them. Chess is one instance
(`Chess.ChessGame`); nothing here mentions a piece. Specification: `docs/spec/Game.md`; every
definition below carries the docstring given there.

## Main definitions

* `Game`: states, moves, the side to move, the available moves, the effect of a move, and when the
  side to move has been mated.
* `Game.Forces a T n x`: from `x`, the attacker `a` forces play into the target `T` using at most
  `n` moves of its own. Three rules: the state is in the target; the attacker has an available
  move to a forced state; the defender has an available move and all its available moves lead to
  forced states.
* `Game.WinsIn`, `Game.Wins`, `Game.MateIn`: forcing the defender to be mated, within a budget,
  within some budget, and in exactly a budget.
* `Game.OnlyWinningMove x m`: `m` is available, the side to move wins after it, and after no other
  available move.
* `Game.searchForces`: bounded search, by structural recursion on the budget.
* `Cert`, `Game.checkForces`, `Game.checkWin`, `Game.checkOnlyMove`: certificates proposed by an
  untrusted search, and their checkers.

## Main statements

* `Forces.mono` (G3), `WinsIn.not_both` and `Wins.not_both` (G4), `winsIn_zero_iff` and
  `not_wins_of_stalemate` (G2), `MateIn.unique` (G6), `OnlyWinningMove.wins_iff` (O2).
* `wins_attacker_iff`, `wins_defender_iff`: one step of winning, read backwards (for G9, G10).
* `searchForces_iff` (G5): the search decides forcing; hence `Forces` and `MateIn` are decidable.
* `checkForces_sound`, `checkForces_complete`, `checkWin_sound`, `checkWin_complete` (C1, C2), and
  `checkOnlyMove_sound` (C7).
* `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`, `Forces.of_play_eq` (C3): the glue for
  proofs that check one node at a time.

## Implementation notes

* The only way to lose is to be mated. A state with no available move that is not mated, and play
  that never ends, are wins for nobody. There is no clock, repetition or move-count rule: for
  chess, `Wins` ignores the fifty-move rule and repetition.
* The defender rule demands at least one available move, so a stalemated defender has not lost.
* Budgets count attacker moves only, the mating move included, and are always counted at the state
  of the claim.
* Only the definitions of the section "Games" are trusted. The search and the checkers are
  executable Boolean functions, each with a soundness theorem; the search and `checkForces` are
  also complete.
-/

namespace Chess

/-! ## Games -/

/-- A two-player game with alternating turns and finitely many moves in each state: its states, its
moves, the side to move, the moves available in each state, the effect of playing a move, and when
the side to move has been mated. The only way to lose is to be mated. A state with no available
move that is not mated, and endless play, are wins for nobody. There is no clock, repetition or
move-count rule. -/
structure Game where
  /-- The states of the game (for chess, positions). -/
  State : Type
  /-- The moves of the game, as data (for chess, a source, a destination and a promotion choice). -/
  Move : Type
  /-- The side to move in a state. -/
  turn : State → Color
  /-- The moves available to the side to move in a state, as a list. Only membership and emptiness
  of this list carry meaning; its order and any repetitions do not. An instance must not list two
  different values for the same move (for chess, two encodings of one castling), since
  `OnlyWinningMove` tells moves apart by their values. -/
  moves : State → List Move
  /-- The state after a move is played. It is total; its value at an unavailable move is
  unconstrained, and no trusted definition reads it. -/
  play : State → Move → State
  /-- The side to move has been mated: it has lost. -/
  Mated : State → Prop
  /-- Whether the side to move has been mated is decidable. -/
  [decMated : DecidablePred Mated]
  /-- Equality of moves is decidable. -/
  [decEqMove : DecidableEq Move]
  /-- Playing an available move passes the turn to the other side. -/
  turn_play : ∀ {x : State} {m : Move}, m ∈ moves x → turn (play x m) = (turn x).other
  /-- In a state where the side to move has been mated, no move is available. -/
  moves_eq_nil_of_mated : ∀ {x : State}, Mated x → moves x = []

-- Structure fields are not instances on their own. Without this line every decision about `Mated`
-- or about equality of moves would need `classical` or an explicit argument.
attribute [instance] Game.decMated Game.decEqMove

namespace Game

/-- In state `x` the defender `a.other` is to move and has been mated. -/
def DefenderMated (G : Game) (a : Color) (x : G.State) : Prop :=
  G.turn x = a.other ∧ G.Mated x

/-- Whether the defender has been mated is decidable. -/
instance DefenderMated.decidable (G : Game) (a : Color) : DecidablePred (G.DefenderMated a) :=
  fun x => inferInstanceAs (Decidable (G.turn x = a.other ∧ G.Mated x))

/-- `G.Forces a T n x`: from state `x`, the attacker `a` can force play into the target `T` using at
most `n` moves of its own, whatever the defender `a.other` does. Defender moves cost nothing. `T` is
tested at every state, `x` included. A defender to move with no available move outside `T` escapes,
and play that never reaches `T` is never forced. -/
inductive Forces (G : Game) (a : Color) (T : G.State → Prop) : Nat → G.State → Prop
  /-- A state in the target is forced, within any budget. -/
  | goal {n : Nat} {x : G.State} : T x → G.Forces a T n x
  /-- If the attacker is to move and some available move leads to a state forced within `n`, the
  state is forced within `n + 1`. -/
  | move {n : Nat} {x : G.State} (m : G.Move) : G.turn x = a → m ∈ G.moves x →
      G.Forces a T n (G.play x m) → G.Forces a T (n + 1) x
  /-- If the defender is to move, has at least one available move, and every available move leads
  to a state forced within `n`, the state is forced within `n`. This rule never applies to a
  defender with no available move. Such a state is forced only if it is already in the target, so
  for `WinsIn` a stalemated defender has not lost. -/
  | replies {n : Nat} {x : G.State} : G.turn x = a.other → G.moves x ≠ [] →
      (∀ m ∈ G.moves x, G.Forces a T n (G.play x m)) → G.Forces a T n x

/-- `G.WinsIn a n x`: from state `x`, the attacker `a` can force the defender to be mated using at
most `n` moves of its own, the mating move included. -/
abbrev WinsIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop :=
  G.Forces a (G.DefenderMated a) n x

/-- `G.Wins a x`: from state `x`, the attacker `a` can force the defender to be mated within a
bound: there is a number `n` such that `G.WinsIn a n x`. -/
def Wins (G : Game) (a : Color) (x : G.State) : Prop :=
  ∃ n, G.WinsIn a n x

/-- `G.MateIn a n x`: from state `x`, the attacker `a` mates in exactly `n`: it can force mate
within `n` moves of its own and not within fewer. -/
def MateIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop :=
  G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x

/-- `G.OnlyWinningMove x m`: `m` is available in state `x`, the side to move wins after `m`, and
after every other available move it does not win. 'Other' means a different value of `G.Move`, so
if another available move also wins, however slowly, there is no only winning move; in particular
there is none when two promotions both win. -/
def OnlyWinningMove (G : Game) (x : G.State) (m : G.Move) : Prop :=
  m ∈ G.moves x ∧ G.Wins (G.turn x) (G.play x m) ∧
    ∀ m' ∈ G.moves x, m' ≠ m → ¬ G.Wins (G.turn x) (G.play x m')

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

/-! ## Certificates -/

/-- A certificate for a forcing claim: a finite strategy tree for the attacker, proposed by an
untrusted search and checked by `Game.checkForces`. It is data; it is never trusted. -/
inductive Cert (M : Type) where
  /-- The state is in the target. -/
  | goal
  /-- The attacker plays `m`; `next` is the certificate for the state after it. -/
  | move (m : M) (next : Cert M)
  /-- The defender is to move; each pair `(m, c)` of `rs` gives the certificate `c` for the state
  after the defender's move `m`. Pairs for moves that are not available, and repeated moves, are
  allowed; every pair must check. -/
  | replies (rs : List (M × Cert M))
  deriving Inhabited

namespace Game

-- `checkReplies` walks the reply list by hand instead of calling `List.all`: structural recursion
-- cannot pass through `List.all` over the nested `List (G.Move × Cert G.Move)`, and the
-- hand-written recursion keeps the checker reducible by the kernel (`decide +kernel`, `rfl`).
mutual

/-- Checks certificate `c` for the claim `G.Forces a T n x`, one rule of forcing per constructor. A
`goal` leaf needs `x` to be in the target. A `move m next` node needs the attacker to be to move, a
budget of the form `k + 1`, `m` to be available, and `next` to check after `m` with budget `k`. A
`replies rs` node needs the defender to be to move and to have an available move, every available
move to appear in `rs` (as the first component of some pair), and every certificate in `rs` to
check after its move with the same budget `n`. Pairs for moves that are not available, and repeated
moves, are allowed; every pair must check. -/
def checkForces (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → Cert G.Move → Bool
  | _, x, .goal => decide (T x)
  | 0, _, .move _ _ => false
  | k + 1, x, .move m next =>
      decide (G.turn x = a) && decide (m ∈ G.moves x) && G.checkForces a T k (G.play x m) next
  | n, x, .replies rs =>
      decide (G.turn x = a.other) && decide (G.moves x ≠ []) &&
        decide (∀ m ∈ G.moves x, m ∈ rs.map Prod.fst) && G.checkReplies a T n x rs

/-- Checks every pair `(m, c)` of `rs`: the certificate `c` checks, with budget `n`, in the state
after `m` is played at `x`. -/
def checkReplies (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → List (G.Move × Cert G.Move) → Bool
  | _, _, [] => true
  | n, x, (m, c) :: rs => G.checkForces a T n (G.play x m) c && G.checkReplies a T n x rs

end

/-- Checks certificate `c` for the claim `G.WinsIn a n x`. -/
def checkWin (G : Game) (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) : Bool :=
  G.checkForces a (G.DefenderMated a) n x c

/-- Accepts only if `best` is the only winning move at `x` and the side to move wins within `n`
moves, counted at `x` with `best` included. Accepting proves both (`checkOnlyMove_sound`). `next` is
the win certificate for the state after `best`; `refs` gives, for every other available move, a
certificate that the opponent wins within `k` moves after it. It rejects true claims in which some
alternative does not lose but only draws: this checker cannot certify those, and refutations by
traps are future work. -/
def checkOnlyMove (G : Game) (n k : Nat) (x : G.State) (best : G.Move) (next : Cert G.Move)
    (refs : List (G.Move × Cert G.Move)) : Bool :=
  G.checkWin (G.turn x) n x (.move best next) &&
    decide (∀ m ∈ G.moves x, m ≠ best → m ∈ refs.map Prod.fst) &&
    refs.all fun r => G.checkWin (G.turn x).other k (G.play x r.1) r.2

section Certificates

variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n k : Nat}
  {x : G.State} {best : G.Move} {c next : Cert G.Move} {refs : List (G.Move × Cert G.Move)}

mutual

/-- If the checker accepts a certificate, the attacker forces the target. THEOREMS C1. -/
theorem checkForces_sound : ∀ {n : Nat} {x : G.State} (c : Cert G.Move),
    G.checkForces a T n x c = true → G.Forces a T n x
  | _, _, .goal, h => .goal (by simpa [checkForces] using h)
  | 0, _, .move _ _, h => by simp [checkForces] at h
  | _ + 1, _, .move m next, h => by
    simp only [checkForces, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .move m h.1.1 h.1.2 (checkForces_sound next h.2)
  | _, _, .replies rs, h => by
    simp only [checkForces, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ht, hne⟩, hcov⟩, hrs⟩ := h
    refine .replies ht hne fun m hm => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (hcov m hm)
    exact checkReplies_sound rs hrs r hr

/-- If every pair of a reply list checks, the attacker forces the target after each listed move. -/
theorem checkReplies_sound : ∀ {n : Nat} {x : G.State} (rs : List (G.Move × Cert G.Move)),
    G.checkReplies a T n x rs = true → ∀ r ∈ rs, G.Forces a T n (G.play x r.1)
  | _, _, [], _ => by simp
  | _, _, (_, c) :: rs, h => by
    simp only [checkReplies, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact checkForces_sound c h.1
    · exact checkReplies_sound rs h.2 r hr

end

/-- If after each move of `ms` some certificate checks with budget `n`, then some reply list whose
moves are exactly `ms`, in the same order, checks. -/
theorem exists_checkReplies (ms : List G.Move)
    (h : ∀ m ∈ ms, ∃ c, G.checkForces a T n (G.play x m) c = true) :
    ∃ rs : List (G.Move × Cert G.Move),
      rs.map Prod.fst = ms ∧ G.checkReplies a T n x rs = true := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨c, hc⟩ := h m (List.mem_cons_self ..)
    obtain ⟨rs, hrs, hcheck⟩ := ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    exact ⟨(m, c) :: rs, by simp [hrs], by simp [checkReplies, hc, hcheck]⟩

/-- Every true forcing claim has an accepted certificate: the format is not lossy. THEOREMS C2. -/
theorem checkForces_complete (w : G.Forces a T n x) : ∃ c, G.checkForces a T n x c = true := by
  induction w with
  | goal h => exact ⟨.goal, by simp [checkForces, h]⟩
  | move m ht hm _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨.move m c, by simp [checkForces, ht, hm, hc]⟩
  | replies ht hne _ ih =>
    obtain ⟨rs, hrs, hcheck⟩ := exists_checkReplies _ ih
    exact ⟨.replies rs, by simp [checkForces, ht, hne, hrs, hcheck]⟩

/-- If the checker accepts a win certificate, the attacker wins within the budget. THEOREMS C1. -/
theorem checkWin_sound (h : G.checkWin a n x c = true) : G.WinsIn a n x :=
  checkForces_sound c h

/-- Every forced win has an accepted win certificate. THEOREMS C2. -/
theorem checkWin_complete (w : G.WinsIn a n x) : ∃ c, G.checkWin a n x c = true :=
  checkForces_complete w

/-- If the only-move checker accepts, `best` is the only winning move at `x` and the side to move
wins within `n`. THEOREMS C7. -/
theorem checkOnlyMove_sound (h : G.checkOnlyMove n k x best next refs = true) :
    G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x := by
  simp only [checkOnlyMove, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hwin, hcov⟩, hrefs⟩ := h
  refine ⟨?_, checkWin_sound hwin⟩
  -- The root of the win certificate is `best`, played with a budget of the form `n + 1`.
  cases n with
  | zero => simp [checkWin, checkForces] at hwin
  | succ n =>
    simp only [checkWin, checkForces, Bool.and_eq_true, decide_eq_true_eq] at hwin
    obtain ⟨⟨_, hm⟩, hnext⟩ := hwin
    refine OnlyWinningMove.of_refuted hm (checkForces_sound next hnext) fun m hm' hdiff => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (hcov m hm' hdiff)
    exact ⟨k, checkWin_sound (hrefs r hr)⟩

end Certificates

/-! ### Lemmas for per-node kernel proofs -/

section PerNode

variable {G : Game} {a : Color} {T : G.State → Prop} {n : Nat} {x y : G.State}
  {m : G.Move} {ms : List G.Move}

/-- If playing `m` at `x` gives `y`, every forcing fact about `y` holds after `m`. THEOREMS C3. -/
theorem Forces.of_play_eq (h : G.play x m = y) (w : G.Forces a T n y) :
    G.Forces a T n (G.play x m) :=
  h ▸ w

/-- Attacker node: if the attacker is to move, `m` is available, playing it gives `y`, and `y` is
forced within `n`, then `x` is forced within `n + 1`. THEOREMS C3. -/
theorem Forces.move_of_play_eq (ht : G.turn x = a) (hm : m ∈ G.moves x) (h : G.play x m = y)
    (w : G.Forces a T n y) : G.Forces a T (n + 1) x :=
  .move m ht hm (h ▸ w)

/-- Defender node: if the defender is to move, its available moves are the explicit non-empty list
`m :: ms`, and each of them leads to a state forced within `n`, then `x` is forced within `n`.
THEOREMS C3. -/
theorem Forces.replies_of_moves_eq (ht : G.turn x = a.other) (hl : G.moves x = m :: ms)
    (h : ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m')) : G.Forces a T n x :=
  .replies ht (by rw [hl]; exact List.cons_ne_nil _ _) (by rw [hl]; exact h)

end PerNode

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
example : takeAway.checkOnlyMove 2 1 (.white, 4) 1
    (.replies [(1, .move 2 .goal), (2, .move 1 .goal)]) [(2, .move 2 .goal)] = true := by
  decide +kernel

-- T10. An unrefuted alternative is rejected.
example : takeAway.checkOnlyMove 2 1 (.white, 4) 1
    (.replies [(1, .move 2 .goal), (2, .move 1 .goal)]) [] = false := by decide

/-- Taking one counter is the only winning move from a pile of 4 with White to move, proved through
the only-move checker (T11). -/
theorem takeAway_onlyWinningMove : takeAway.OnlyWinningMove (.white, 4) 1 :=
  (checkOnlyMove_sound (by decide +kernel : takeAway.checkOnlyMove 2 1 (.white, 4) 1
    (.replies [(1, .move 2 .goal), (2, .move 1 .goal)]) [(2, .move 2 .goal)] = true)).1

-- T12. A stalemated defender has not lost.
example : ¬ takeAwayStalemate.Wins .white (.black, 0) :=
  not_wins_of_stalemate (by decide) rfl

-- T13. The search agrees on stalemate.
example : ¬ takeAwayStalemate.WinsIn .white 3 (.black, 0) := by decide

-- T14. The variant still has mates.
example : takeAwayStalemate.WinsIn .black 1 (.black, 1) := by decide

end Toy

end Game

end Chess
