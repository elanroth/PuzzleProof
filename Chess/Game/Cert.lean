import Chess.Game.Laws

/-!
# Game: certificates

Certificates for forcing claims, proposed by an untrusted search; the Boolean checkers that replay
them against the rules of the game; the lemmas that turn acceptance into the claim; and diagnostics
that say where a rejected certificate fails. This file is the interface of generated certificate
files. Specification: `docs/spec/Game.md` §4; every definition below carries the docstring given
there.

## Main definitions

* `Cert`: a finite strategy tree for the attacker.
* `OnlyMoveCert`: the evidence for an only-move claim, a win certificate after the best move and
  refutations of the other moves.
* `Game.checkForces`, `Game.checkWin`, `Game.checkOnlyMove`: the checkers.
* `Game.firstFailure`, `Game.firstFailureWin`, `Game.firstFailureOnlyMove`: the path to the first
  node a checker rejects, and the condition that fails there (`Cert.Rejection`).

## Main statements

* `checkForces_sound`, `checkForces_complete`, `checkWin_sound`, `checkWin_complete` (C1, C2), and
  `checkOnlyMove_sound` (C7).
* `Forces.of_play_eq`, `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`,
  `Forces.forall_mem_cons`, `Forces.forall_mem_nil`, `WinsIn.of_mated`, and for the root of an
  only-move claim `OnlyWinningMove.of_moves_eq`, `.refuted_nil`, `.refuted_cons_self`,
  `.refuted_cons` (C3): the glue for proofs that check one node at a time.
* `not_winsIn_zero_of_turn`, `not_winsIn_succ_of_moves_eq`, `not_winsIn_of_escape`,
  `not_winsIn_zero_of_defender`, `not_winsIn_of_stalemate`, `not_winsIn_of_winsIn_other`,
  `not_winsIn_forall_mem_nil`, `not_winsIn_forall_mem_cons`, `not_winsIn_mono`,
  `MateIn.of_winsIn_of_not` (C9): the
  glue for lower bounds, "the attacker does not win within `n`", checked one node at a time: every
  attacker move is refuted, and the defender answers with one escape or a win of its own.
* `firstFailure_eq_none_iff`, `firstFailureOnlyMove_eq_none_iff`: the diagnostics find a failure
  exactly when the checkers reject.

## Implementation notes

* Nothing here is trusted. The checkers are executable Boolean functions with soundness theorems,
  and `checkForces` is also complete. The diagnostics are for reading a rejected certificate; no
  theorem about a game depends on them.
* The generated-file interface (`docs/spec/Game.md` §4.3). A generated certificate file states its
  claims with the definitions of `Chess.Game.Defs` (for chess, their abbreviations in
  `Chess.ChessGame`), writes its certificates as values of `Cert` and `OnlyMoveCert`, and proves
  its claims only through `checkWin_sound`, `checkOnlyMove_sound`, the glue lemmas above,
  `OnlyWinningMove.of_refuted`, literal checkpoint equations for `Position.play` and
  `Game.chess.moves` proved by `decide +kernel`, and for chess `mem_chess_moves`. It never applies
  a constructor of `Forces`, so the constructors may change. The test file `ChessTest.Interface`
  records the signatures of these names.
-/

namespace Chess

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

/-- The evidence for an only-move claim, proposed by an untrusted search and checked by
`Game.checkOnlyMove`: a win certificate for the state after the best move, and refutations of the
other moves. The claim itself (the state, the best move and the budget of the win) is not part of
it. It is data; it is never trusted. -/
structure OnlyMoveCert (M : Type) where
  /-- The win certificate for the state after the best move. -/
  next : Cert M
  /-- The budget within which the opponent wins after each refuted move; one budget serves them
  all. -/
  refBudget : Nat
  /-- For each refuted move `m`, a certificate that the opponent wins within `refBudget` after `m`.
  Pairs for moves that are not available, and repeated moves, are allowed; every pair must
  check. -/
  refs : List (M × Cert M)
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
moves, counted at `x` with `best` included. Accepting proves both (`checkOnlyMove_sound`).
`oc.next` is the win certificate for the state after `best`; `oc.refs` gives, for every other
available move, a certificate that the opponent wins within `oc.refBudget` moves after it. It
rejects true claims in which some alternative does not lose but only draws: this checker cannot
certify those, and refutations by traps are future work. -/
def checkOnlyMove (G : Game) (n : Nat) (x : G.State) (best : G.Move) (oc : OnlyMoveCert G.Move) :
    Bool :=
  G.checkWin (G.turn x) n x (.move best oc.next) &&
    decide (∀ m ∈ G.moves x, m ≠ best → m ∈ oc.refs.map Prod.fst) &&
    oc.refs.all fun r => G.checkWin (G.turn x).other oc.refBudget (G.play x r.1) r.2

section Certificates

variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat}
  {x : G.State} {best : G.Move} {c : Cert G.Move} {oc : OnlyMoveCert G.Move}

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

/-- Every pair of a reply list checks exactly when each certificate in it checks after its move. -/
theorem checkReplies_eq_true_iff {rs : List (G.Move × Cert G.Move)} :
    G.checkReplies a T n x rs = true ↔ ∀ r ∈ rs, G.checkForces a T n (G.play x r.1) r.2 = true := by
  induction rs with
  | nil => simp [checkReplies]
  | cons r rs ih => simp [checkReplies, ih]

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
theorem checkOnlyMove_sound (h : G.checkOnlyMove n x best oc = true) :
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
    refine OnlyWinningMove.of_refuted hm (checkForces_sound oc.next hnext) fun m hm' hdiff => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (hcov m hm' hdiff)
    exact ⟨oc.refBudget, checkWin_sound (hrefs r hr)⟩

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

/-- Mate leaf: if the defender is to move and has been mated, the attacker wins within any budget.
THEOREMS C3. -/
theorem WinsIn.of_mated (ht : G.turn x = a.other) (h : G.Mated x) : G.WinsIn a n x :=
  .goal ⟨ht, h⟩

/-- The end of a defender's move list: every move of the empty list leads to a state forced within
`n`. THEOREMS C3. -/
theorem Forces.forall_mem_nil : ∀ m' ∈ ([] : List G.Move), G.Forces a T n (G.play x m') :=
  fun _ h => nomatch h

/-- One move of a defender's move list: if `m` leads to a state forced within `n`, and so does
every move of `ms`, then so does every move of `m :: ms`. THEOREMS C3. -/
theorem Forces.forall_mem_cons (h : G.Forces a T n (G.play x m))
    (t : ∀ m' ∈ ms, G.Forces a T n (G.play x m')) :
    ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m') :=
  List.forall_mem_cons.2 ⟨h, t⟩

/-- Only-move root: if `a` is to move, its available moves are the explicit list `ms`, `m` is one
of them, `a` wins within `n` after `m`, and after every other move of `ms` the opponent wins within
some budget, then `m` is the only winning move at `x`. THEOREMS C3. -/
theorem OnlyWinningMove.of_moves_eq (ht : G.turn x = a) (hl : G.moves x = ms) (hm : m ∈ ms)
    (w : G.WinsIn a n (G.play x m))
    (hr : ∀ m' ∈ ms, m' ≠ m → ∃ k, G.WinsIn a.other k (G.play x m')) :
    G.OnlyWinningMove x m := by
  subst ht hl
  exact OnlyWinningMove.of_refuted hm w hr

/-- The end of a list of alternatives: every move of the empty list other than `m` is refuted.
THEOREMS C3. -/
theorem OnlyWinningMove.refuted_nil :
    ∀ m' ∈ ([] : List G.Move), m' ≠ m → ∃ k, G.WinsIn a k (G.play x m') :=
  fun _ h => nomatch h

/-- The move `m` itself in a list of alternatives: if every move of `ms` other than `m` is refuted,
so is every move of `m :: ms` other than `m`. THEOREMS C3. -/
theorem OnlyWinningMove.refuted_cons_self
    (t : ∀ m' ∈ ms, m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')) :
    ∀ m' ∈ m :: ms, m' ≠ m → ∃ k, G.WinsIn a k (G.play x m') :=
  List.forall_mem_cons.2 ⟨fun h => (h rfl).elim, t⟩

/-- One refuted move in a list of alternatives: if the opponent `a` wins within `k` after `m'`,
and every move of `ms` other than `m` is refuted, then so is every move of `m' :: ms` other than
`m`. THEOREMS C3. -/
theorem OnlyWinningMove.refuted_cons {m' : G.Move} {k : Nat} (w : G.WinsIn a k (G.play x m'))
    (t : ∀ m'' ∈ ms, m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'')) :
    ∀ m'' ∈ m' :: ms, m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'') :=
  List.forall_mem_cons.2 ⟨fun _ => ⟨k, w⟩, t⟩

end PerNode

/-! ### Lemmas for per-node proofs of lower bounds -/

section Bounds

variable {G : Game} {a : Color} {n k : Nat} {x y : G.State} {m : G.Move} {ms : List G.Move}

/-- Attacker node with no budget: the attacker, to move, does not win within `0`. THEOREMS C9. -/
theorem not_winsIn_zero_of_turn (ht : G.turn x = a) : ¬ G.WinsIn a 0 x := fun w =>
  turn_ne_both ht ((forces_attacker_zero_iff ht).1 w).1

/-- Attacker node: if the attacker is to move, its available moves are the explicit list `ms`, and
after none of them does it win within `n`, it does not win within `n + 1`. THEOREMS C9. -/
theorem not_winsIn_succ_of_moves_eq (ht : G.turn x = a) (hl : G.moves x = ms)
    (h : ∀ m ∈ ms, ¬ G.WinsIn a n (G.play x m)) : ¬ G.WinsIn a (n + 1) x := by
  intro w'
  rcases (forces_attacker_succ_iff ht).1 w' with h' | ⟨m, hm, w⟩
  · exact turn_ne_both ht h'.1
  · exact h m (hl ▸ hm) w

/-- Defender node, one escape: if the defender is to move and has not been mated, `m` is
available, playing it gives `y`, and the attacker does not win within `n` from `y`, then the
attacker does not win within `n` from `x`. THEOREMS C9. -/
theorem not_winsIn_of_escape (ht : G.turn x = a.other) (hnm : ¬ G.Mated x) (hm : m ∈ G.moves x)
    (h : G.play x m = y) (w : ¬ G.WinsIn a n y) : ¬ G.WinsIn a n x := by
  intro w'
  rcases (forces_defender_iff ht).1 w' with h' | ⟨_, hw⟩
  · exact hnm h'.2
  · exact w (h ▸ hw m hm)

/-- Defender node with no budget: if the defender is to move and has not been mated, the attacker
does not win within `0`. THEOREMS C9. -/
theorem not_winsIn_zero_of_defender (ht : G.turn x = a.other) (hnm : ¬ G.Mated x) :
    ¬ G.WinsIn a 0 x := by
  intro w'
  rcases (forces_defender_iff ht).1 w' with h' | ⟨hne, hw⟩
  · exact hnm h'.2
  · obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
    have hc : G.turn (G.play x m) = a := by rw [G.turn_play hm, ht, Color.other_other]
    exact not_winsIn_zero_of_turn hc (hw m hm)

/-- Stalemate: if the side to move has no available move and has not been mated, nobody wins
within any budget. THEOREMS C9. -/
theorem not_winsIn_of_stalemate (hnm : ¬ G.Mated x) (hl : G.moves x = []) : ¬ G.WinsIn a n x :=
  fun w => not_wins_of_stalemate hnm hl ⟨n, w⟩

/-- The defender's own win: if the other side wins within `k`, the attacker does not win within
`n`. THEOREMS C9. -/
theorem not_winsIn_of_winsIn_other (w : G.WinsIn a.other k x) : ¬ G.WinsIn a n x :=
  fun w' => w'.not_both w

/-- The end of an attacker's move list: after no move of the empty list does the attacker win
within `n`. THEOREMS C9. -/
theorem not_winsIn_forall_mem_nil : ∀ m' ∈ ([] : List G.Move), ¬ G.WinsIn a n (G.play x m') :=
  fun _ h => nomatch h

/-- One move of an attacker's move list: if playing `m` gives `y`, the attacker does not win within
`n` from `y`, and the same holds after every move of `ms`, then it holds after every move of
`m :: ms`. THEOREMS C9. -/
theorem not_winsIn_forall_mem_cons (h : G.play x m = y) (w : ¬ G.WinsIn a n y)
    (t : ∀ m' ∈ ms, ¬ G.WinsIn a n (G.play x m')) :
    ∀ m' ∈ m :: ms, ¬ G.WinsIn a n (G.play x m') :=
  List.forall_mem_cons.2 ⟨h ▸ w, t⟩

/-- A smaller budget: if the attacker does not win within `n`, it does not win within any `k ≤ n`.
THEOREMS C9. -/
theorem not_winsIn_mono (h : ¬ G.WinsIn a n x) (hk : k ≤ n) : ¬ G.WinsIn a k x :=
  fun w => h (w.mono hk)

/-- Exact distance from the two halves: winning within `n + 1` and not within `n`. THEOREMS C9. -/
theorem MateIn.of_winsIn_of_not (w : G.WinsIn a (n + 1) x) (h : ¬ G.WinsIn a n x) :
    G.MateIn a (n + 1) x :=
  mateIn_succ_iff.2 ⟨w, h⟩

end Bounds

end Game

/-! ## Diagnostics -/

/-- Why a checker rejects a certificate: the condition of `Game.checkForces` or
`Game.checkOnlyMove` that fails at the node where checking stops. Reported by `Game.firstFailure`
and `Game.firstFailureOnlyMove`; it is never trusted. -/
inductive Cert.Rejection (M : Type) where
  /-- A `goal` leaf at a state that is not in the target. -/
  | notInTarget
  /-- A `move` node with no budget left. -/
  | noBudget
  /-- A `move` node at a state where the attacker is not to move. -/
  | notAttackerTurn
  /-- A `move` node whose move `m` is not available. -/
  | unavailable (m : M)
  /-- A `replies` node at a state where the defender is not to move. -/
  | notDefenderTurn
  /-- A `replies` node at a state where the defender has no available move. -/
  | noDefenderMove
  /-- A `replies` node with no pair for the available move `m`. -/
  | missingReply (m : M)
  /-- An only-move certificate with no refutation of the available move `m`, which is not the best
  move. -/
  | unrefuted (m : M)
  deriving Repr, DecidableEq

namespace Game

mutual

/-- Finds where certificate `c` for the claim `G.Forces a T n x` fails: `none` if `checkForces`
accepts it (`firstFailure_eq_none_iff`), and otherwise `some (ms, r)`, where `ms` is the path of
moves from `x` to the first node that fails and `r` is the first condition of `checkForces` that
fails there. Conditions are tested in the order `checkForces` states them, and the pairs of a reply
list in their order. An untrusted diagnostic, for reading a rejected certificate. -/
def firstFailure (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → Cert G.Move → Option (List G.Move × Cert.Rejection G.Move)
  | _, x, .goal => if T x then none else some ([], .notInTarget)
  | 0, _, .move _ _ => some ([], .noBudget)
  | k + 1, x, .move m next =>
      if G.turn x ≠ a then some ([], .notAttackerTurn)
      else if m ∉ G.moves x then some ([], .unavailable m)
      else match G.firstFailure a T k (G.play x m) next with
        | some (ms, r) => some (m :: ms, r)
        | none => none
  | n, x, .replies rs =>
      if G.turn x ≠ a.other then some ([], .notDefenderTurn)
      else if G.moves x = [] then some ([], .noDefenderMove)
      else match (G.moves x).find? (fun m => m ∉ rs.map Prod.fst) with
        | some m => some ([], .missingReply m)
        | none => G.firstFailureReplies a T n x rs

/-- Finds the first pair `(m, c)` of `rs` whose certificate `c` fails with budget `n` in the state
after `m` is played at `x`: `none` if every pair checks, and otherwise the path from `x`, starting
with `m`, to the first node that fails, and the condition that fails there. -/
def firstFailureReplies (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → List (G.Move × Cert G.Move) → Option (List G.Move × Cert.Rejection G.Move)
  | _, _, [] => none
  | n, x, (m, c) :: rs =>
      match G.firstFailure a T n (G.play x m) c with
      | some (ms, r) => some (m :: ms, r)
      | none => G.firstFailureReplies a T n x rs

end

/-- Finds where certificate `c` for the claim `G.WinsIn a n x` fails, as `firstFailure` does for
the target of `checkWin`. -/
def firstFailureWin (G : Game) (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) :
    Option (List G.Move × Cert.Rejection G.Move) :=
  G.firstFailure a (G.DefenderMated a) n x c

/-- Finds where `checkOnlyMove n x best oc` fails: `none` if it accepts
(`firstFailureOnlyMove_eq_none_iff`), and otherwise the path of moves from `x` to the first node
that fails and the condition that fails there. It tests, in this order, the win certificate
`.move best oc.next`, that every other available move has a refutation, and the refutations of
`oc.refs` in their order; the path to a node of a refutation starts with the refuted move. An
untrusted diagnostic, for reading a rejected certificate. -/
def firstFailureOnlyMove (G : Game) (n : Nat) (x : G.State) (best : G.Move)
    (oc : OnlyMoveCert G.Move) : Option (List G.Move × Cert.Rejection G.Move) :=
  match G.firstFailureWin (G.turn x) n x (.move best oc.next) with
  | some f => some f
  | none =>
    match (G.moves x).find? (fun m => m ≠ best ∧ m ∉ oc.refs.map Prod.fst) with
    | some m => some ([], .unrefuted m)
    | none =>
      G.firstFailureReplies (G.turn x).other (G.DefenderMated (G.turn x).other) oc.refBudget x
        oc.refs

section Diagnostics

variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat}
  {x : G.State} {best : G.Move} {oc : OnlyMoveCert G.Move}

mutual

/-- The diagnostic finds no failure exactly when the checker accepts. -/
theorem firstFailure_eq_none_iff : ∀ {n : Nat} {x : G.State} (c : Cert G.Move),
    G.firstFailure a T n x c = none ↔ G.checkForces a T n x c = true
  | _, x, .goal => by by_cases h : T x <;> simp [firstFailure, checkForces, h]
  | 0, _, .move _ _ => by simp [firstFailure, checkForces]
  | k + 1, x, .move m next => by
    by_cases ht : G.turn x = a
    · by_cases hm : m ∈ G.moves x
      · simp [firstFailure, checkForces, ht, hm]
        rw [← firstFailure_eq_none_iff next]
        cases G.firstFailure a T k (G.play x m) next <;> simp
      · simp [firstFailure, checkForces, ht, hm]
    · simp [firstFailure, checkForces, ht]
  | n, x, .replies rs => by
    by_cases ht : G.turn x = a.other
    · by_cases hne : G.moves x = []
      · simp [firstFailure, checkForces, ht, hne]
      · rw [firstFailure.eq_4, if_neg (not_not_intro ht), if_neg hne, checkForces.eq_4]
        cases hf : (G.moves x).find? (fun m => m ∉ rs.map Prod.fst) with
        | some m =>
          have hm := List.mem_of_find?_eq_some hf
          have hmiss : m ∉ rs.map Prod.fst := by simpa using List.find?_some hf
          simp only [reduceCtorEq, false_iff, Bool.and_eq_true, decide_eq_true_eq]
          exact fun ⟨⟨_, hcov⟩, _⟩ => hmiss (hcov m hm)
        | none =>
          have hcov : ∀ m ∈ G.moves x, m ∈ rs.map Prod.fst := by
            simpa using List.find?_eq_none.1 hf
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact (firstFailureReplies_eq_none_iff rs).trans
            ⟨fun h => ⟨⟨⟨ht, hne⟩, hcov⟩, h⟩, And.right⟩
    · simp [firstFailure, checkForces, ht]

/-- The diagnostic finds no failing pair exactly when every pair of the reply list checks. -/
theorem firstFailureReplies_eq_none_iff : ∀ {n : Nat} {x : G.State}
    (rs : List (G.Move × Cert G.Move)),
    G.firstFailureReplies a T n x rs = none ↔ G.checkReplies a T n x rs = true
  | _, _, [] => by simp [firstFailureReplies, checkReplies]
  | n, x, (m, c) :: rs => by
    rw [firstFailureReplies.eq_2, checkReplies.eq_2]
    cases hc : G.firstFailure a T n (G.play x m) c with
    | some f =>
      obtain ⟨ms, r⟩ := f
      have h : G.checkForces a T n (G.play x m) c ≠ true := fun h => by
        simp [(firstFailure_eq_none_iff c).2 h] at hc
      simp [h]
    | none =>
      simp [(firstFailure_eq_none_iff c).1 hc, firstFailureReplies_eq_none_iff rs]

end

/-- The diagnostic of the only-move checker finds no failure exactly when that checker accepts. -/
theorem firstFailureOnlyMove_eq_none_iff :
    G.firstFailureOnlyMove n x best oc = none ↔ G.checkOnlyMove n x best oc = true := by
  unfold firstFailureOnlyMove firstFailureWin checkOnlyMove
  simp only [checkWin, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  cases hw : G.firstFailure (G.turn x) (G.DefenderMated (G.turn x)) n x (.move best oc.next) with
  | some f =>
    have h : G.checkForces (G.turn x) (G.DefenderMated (G.turn x)) n x (.move best oc.next) ≠
        true := fun h => by simp [(firstFailure_eq_none_iff _).2 h] at hw
    simp [h]
  | none =>
    have hw' := (firstFailure_eq_none_iff _).1 hw
    cases hf : (G.moves x).find? (fun m => m ≠ best ∧ m ∉ oc.refs.map Prod.fst) with
    | some m =>
      have hm := List.mem_of_find?_eq_some hf
      obtain ⟨hdiff, hmiss⟩ : m ≠ best ∧ m ∉ oc.refs.map Prod.fst := by
        simpa using List.find?_some hf
      simp only [reduceCtorEq, false_iff]
      exact fun ⟨⟨_, hcov⟩, _⟩ => hmiss (hcov m hm hdiff)
    | none =>
      have hcov : ∀ m ∈ G.moves x, m ≠ best → m ∈ oc.refs.map Prod.fst := by
        simpa using List.find?_eq_none.1 hf
      simp only [firstFailureReplies_eq_none_iff, checkReplies_eq_true_iff]
      exact ⟨fun h => ⟨⟨hw', hcov⟩, h⟩, And.right⟩

end Diagnostics

end Game

end Chess
