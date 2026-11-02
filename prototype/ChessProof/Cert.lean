import ChessProof.Basic

/-!
# Forced wins, certificates, and a verified checker

`WinsIn a n p`: side `a` can force checkmate from `p` using at most `n` of its own moves,
whatever the opponent does. This is the specification; it mentions only `legal`, `play`,
and `mated` from the model.

A `Cert` is a strategy tree an untrusted search (Stockfish + a script) emits. `check` is a
Boolean function the kernel can run; `check_sound` says that a passing certificate proves the
specification. The kernel never trusts the engine, only the evaluation of `check`.
-/
namespace ChessProof

inductive WinsIn (a : Side) : Nat → Pos → Prop where
  /-- The defender is to move and is checkmated. -/
  | mate {n p} : p.turn = a.other → mated p = true → WinsIn a n p
  /-- The attacker picks one legal move. -/
  | att {n p} (m : Move) : p.turn = a → m ∈ legal p → WinsIn a n (play p m) → WinsIn a (n + 1) p
  /-- The defender has legal moves (so not stalemate) and every one of them still loses. -/
  | dfd {n p} : p.turn = a.other → legal p ≠ [] →
      (∀ m ∈ legal p, WinsIn a n (play p m)) → WinsIn a n p

/-- A side has a forced win at all. -/
def Wins (a : Side) (p : Pos) : Prop := ∃ n, WinsIn a n p

inductive Cert where
  | mate
  | att (m : Move) (k : Cert)
  | dfd (replies : List (Move × Cert))
deriving Inhabited

def lookup (m : Move) : List (Move × Cert) → Option Cert
  | [] => none
  | (m', c) :: rs => if m = m' then some c else lookup m rs

def memB (m : Move) : List Move → Bool
  | [] => false
  | m' :: ms => decide (m = m') || memB m ms

theorem memB_sound {m : Move} : ∀ {l : List Move}, memB m l = true → m ∈ l
  | [], h => by simp [memB] at h
  | m' :: ms, h => by
    simp only [memB, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memB_sound h)

/-- `fuel` bounds recursion (so `check` is structural and kernel-reducible); `n` is the
attacker's move budget. -/
def check : Nat → Side → Nat → Pos → Cert → Bool
  | 0, _, _, _, _ => false
  | _ + 1, a, _, p, .mate => decide (p.turn = a.other) && mated p
  | f + 1, a, n, p, .att m k =>
    decide (p.turn = a) && decide (0 < n) && memB m (legal p) && check f a (n - 1) (play p m) k
  | f + 1, a, n, p, .dfd rs =>
    decide (p.turn = a.other) && !(legal p).isEmpty &&
      (legal p).all fun m => match lookup m rs with
        | some k => check f a n (play p m) k
        | none => false

theorem check_sound : ∀ (f : Nat) (a : Side) (n : Nat) (p : Pos) (c : Cert),
    check f a n p c = true → WinsIn a n p := by
  intro f
  induction f with
  | zero => intro a n p c h; simp [check] at h
  | succ f ih =>
    intro a n p c h
    cases c with
    | mate =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .mate h.1 h.2
    | att m k =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨ht, hn⟩, hm⟩, hk⟩ := h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact .att m ht (memB_sound hm) (ih a n' _ k (by simpa using hk))
    | dfd rs =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, List.all_eq_true] at h
      obtain ⟨⟨ht, hne⟩, hall⟩ := h
      refine .dfd ht hne fun m hm => ?_
      have := hall m hm
      split at this
      · exact ih a n _ _ this
      · simp at this

theorem mated_legal_nil {p : Pos} (h : mated p = true) : legal p = [] := by
  simp only [mated, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.2

/-- **Consistency of the semantics.** No position is a forced win for both sides. This is
what turns "this move wins" into "this move is optimal": once one side's win is proved, every
alternative that hands the opponent a forced win is strictly worse. -/
theorem not_both {a : Side} {n k : Nat} {p : Pos} (h1 : WinsIn a n p) (h2 : WinsIn a.other k p) :
    False := by
  induction h1 generalizing k with
  | mate ht hm =>
    cases h2 with
    | mate ht' _ => simp_all
    | att m _ hm' _ => simp [mated_legal_nil hm] at hm'
    | dfd ht' _ _ => simp_all
  | att m ht hm _ ih =>
    cases h2 with
    | mate _ hm' => simp [mated_legal_nil hm'] at hm
    | att _ ht' _ _ => simp_all
    | dfd _ _ hall => exact ih (hall m hm)
  | dfd ht _ _ ih =>
    cases h2 with
    | mate ht' _ => simp_all
    | att m _ hm h => exact ih m hm h
    | dfd ht' _ _ => simp_all

/-- Checks that `best` is legal and wins for the side to move, and that every *other* legal
move hands the opponent a forced win (certificates looked up in `refutations`). -/
def onlyMove (fuel n : Nat) (p : Pos) (best : Move) (cBest : Cert)
    (refutations : List (Move × Cert)) : Bool :=
  memB best (legal p) && check fuel p.turn n (play p best) cBest &&
    (legal p).all fun m => decide (m = best) || match lookup m refutations with
      | some c => check fuel p.turn.other fuel (play p m) c
      | none => false

/-- If `onlyMove` passes, then after any legal move `m`, the mover keeps a forced win
**iff** `m = best`. -/
theorem onlyMove_sound {fuel n : Nat} {p : Pos} {best : Move} {cBest : Cert}
    {rs : List (Move × Cert)} (h : onlyMove fuel n p best cBest rs = true) :
    best ∈ legal p ∧ WinsIn p.turn n (play p best) ∧
    ∀ m ∈ legal p, (Wins p.turn (play p m) ↔ m = best) := by
  simp only [onlyMove, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hmem, hbest⟩, hall⟩ := h
  have hwin := check_sound _ _ _ _ _ hbest
  refine ⟨memB_sound hmem, hwin, fun m hm => ⟨fun ⟨k, hk⟩ => ?_, fun he => he ▸ ⟨n, hwin⟩⟩⟩
  rcases hall m hm with he | hr
  · exact he
  · split at hr
    · exact (not_both hk (check_sound _ _ _ _ _ hr)).elim
    · simp at hr

end ChessProof

/-! ## Glue lemmas for per-node (flattened) kernel proofs -/
namespace ChessProof

theorem of_play_eq {a : Side} {n : Nat} {p q : Pos} {m : Move} (h : play p m = q)
    (w : WinsIn a n q) : WinsIn a n (play p m) := h ▸ w

theorem all_nil {a : Side} {n : Nat} {p : Pos} : ∀ x ∈ ([] : List Move), WinsIn a n (play p x) :=
  fun _ h => nomatch h

theorem all_cons {a : Side} {n : Nat} {p : Pos} {m : Move} {l : List Move}
    (h : WinsIn a n (play p m)) (t : ∀ x ∈ l, WinsIn a n (play p x)) :
    ∀ x ∈ m :: l, WinsIn a n (play p x) :=
  List.forall_mem_cons.2 ⟨h, t⟩

theorem iff_best {a : Side} {n : Nat} {p : Pos} {b : Move} (w : WinsIn a n (play p b)) :
    (Wins a (play p b) ↔ b = b) := ⟨fun _ => rfl, fun _ => ⟨n, w⟩⟩

theorem iff_refuted {a : Side} {k : Nat} {p : Pos} {m b : Move}
    (r : WinsIn a.other k (play p m)) (hne : m ≠ b) : (Wins a (play p m) ↔ m = b) :=
  ⟨fun ⟨_, h⟩ => (not_both h r).elim, fun h => (hne h).elim⟩

theorem iff_cons {a : Side} {p : Pos} {b m : Move} {l : List Move}
    (h : Wins a (play p m) ↔ m = b) (t : ∀ x ∈ l, (Wins a (play p x) ↔ x = b)) :
    ∀ x ∈ m :: l, (Wins a (play p x) ↔ x = b) :=
  List.forall_mem_cons.2 ⟨h, t⟩

theorem iff_nil {a : Side} {p : Pos} {b : Move} :
    ∀ x ∈ ([] : List Move), (Wins a (play p x) ↔ x = b) := fun _ h => nomatch h

end ChessProof
