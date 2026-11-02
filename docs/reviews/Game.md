# File-level design review: `Chess.Game`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/Game.lean` (whole file), `docs/spec/Game.md` (whole file), `docs/process/Game.md`
(Rounds 1–4), `Chess/Basic.lean` (the `Color` section), `Chess/Rules.lean` (`InCheck`,
`Checkmate`, `play`, `play_turn`) and `Chess/MoveGen.lean` (`legalMoves` and its lemmas),
`docs/reviews/MoveGen.md` and `docs/reviews/Rules.md`, `docs/DESIGN.md` (§3, §6, §7, §8, §11) and
`docs/THEOREMS.md` (G7, C4–C7).

State at review time: `lake build` green, no warnings, no `sorry`, no `native_decide`. 748 lines:
about 140 trusted (the section "Games"), 250 of laws, 90 of search, 270 of certificates and glue,
90 of toy games and tests. 77 of the 78 Lean docstrings occur word for word in the spec (checked by
script, whitespace-insensitive, trailing "THEOREMS …" tags stripped); the exception is T11's
docstring, whose text the spec does not give (see C9).

Experiments behind the findings were run in scratch files outside the library, importing the built
`Chess.Game` or `Chess`. Timings are wall-clock `lake env lean` on this machine, minus the
0.4 s cost of an empty file.

## Changes made in this review

- **One line rewrapped** (`Chess/Game.lean`, the comment above `mutual`): it was 101 characters,
  the only line in the library over 100. Words unchanged; build green.

Nothing else in the Lean, the spec or the process log was touched. Every larger point below is a
recommendation; the Appendix gives the checked Lean for the ones that are proofs.

---

## 1. Verdict

**The right abstraction, faithfully translated. Build on it.** The semantics is small, the proofs
are short, and every executable part has its soundness theorem. I found no semantic error. The
concerns are about what later modules and the certificate pipeline will pay for, and about two
decisions that get expensive once generated files exist.

What is right and should not change:

- **`Forces` as the primitive, with three rules and the "has a move" guard.** Winning is one
  target; monotonicity, search, certificates, soundness and completeness are proved once for every
  decidable target. The guard makes stalemate a non-loss for both sides by construction
  (`not_wins_of_stalemate` needs no turn hypothesis), and it is exactly what the trap duality (G9)
  needs: with `forces_common_budget` already proved, G9's hard direction is a few lines.
- **Budgets count attacker moves, the goal holds at any budget, and every budget is counted at the
  state of the claim.** This matches Stockfish's "mate in n" and problem stipulations directly, so
  no headline ever subtracts one. `checkOnlyMove` follows it (`n = 11` for Gotham).
- **`attackerForces` takes no colour, and `defenderStep` names the defender rule once.** The search
  is structural on the budget, and the proof is one lemma per rule. This is the cleanest bounded
  minimax correctness proof I have seen in Lean; the prototype's mutual induction is gone.
- **Every Boolean conjunct of a checker is `decide` of its proposition.** Soundness is one
  `simp only` per node, and no Boolean helper or its lemma exists.
- **The trusted definitions read `moves` only through membership and emptiness.** This is what
  makes the bitboard refinement cheap; I checked it (C4).
- **`OnlyWinningMove.of_refuted` as the root of only-move proofs.** It is also the right interface
  for transferring only-move claims between games (C4).
- **`Cert` is generic in the move type and carries no budgets and no states.**

---

## 2. Concerns, in priority order

### C1 (medium-high, for the `ChessGame` spec). The instance-implicit fields fill themselves silently

`decMated` and `decEqMove` are instance-implicit fields, so `Game.chess` is built without naming
them and Lean takes whatever instance search finds. Today that is harmless: with DESIGN §6.4's
`Mated p := InCheck p ∧ legalMoves p = []`, search finds `InCheck.decidable` and list equality with
`[]`, which the kernel evaluates lazily (it needs only the first legal move). But MoveGen review C1
proposes proving `checkmate_iff` now, and the natural next step is `Mated := Checkmate`, the FIDE
predicate, which reads better in the trusted base. Then search silently picks Rules'
`Checkmate.decidable`, measured at more than 500 s in the kernel (Rules review C3), and every `goal`
leaf of every certificate, which decides `Mated`, becomes unusable. Nothing would fail to build;
only the kernel checks would time out.

Recommendations for the `ChessGame` spec:

1. Pass `decMated` explicitly in `Game.chess`, whichever definition of `Mated` is chosen. With
   `Mated := Checkmate`, use `decMated := fun p => decidable_of_iff _ checkmate_iff.symm`, the
   cheap instance of MoveGen review C1.
2. Make `Game.chess` an `abbrev` (or `@[reducible] def`). The toy games had to be `abbrev`s for
   numerals to elaborate as moves (spec D5.1, checked); the same reducibility keeps
   `Game.chess.Move` and `Game.chess.State` interchangeable with `Chess.Move` and `Chess.Position`
   for instance search and dot notation in headline statements.

Nothing in `Game` needs to change. A sentence in the `decMated` field docstring ("an instance should
supply a decision procedure the kernel can afford") would document the trap at its source, but that
is a spec edit, so it is left to the refiner.

### C2 (medium, do now while only `Chess.lean` imports it). Split the file at the trust boundary

DESIGN §11 merged `Game` and `Certificate` with an explicit trigger: "If the file exceeds about 600
lines, certificates split off as `Chess.Game.Certificate`." The file is 748 lines. More important
than size: the module docstring says only the section "Games" is trusted, and a reader auditing
the trusted base currently has to know where in a 750-line file to stop reading. Suggested layout,
with no change to any declaration or name:

| File | Contents | Trusted |
|---|---|---|
| `Chess/Game/Defs.lean` | `Game`, the instance attribute, `DefenderMated`, `Forces`, `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove` (about 140 lines) | yes |
| `Chess/Game/Laws.lean` | section Laws | no |
| `Chess/Game/Search.lean` | section Search, the two decidability instances | no |
| `Chess/Game/Cert.lean` | `Cert`, the checkers, their soundness and completeness, `PerNode` | no |
| `Chess/Game.lean` | imports the four, keeps the module docstring | – |
| `Chess/Game/Examples.lean` (or the test library of MoveGen review C4) | `Toy` and T1–T14 | no |

The cost is a spec edit to "Contents of the file" and `namespace` bookkeeping (the two
`namespace Game` blocks around `Cert` become two files). Nothing imports `Chess.Game` except
`Chess.lean` today, so this is the cheapest moment. After `ChessGame`, `scripts/` and the generated
certificate files import it, every split also moves import lines in generated code.

### C3 (medium, before `scripts/` emits its first file). Freeze the generated-file interface, and add a diagnostic

Generated certificate files will be the largest Lean in the project, and they are regenerated
rather than edited. Whatever names and argument orders they use become expensive to change.

1. **Generators should emit only checker calls and the glue lemmas** (`checkWin`, `checkOnlyMove`,
   `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`, `Forces.of_play_eq`,
   `OnlyWinningMove.of_refuted`), never the `Forces` constructors directly. Then the constructors'
   argument order (explicit `m`, then the hypotheses) stays free to change, and the glue lemmas are
   the stable API. Worth one sentence in the `scripts/` README and in spec §4.1.
2. **Settle the names now.** `Chess.Cert` will have siblings (survival certificates C4, traps C5,
   ranked sets C6). If it is to be renamed (`Strategy`, `ForceCert`), it is free today and
   expensive later. I would keep `Cert`, but decide it explicitly.
3. **`checkOnlyMove n k x best next refs`** has six positional arguments, two of them adjacent
   budgets. A swap of `n` and `k` is not a soundness risk (the theorem states `n`), but it makes a
   generated call hard to read. A structure
   `OnlyMoveCert M := (best : M) (win : Cert M) (refBudget : Nat) (refs : List (M × Cert M))`
   would make generated files self-describing. It is also where spec open item 1 (Stage 3 trap
   refutations) can grow a field without breaking old files. Optional; decide before the Gotham
   port.
4. **Add an untrusted diagnostic.** When a 300-node certificate fails, `checkWin … = false` says
   nothing about where. A `#eval`-only function
   `firstFailure : … → Cert G.Move → Option (List G.Move)` returning the path of moves to the first
   rejecting node (and which conjunct failed) needs no proof and turns a failing certificate into a
   one-line bug report. It belongs beside the checkers or in `scripts/`; it is not trusted and needs
   no soundness theorem.

### C4 (medium, for THEOREMS G7). Morphisms work with this interface; state them by membership

The bitboard layer (DESIGN §3.3) depends on G7. I checked that `Game` supports it as it stands. In
a scratch file, with a morphism stated by **membership** instead of THEOREMS G7's `moves_perm`:

```lean
mem_moves : ∀ x m', m' ∈ H.moves (state x) ↔ ∃ m ∈ G.moves x, move m = m'
play_state : ∀ x m, m ∈ G.moves x → state (G.play x m) = H.play (state x) (move m)
```

both directions of the transfer of `Forces` go through by one induction each, 12 and 15 lines
(Appendix A), and `WinsIn` follows from the turn and `mated_iff` fields. Consequences:

- THEOREMS G7 should replace `moves_perm` by `mem_moves`, as spec choice 16 already says. A
  bitboard generator then may order and even repeat its moves freely.
- The backward direction needs `recolor` to be injective. For `Color → Color` that follows from
  `recolor_other`, but the proof is a fiddly case split; a field or lemma `recolor_injective`
  is worth stating once.
- **`OnlyWinningMove` transfers without assuming the move map is injective.** Forward transfer of
  the best move's win, backward transfer of every alternative's "does not win", and `of_refuted`
  style reasoning on the target side suffice: an alternative in `H` other than the image of `best`
  is the image of an alternative in `G` other than `best`. So the fast layer's checker can certify
  only-move claims about the specification game. This is the main payoff of the value-based
  `OnlyWinningMove` combined with membership-based laws, and it should be recorded in G7.

### C5 (low-medium, cheap). Two lemmas later stages will want

Both checked (Appendix B), each under 10 lines:

- **`Forces.imp (w : G.Forces a T n x) (h : ∀ y, T y → U y) : G.Forces a U n x`**: forcing is
  monotone in the target. G7 (pulling back targets), C5's "trap relative to `Safe`", and G12's
  clock headroom arguments all reach for it. Its absence will be felt the first time someone states
  a target as a conjunction.
- **`MateIn.exists_move (ht : G.turn x = a) (h : G.MateIn a (n + 1) x) :
  ∃ m ∈ G.moves x, G.MateIn a n (G.play x m)`**: exact distance drops by exactly one along a
  fastest move. This is the step of O3 (fastest mate) and of every "this move is optimal"
  approximation that measures distance to mate, which is the owner's stated direction. With it,
  "move `m` keeps a mate in `n`" and "every other move allows the defender to delay" are both
  one-step statements.

Since the spec is word-for-word with the Lean, these go through the spec first (as L2.26, L2.27).

### C6 (low). Spec open item 2 is probably moot: the kernel shares repeated move lists

Open item 2 worries that the `replies` case of `checkForces` (and `defenderStep`) names
`G.moves x` twice and may make the kernel generate it twice. Measured on chess:
`decide +kernel` of `(legalMoves Position.initial).length = 20` takes 3.2 s; the conjunction of
that with `(legalMoves Position.initial).isEmpty = false` also takes 3.2 s. The kernel caches the
reduction of the identical closed term. Inside the checker the two occurrences are the same term
after substitution, so the same cache applies. I recommend closing the item, or at most re-measuring
once on a real defender node, rather than restructuring the checker into a `match`.

For scale: on the take-away toy, `checkWin` with a certificate of about 16 000 nodes takes 13 s in
the kernel, under 1 ms a node, against about 3 s a node for chess move generation. The recursion
scheme of the checker is not where chess certificates will spend their time; move generation is
(MoveGen review C2, and the `isLegal` question of spec choice 13).

### C7 (low, a known limit). Strategy trees duplicate transpositions

`Cert` is a tree, so a strategy that reaches the same position by two move orders carries two
copies of the subtree, and the monolithic checker checks both. Forced mates in chess transpose
often (the toy experiment above is a case: the two defender replies lead to the same state, and
the kernel cannot see it because the two state terms differ syntactically). The per-node route
(spec §4.1) already shares, since a checkpoint theorem is named once and cited twice; the ranked
sets of C6 (Stage 5) share in the monolithic route. So nothing changes now, but the `scripts/`
generator should deduplicate checkpoints by position, not by path.

### C8 (low). `OnlyWinningMove` is a claim about G∞

`Wins` has no move-count rule, so an alternative that wins only beyond the fifty-move horizon makes
`OnlyWinningMove` false in G∞ even when it is a draw under FIDE. The direction is safe: the
certificates prove that alternatives *lose*, which survives any clocked game with enough headroom
(G12). The module docstring says that `Wins` ignores the fifty-move rule; headline docstrings in
`ChessGame` should repeat "in the game without move-count rules" next to any "only winning move"
claim, since that is where a chess reader will look.

### C9 (cosmetic)

- The module docstring's "Main statements" omits `Forces.trans` (O8), `OnlyWinningMove.of_refuted`
  and `OnlyWinningMove.winsIn_play`, the three lemmas later stages use most. A spec edit first.
- T11's docstring is not given in the spec (which only says T11 has one). Add its text to the spec
  table so the word-for-word check covers it.
- `Toy.takeAway_onlyWinningMove` is a named theorem in the library namespace
  `Chess.Game.Toy`. Harmless; it moves with the tests under C2.

---

## 3. Fit with the other modules

- **`Basic`.** `Game` uses only `Color`, `other` and three lemmas. `turn_ne_both` could move to
  `Basic` as a `Color` lemma (`c' = c → c' = c.other → False`), but it reads better here, phrased
  about turns.
- **`Rules` / `MoveGen` to `ChessGame`.** Both laws are immediate: `turn_play` from `play_turn`
  (unconditional, stronger than needed) and `moves_eq_nil_of_mated` from the definition of `Mated`.
  The per-node glue takes `m ∈ G.moves x` from any source, so `mem_legalMoves` (MoveGen review C1)
  plugs in without a `Game` change. See C1 for the instance trap.
- **Bitboards.** Supported as is (C4). The fast game can use the same `Chess.Move` type, which makes
  the move map the identity and `mem_moves` a plain `↔` between move lists.
- **Stage 3 (traps, `Holds`, game value).** Supported: the guard and `forces_common_budget` give
  G9's duality; `wins_attacker_iff` and `wins_defender_iff` are G10's negamax equations. The only
  open design question is spec open item 1 (how `checkOnlyMove` grows trap refutations), which C3.3
  makes painless either way.
- **Clocked games (G12).** A state pairing a position with a clock, with no moves once the clock
  runs out, is an ordinary `Game`: such a state is neither mated nor lost, exactly the intended
  draw. No field is missing.

---

## Appendix A. Morphisms by membership (checked, scratch file)

```lean
structure Hom (G H : Game) where
  state : G.State → H.State
  move : G.Move → H.Move
  recolor : Color → Color
  recolor_other : ∀ c, recolor c.other = (recolor c).other
  recolor_inj : ∀ c c', recolor c = recolor c' → c = c'   -- used only backwards
  turn_state : ∀ x, H.turn (state x) = recolor (G.turn x)
  mated_iff : ∀ x, H.Mated (state x) ↔ G.Mated x
  mem_moves : ∀ x m', m' ∈ H.moves (state x) ↔ ∃ m ∈ G.moves x, move m = m'
  play_state : ∀ x m, m ∈ G.moves x → state (G.play x m) = H.play (state x) (move m)

theorem Hom.forces (f : Hom G H) {T' : H.State → Prop} (hT : ∀ y, T y → T' (f.state y))
    (w : G.Forces a T n x) : H.Forces (f.recolor a) T' n (f.state x) := by
  induction w with
  | goal h => exact .goal (hT _ h)
  | move m ht hm _ ih =>
    refine .move (f.move m) (by rw [f.turn_state, ht]) ((f.mem_moves _ _).2 ⟨m, hm, rfl⟩) ?_
    rw [← f.play_state _ _ hm]; exact ih
  | @replies n x ht hne _ ih =>
    refine .replies (by rw [f.turn_state, ht, f.recolor_other]) ?_ ?_
    · obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
      exact List.ne_nil_of_mem ((f.mem_moves _ _).2 ⟨m, hm, rfl⟩)
    · intro m' hm'
      obtain ⟨m, hm, rfl⟩ := (f.mem_moves _ _).1 hm'
      rw [← f.play_state _ _ hm]; exact ih m hm

theorem Hom.forces_back (f : Hom G H) {T : G.State → Prop} {T' : H.State → Prop}
    (hT : ∀ x, T' (f.state x) → T x) {y : H.State} (w : H.Forces (f.recolor a) T' n y) :
    ∀ x, f.state x = y → G.Forces a T n x := by
  induction w with
  | goal h => intro x hx; subst hx; exact .goal (hT _ h)
  | @move n y m ht hm _ ih =>
    intro x hx; subst hx
    obtain ⟨m₀, hm₀, rfl⟩ := (f.mem_moves _ _).1 hm
    exact .move m₀ (f.recolor_inj _ _ (by rw [← f.turn_state, ht])) hm₀
      (ih _ (f.play_state _ _ hm₀))
  | @replies n y ht hne _ ih =>
    intro x hx; subst hx
    refine .replies (f.recolor_inj _ _ (by rw [← f.turn_state, ht, f.recolor_other])) ?_ ?_
    · obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨m₀, hm₀, -⟩ := (f.mem_moves _ _).1 hm'
      exact List.ne_nil_of_mem hm₀
    · intro m₀ hm₀
      exact ih _ ((f.mem_moves _ _).2 ⟨m₀, hm₀, rfl⟩) _ (f.play_state _ _ hm₀)

theorem Hom.winsIn (f : Hom G H) (w : G.WinsIn a n x) : H.WinsIn (f.recolor a) n (f.state x) :=
  f.forces (fun y ⟨ht, hm⟩ => ⟨by rw [f.turn_state, ht, f.recolor_other], (f.mated_iff y).2 hm⟩) w
```

## Appendix B. The two lemmas of C5 (checked, scratch file)

```lean
theorem Forces.imp (w : G.Forces a T n x) (h : ∀ y, T y → U y) : G.Forces a U n x := by
  induction w with
  | goal hT => exact .goal (h _ hT)
  | move m ht hm _ ih => exact .move m ht hm ih
  | replies ht hne _ ih => exact .replies ht hne ih

theorem MateIn.exists_move (ht : G.turn x = a) (h : G.MateIn a (n + 1) x) :
    ∃ m ∈ G.moves x, G.MateIn a n (G.play x m) := by
  rcases (forces_attacker_succ_iff ht).1 h.1 with h0 | ⟨m, hm, w⟩
  · exact (turn_ne_both ht h0.1).elim
  · exact ⟨m, hm, w, fun k hk wk => h.2 (k + 1) (by omega) (.move m ht hm wk)⟩
```
