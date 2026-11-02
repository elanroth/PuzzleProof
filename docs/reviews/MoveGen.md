# File-level design review: `Chess.MoveGen`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/MoveGen.lean` (whole file), `docs/spec/MoveGen.md` (whole file),
`docs/process/MoveGen.md` (Rounds 1–4), `Chess/Rules.lean` (§§ "Reaching and attacking",
"Shapes of moves", "Movement rules", `play`, `Legal`, terminal positions), `Chess/Position.lean`
and `Chess/Basic.lean` (declaration outlines and the lemmas used here), `docs/reviews/Rules.md`
and `docs/reviews/Position.md`, `docs/DESIGN.md` (§3, §5.7, §6.1, §6.4, §7, §8, §8.4) and
`docs/THEOREMS.md` (M4, M5, M10, G7, G16, and the `Forces` definition).

State at review time: `lake build` green; `lake env lean Chess/MoveGen.lean` prints no warnings
(about 30 s, nearly all of it tests); no `sorry`, no `native_decide`. 433 lines. All 35 Lean
docstrings occur word for word in the spec (checked with the script of Rules review C8). No line is
longer than 100 characters.

**No change was made to the Lean, the spec or the process log in this review.** Nothing in the file
is wrong, and the most valuable change (C1) is a new section of proofs. Under the process, that
section goes through the spec first. The proof is checked and given in the Appendix, ready to
paste. All experiments were run in scratch files outside the library.

---

## 1. Verdict

**The right design. Build on it, and close the trust gap now: it costs about 45 lines (C1).**

What is right and should not change:

- **Propose and dispose** (spec design choice 1). The generator proposes candidates by geometry.
  It keeps a candidate only if `PseudoLegal` allows it and the second conjunct of `Legal` holds,
  word for word. Soundness is a one-line theorem. Completeness reduces to a geometric cover with no
  check, pin or blocker reasoning. No second copy of any rule exists, so nothing can drift. This is
  the cleanest generator/specification split I know of for a chess formalization. The prototype's
  bug classes (en passant, castling, promotion re-encoded in the generator) cannot recur.
- **Target lists mirror `Reaches` arm for arm**, and M1 is one `↔` per list
  (`mem_slideTargets`, `mem_reachTargets`). `Board.upToBlocker` is a general list operation with a
  general lemma, so the ray walk is proved once.
- **Membership, not order, is the contract** (design choice 6). This keeps a later bitboard
  generator free to order its moves however it likes.
- **The king-on-home-square guard in `castleCandidates`.** It makes M5 true without `WellFormed`.
  This was found by checking, not by assuming.
- **`candidates_ignores_epTarget` by `rfl`.** It is a cheap tripwire for G16 and documents a real
  invariant.
- **`agreesWithLegal` with its two lemmas.** A Boolean test turned into a per-position theorem is
  the right pattern, and the next modules should copy it.
- **No `Board`-valued conditionals anywhere.** The file respects the convention that keeps the
  function board safe in compiled code (Position review C1).

---

## 2. Concerns, in priority order

### C1 (high, do now). Prove the cover; the generator then leaves the trusted base in Stage 1

Spec open item 1 asks whether to pull `Correct.lean` into Stage 1. **Yes, and it is smaller than
the spec estimates.** In a scratch file importing the built `Chess.MoveGen`, I proved the following
in 56 lines, with no warnings (Appendix):

- `PseudoLegal.mem_candidates` (L7.1, the cover): one six-way `rcases` and one short bullet per
  rule. The double-push case is `relRank_of_offset_forward` plus `omega`. The en passant case is
  `rw [hr5]; decide`.
- `mem_pseudoMoves` (L7.2, M2) and `mem_legalMoves` (L7.4, M4) are one line each, from L3.1/L3.4
  and the cover.
- `checkmate_iff : Checkmate p ↔ InCheck p ∧ legalMoves p = []` (L7.6, M6) is one `simp only`.

`#print axioms mem_legalMoves`: `propext`, `Classical.choice`, `Quot.sound`. Elaboration is well
under a second.

Consequences:

1. The "one trusted claim" of the module header, DESIGN §3's "trusted UNTIL STAGE 2" box and
   §7.3's last trusted item all disappear before `Game` and `ChessGame` are written. G8
   (`Game.chess` means FIDE chess) then becomes a Stage 1 corollary.
2. `Checkmate` gets its cheap decision now: `decidable_of_iff _ checkmate_iff.symm`. Rules review
   C3 measured Rules' own instance at more than 500 s in the kernel; this one costs about 3.4 s.
3. DESIGN §6.1's `isLegal` option is available at once with law `mem_legalMoves`, through
   `isLegal p m := decide (Legal p m)`, which is cheaper than the spec's `m ∈ candidates p ∧ …`
   variant. See C2 for what it saves.
4. `legalMovesBySpec`/`agreesWithLegal` stop testing anything that is not already a theorem except
   `Nodup` (M5). They can move to the test library (C4) without loss.

**Where to put it.** Design choice 8 says a promise should be proved in the file that makes it.
I recommend a section `Completeness` in `MoveGen.lean` itself, right after `section Generator`,
holding L7.1–L7.4, L7.6 and L7.7. The docstrings of `candidates`, `pseudoMoves` and `legalMoves`
then take the plain wording the spec already provides ("The pseudo-legal moves of `p`", "The legal
moves of `p`"). `Chess/MoveGen/Correct.lean` keeps M5 (`Nodup`, longer; see C3). The cover's
`rcases` encodes the conjunct order of all six rules. If Rules review C1 (structures) is adopted
later, that one pattern is the only line here that must change. This is not a reason to wait.

### C2 (high, before certificate work). Kernel cost per node: measured, and where the real fix lies

Spec open item 4 and design choice 10 frame this as Rules' instances versus a local Boolean. I
measured both directions in the kernel (`decide +kernel`, `profiler`, same session):

| Decision | Kernel |
|---|---|
| `candidates Position.initial` (56 moves) | 0.11 s |
| `Legal Position.initial e2e4` (one move) | 0.27 s |
| `pseudoMoves Position.initial` | 0.65 s |
| `legalMoves Position.initial` (as built) | 3.19 s |
| `legalMoves foolsMate = []` (as built) | 3.36 s |
| same, king safety by the super-piece method (`reachTargets` outward from each square holding the mover's king, `== some ⟨c, k⟩`) | 1.85 s / 1.54 s |
| same, with the king squares computed once by `let` and passed in | 3.09 s / 2.81 s (slower) |

Findings:

- **The super-piece filter gains only about 2×.** It agrees with `legalMoves` on the positions
  tried (`#guard`). Most of the remaining cost is representation: every read of `(p.play m).board`
  goes through a `setMany` closure, and every offset is `Int` arithmetic in the kernel. The
  prototype's nibble-packed `Nat` board, whose operations are GMP-accelerated in the kernel, ran
  about 0.25 s per node. Instance or algorithm tweaks on the function board will not close a
  10× gap.
- **`let` does not memoize in the kernel.** Precomputing the king squares was *slower*, because
  the kernel substitutes the `let` and re-evaluates it for each move. Kernel-evaluated code must
  receive precomputed facts as literal data (the checkpoint pattern of DESIGN §7.4), not through
  `let`. Worth one sentence in DESIGN §7.4.
- **Faster instances do not cascade.** Each composite instance in Rules (`Legal.decidable`,
  `PseudoLegal.decidable`, `InCheck.decidable`, `CanCastle.decidable`, …) is a term that names the
  leaf instances by constant when Rules is elaborated. A faster `Slides` or `Attacked` instance
  declared after Rules (even in a module between Rules and MoveGen) therefore changes neither
  `legalMoves` nor any of Rules' composite instances. There are only two ways to get a speed-up:
  replace the *body* of the leaf instance inside Rules, in place, or re-declare the whole chain
  above it. The spec's design choice 10 is correct but understates this. It concerns Rules'
  instances, not only this module.

Recommended order:

1. **Attacker nodes:** use `isLegal := decide (Legal p m)` (0.27 s against 3.2 s; available once
   C1 lands).
2. **Defender nodes:** use a local Boolean `kingSafeAfter` with an `_iff` lemma, as in design
   choice 10's second option, for about 2×. It touches neither Rules' text nor its instances.
3. **Plan for the fast layer in the kernel earlier than Stage 5** if C-tier certificates of
   prototype size (about 320 nodes; roughly 9 minutes at today's defender cost) are a Stage 1–2
   goal. The fast layer is bitboards over `Nat`/`BitVec 64`, which the kernel accelerates, with a
   game morphism.

Decide this before `Game`'s certificate checker is benchmarked, so that its interface (an
`isLegal` field or not) is fixed once.

### C3 (medium-high, before G7/M10/M9). M5 (`Nodup`) is on a critical path only because G7 asks for `Perm`

THEOREMS G7 has `moves_perm : ((G.moves x).map move).Perm (H.moves (state x))`, and M10 has
`Fast.legalMoves_perm`. A `Perm` needs `Nodup` on both sides plus a helper that core lacks (spec
open item 8). That puts M5 (L1.4, L1.5, L2.3, L2.4: the longest proofs left in this module) and
an equivalent `Nodup` proof for the bitboard generator on the path to every morphism: colour flip,
refinement, normalization.

But `Forces`, `WinsIn`, `Mated` and the certificate coverage test read `moves` only through `∈`
and `= []` (THEOREMS `Forces.replies`, DESIGN §7.2). **Recommend stating G7 by membership:**
`m' ∈ H.moves (state x) ↔ ∃ m ∈ G.moves x, move m = m'`. That is enough for `winsIn_iff`, and it
takes M5 and the `Perm` helper off the critical path. M5 then serves only M8 (perft counts lines).
Raise this with whoever owns THEOREMS and `Game` before `Game.Hom` is written; changing it later
costs every morphism proof.

### C4 (medium). Test code and 30 s of tests are inside a library module

Spec open item 9 defers this until "the test library exists". It should be created now. About
29 of the module's 30 s are tests (nine `decide +kernel` examples, the `#guard`s). Every edit to
`Basic`, `Position` or `Rules` pays those 30 s again, and so will `ChessGame` and everything after
it. A second `lean_lib` (say `ChessTest`, with `Test/MoveGen.lean` and `Test/Rules.lean`) in
`lakefile.toml`, not in `defaultTargets` or built by a separate `lake build ChessTest`, takes about
ten lines. `legalMovesBySpec`, `agreesWithLegal`, L5.1–L5.3, `epCheckPos`, `promoKnightPos` and
every test move there. Keep one or two cheap `#guard`s here as smoke tests if wanted. After C1,
the agreement tests check only `Nodup`, so they lose most of their reason to sit in the library.

### C5 (medium). Text that becomes stale the day C1 lands, and text already stale elsewhere

When the cover is proved, these must change together (all are spec-synced, so the spec moves
first):

- the module header's last implementation note and "Main statements";
- the docstrings of `candidates` (second sentence), `pseudoMoves` and `legalMoves` (the spec gives
  the replacements in D2.6, D3.1 and D3.2's notes);
- `perft`'s docstring stays as it is until M5 (it correctly says "entries", not "legal lines").

Outside this module (flagged, not edited):

- DESIGN §5.7 still describes per-rule enumeration ("castling by checking `CastleMove` for each
  wing") and §8.4 says perft counts "sequences of `n` legal moves"; both predate propose-and-
  dispose (spec open item 5).
- DESIGN §6.1 says `isLegal` "needs M4, so it waits for Stage 2".
- DESIGN §8's table lists `mem_ray_iff` under `Correct.lean`; the M1 lemmas are
  `mem_slideTargets`/`mem_reachTargets` and already live here.
- THEOREMS M2's "Forces" and M7's position list (spec open item 6, still open after Round 4).

### C6 (low-medium). Sequence Rules review C1/C5 with the completeness proof

`MoveGen.lean` touches the rules' internals in only two places today: `CastleMove.eq_castle`'s
`obtain` and `h.1.colorAt_src` in L5.1. Coupling is low. The cover (C1) adds one six-way
positional pattern, and M5 would add more. If the owner intends to adopt Rules C1 (rules as
structures) or C5 (`StepMove` → `PieceMove`), decide before M5 is written. For the cover alone the
migration cost is a single `rcases` line, so C1 here should not wait.

### C7 (low). Compiled perft speed is unmeasured, and test-library depth targets depend on it

Interpreted, `legalMoves` costs about 24 ms per call (spec). `perft n` calls it once per node at
depths below `n`. Depth 4 from the initial position makes 9 323 calls (about 4 minutes
interpreted). Depth 5 makes about 206 000 (about 80 minutes). Before the test library promises
"depth 3 for all six positions and deeper where time allows", build one `lean_exe` and time
`perft 4` compiled. If the function board's compiled cost (Position review C1) shows up anywhere,
it is here.

### C8 (low). Fit with the bitboard layer: good, with one caution

Nothing here constrains Stage 5. The fast generator should be proved against `Legal` through
`mem_legalMoves`, not against this module's candidate structure. Its attack sets should refine
`Reaches`/`Board.attacked_iff` (Rules review C9), not `reachTargets`. Spec design choice 3's
remark that "the same lists serve attack generation later" applies to a list-based fast path, not
to bitboards. With C3's membership-based G7, the fast layer needs no `Nodup` proof at all for
certificate transfer.

### C9 (low). Small items, no action needed now

- `Move.castle` lives here and Rules' `IsCastle` restates it (spec open item 3). This is fine:
  every client of `Move.castle` (tests, certificates, `ChessGame`) imports MoveGen.
- `Board.upToBlocker`, `slideTargets` and L1.1–L1.2 would move to Rules only if Rules swaps its
  `Slides` instance body for the ray walk. C2 shows that buys little, so leave them here.
- Names: `candidates`, `pseudoMoves`, `legalMoves`, `perft` are top level, consistent with
  `Legal p m`. Settle this together with Rules review C5's namespace rule, not separately.
- `pawnTargets` proposes the double push from any rank, and the back-rank pawn push is accepted
  because `PushMove` reads no rank. Both are documented, and both are correct consequences of
  propose-and-dispose.

---

## 3. Checked and accepted (not concerns)

- **Totality on junk positions** (no king; opponent in check): `legalMoves` is faithful to `Legal`
  there, as spec §3 says. DESIGN §6.4's FEN filter is the right place to exclude such positions.
- **Re-deciding `PseudoLegal` on candidates** costs about 4 % (spec measurement) and is what makes
  soundness free. Worth it.
- **`castleCandidates`' rights guard**: the Round 4 correction (no speed claim) is accurate; core's
  `And` instance short-circuits.
- **Kernel tests use `decide +kernel`**, interpreted tests use `#guard`, and no `native_decide`
  appears, per DESIGN §7.3.
- **`legalMoves_eq_filter`'s proof** comments the `Bool.and_comm` step; the proofs throughout are
  short and say which step does the work.

---

## 4. Summary of recommendations

| # | Priority | Action | Owner |
|---|---|---|---|
| C1 | high, now | Add a `Completeness` section with L7.1–L7.4, L7.6, L7.7 (proof in the Appendix); restore the plain docstrings; register the cheap `Checkmate` instance; drop "trusted until M4" from DESIGN. | spec writer, then translator |
| C2 | high | Attacker nodes via `decide (Legal p m)`; defender nodes via `kingSafeAfter` + `_iff` (≈2×); plan the kernel-side fast layer earlier if large certificates are a Stage 1–2 goal; note in DESIGN §7.4 that `let` does not memoize in the kernel and that instance swaps do not cascade. | architect |
| C3 | med-high | State G7's `moves` clause by membership, not `Perm`; M5 then only serves M8. | THEOREMS / `Game` owner |
| C4 | medium | Create a `ChessTest` lib now; move test code and the agreement tests there. | anyone |
| C5 | medium | Update the docstrings and DESIGN/THEOREMS text listed above when C1 lands. | spec writer |
| C6 | low-med | Decide Rules C1/C5 before M5 is written. | owner |
| C7 | low | Time compiled `perft 4` before fixing test-library depths. | test library |
| C8–C9 | low | None now. | — |

---

## Appendix: the completeness proof (checked in scratch against the built library)

Elaborates with no errors or warnings after `import Chess.MoveGen`, inside `namespace Chess` with
`variable {p : Position} {m : Move}`. Docstrings for the helpers and the spec rows are still to
be written by the spec writer. Names follow spec §7.

```lean
theorem mem_candidatesFrom_pawn (hs : p.board m.src = some ⟨p.turn, .pawn⟩)
    (ht : m.dst ∈ pawnTargets p.turn m.src) (hp : m.PromotionRule p.turn) :
    m ∈ candidatesFrom p m.src := by
  simp only [candidatesFrom, hs, ↓reduceIte, List.mem_flatMap]
  exact ⟨m.dst, ht, mem_pawnMovesTo.mpr ⟨rfl, rfl, hp⟩⟩

theorem mem_candidates_of_mem_candidatesFrom (h : m ∈ candidatesFrom p m.src) :
    m ∈ candidates p :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨m.src, Square.mem_all _, h⟩)

theorem promotionRule_of_none (hp : m.promo = none) (h : m.dst.relRank p.turn ≠ 7) :
    m.PromotionRule p.turn := by
  simp [Move.PromotionRule, hp, h]

theorem PseudoLegal.mem_candidates (h : PseudoLegal p m) : m ∈ candidates p := by
  rcases h with ⟨k, hk, hs, hr, -, hp⟩ | ⟨hs, hd, -, hpr⟩ | ⟨⟨hs, hd⟩, hr1, -, -, hp⟩ |
    ⟨hs, hr, -, hpr⟩ | ⟨⟨hs, -⟩, hr, hr5, -, -, hp⟩ | ⟨w, ⟨hsrc, hk, hdst⟩, ⟨hright, -⟩, hp⟩
  · apply mem_candidates_of_mem_candidatesFrom
    simp only [candidatesFrom, hs, hk, ↓reduceIte, List.mem_map]
    exact ⟨m.dst, mem_reachTargets.mpr hr, by cases m; simp_all⟩
  · exact mem_candidates_of_mem_candidatesFrom
      (mem_candidatesFrom_pawn hs (by simp [pawnTargets, hd]) hpr)
  · refine mem_candidates_of_mem_candidatesFrom
      (mem_candidatesFrom_pawn hs (by simp [pawnTargets, hd]) (promotionRule_of_none hp ?_))
    have := Square.relRank_of_offset_forward (dr := 2) (by simpa using hd)
    omega
  · refine mem_candidates_of_mem_candidatesFrom (mem_candidatesFrom_pawn hs ?_ hpr)
    rcases hr with h | h <;> simp [pawnTargets, h]
  · refine mem_candidates_of_mem_candidatesFrom (mem_candidatesFrom_pawn hs ?_
      (promotionRule_of_none hp (by rw [hr5]; decide)))
    rcases hr with h | h <;> simp [pawnTargets, h]
  · refine List.mem_append_right _ ?_
    have hm : m = Move.castle p.turn w := by cases m; simp_all [Move.castle]
    simp only [castleCandidates, ← hsrc, hk, ↓reduceIte, List.mem_map, List.mem_filter]
    exact ⟨w, ⟨Wing.mem_all w, hright⟩, hm.symm⟩

theorem mem_pseudoMoves : m ∈ pseudoMoves p ↔ PseudoLegal p m :=
  mem_pseudoMoves_iff_candidate.trans ⟨And.right, fun h => ⟨h.mem_candidates, h⟩⟩

theorem mem_legalMoves : m ∈ legalMoves p ↔ Legal p m :=
  mem_legalMoves_iff_candidate.trans ⟨And.right, fun h => ⟨h.1.mem_candidates, h⟩⟩

theorem checkmate_iff : Checkmate p ↔ InCheck p ∧ legalMoves p = [] := by
  simp only [Checkmate, List.eq_nil_iff_forall_not_mem, mem_legalMoves]
```

`stalemate_iff` is the same `simp only` with `Stalemate`. The castling bullet's `hm` re-derives
`CastleMove.eq_castle` inline; in the library, use that lemma instead.
