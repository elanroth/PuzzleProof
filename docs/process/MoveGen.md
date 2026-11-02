# Process log: `Chess.MoveGen`

The record of the back-and-forth between the English specification (`docs/spec/MoveGen.md`) and the
Lean (`Chess/MoveGen.lean`, and later `Chess/MoveGen/Correct.lean`). Each round says what changed, in
which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written in the library: none.

**Inputs read.** `docs/DESIGN.md` (whole file; §1, §3.2, §5.7, §6.1, §7.3–§7.4, §8.4 most closely),
`docs/THEOREMS.md` (§0, §1, M1–M11), `Chess/Basic.lean`, `Chess/Position.lean` and `Chess/Rules.lean`
(declarations, and every definition the generator touches), `docs/spec/Rules.md` (§0, §10–§13),
`docs/process/Rules.md` (Rounds 1 and 4, for format and measurements), `docs/reviews/Rules.md`
(C1, C3, C5, C9 concern this module), `docs/research/representation.md` (§2.4–§2.7, §4, §5) and
`docs/research/theorem-landscape.md` (§3.3–§3.4), and the prototype's `ChessProof/Basic.lean`
(`pseudo`, `legal`, `perft`).

**What the draft fixes.** 17 definitions (D1.1–D6.2: three target lists, six candidate builders,
the two generators, `perft` and `perftDivide`, two test utilities, two test positions), 18 lemmas in
this file (L1.1–L4.4; 14 [core], 4 [later]), and the Stage 2 plan for `Correct.lean` (L7.1–L7.7: the
cover lemma, M2, M4, M5, M6).

**The one decision that shapes everything: propose and dispose.** The generator proposes candidate
moves by geometry (`candidates`) and keeps those the specification allows:
`pseudoMoves p := (candidates p).filter (PseudoLegal p ·)`, then the king-safety filter. Considered
and rejected: per-rule generators that restate each rule's conditions (the prototype's shape and
THEOREMS M2's sketch). Consequences, all recorded in spec §8:
- generator soundness (`legalMoves_sound`, the soundness half of M4) is a one-line Stage 1 theorem;
- M4's completeness reduces to one geometric cover lemma (`PseudoLegal.mem_candidates`), which is
  also the Rules review's C3.2 candidate cover;
- the Stage 1 tests need only check completeness and duplicates (`agreesWithLegal`).

**Facts checked in Lean 4.28 before writing them down** (scratch files importing the built
`Chess.Rules`; nothing written in the library):
- Every definition of spec §1–§6 elaborates as written.
- Proved: `Board.mem_upToBlocker`, `mem_slideTargets`, `mem_reachTargets` (M1, about 45 lines),
  `mem_pawnMovesTo`, `CastleMove.eq_castle`, all five generator lemmas of §3, all four perft lemmas.
  Core 4.28 has no `by_contra` (used `Nat.lt_or_ge`); `List.filter_filter` needs `Bool.and_comm` to
  close L3.3; L4.3 needs `List.map_const'`.
- The cover lemma L7.1: skeleton elaborates; the step-move, push and castling cases are proved, the
  double push, pawn capture and en passant cases left as rank arithmetic. So M4 looks like D1, not
  THEOREMS' D2.
- Tests: `agreesWithLegal` holds on 17 positions (Rules' 15 named positions and two new ones);
  perft 1, 2, 3 from the initial position are 20, 400, 8 902; `legalMoves foolsMate = []` by
  `decide +kernel`; e5d6 en passant out of check is legal in the new `epCheckPos`; Black's O-O is
  legal and O-O-O is not after b7a8=N in `promoPos`.
- Found while checking: **the castling candidates need "a king stands on its home square"**.
  Without it, a castling right held with a queen on e1 makes e1g1 a candidate twice, both copies
  pseudo-legal, so `legalMoves_nodup` (M5, stated without `WellFormed`) would be false. Recorded as
  D2.5's first note.
- Measurements (interpreted, initial position, per call): `candidates` 0.3 ms, `pseudoMoves` 2.1 ms,
  a constructive variant 1.1 ms, `legalMoves` 24 ms; perft 3: 17.0 s against 16.2 s for the
  variant. Kernel: `pseudoMoves` 0.65 s, `legalMoves` 3.4 s, `legalMoves foolsMate = []` 3.9 s;
  plain `decide` adds about 2.7 s of elaboration to the 3.4 s. A hypothesis that compiled code was
  slow because `KingAttacked`'s derived instance evaluates `Attacked` on every square was tested
  with a short-circuiting instance and refuted (no change).

**Questions for the critic and the owner** (spec §9):
1. Pull `Correct.lean` into Stage 1 (about 150 lines; removes the generator from the trusted base
   before the first milestone)?
2. M1 is placed in `MoveGen.lean`, against DESIGN §8's table (spec design choice 8). Agree?
3. Faster `Decidable` instances must be registered in `Chess.Rules`, since `legalMoves` captures
   Rules' instances when it is elaborated (design choice 10); if the Rules review's C3.1 is adopted,
   the ray walk moves to Rules.
4. Rules review C1/C5 (structures, `StepMove` → `PieceMove`) are not yet applied; this spec follows
   the current names.
5. DESIGN and THEOREMS edits listed in spec §9 items 5 and 6 (not made here).

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator, answering the Round 1 English critique (A1–A8, B1–B14,
C1–C4, D). Every item was taken; none was rejected. Lean written in the library: none at the time of
this round.

**[A] Statements that were false, or claimed before they were proved.**
- **A1 (D2.6 states the cover as fact).** The docstring now says the candidates "are meant to
  include every pseudo-legal move of `p` (the cover, `PseudoLegal.mem_candidates`, planned in
  `Chess/MoveGen/Correct.lean`); in general some candidates are not pseudo-legal." The note gives
  the plain sentence to restore when L7.1 lands.
- **A2 (perft counts entries, not sequences).** D4.1's docstring counts "ways to choose `n` moves one
  after another …, each an entry of `legalMoves`"; a move counts as often as it is listed; depth 0
  is the empty choice; "no legal moves" became "`legalMoves` is empty". The note says the reading as
  legal sequences (M8) needs M4 and M5. L4.1–L4.3 follow ("the empty choice", "the entries of
  `legalMoves p`").
- **A3 (perftDivide).** "For each entry of `legalMoves p`, in order, …".
- **A4 (Fool's mate read as a mate proof).** The test text now says it is `Game.chess.Mated` once
  L7.6 is proved, and is evidence until then, Rules' `#guard decide (Checkmate foolsMate)` being the
  proof.
- **A5 (rights clause "changes no result").** It changes `candidates` but not `pseudoMoves` or
  `legalMoves`, with the reason (no `CastleMove` without the right; a king does not reach its
  castling square, so no `StepMove` either). Checked in scratch: `kingsPos` with full rights has 7
  candidates against 5, and the same `legalMoves`.
- **A6 (the "Idea" paragraph).** Legal "by a one-line theorem (L3.5)", not "by construction"; the
  castling clause names the king on its home square; "no king of the mover's colour is attacked";
  "never decides a rule itself: its only tests outside `PseudoLegal` and king safety are two guards
  in `castleCandidates`, each a necessary condition of `CastleMove`". Design choice 1 says the same.
- **A7 (§1 intro).** Membership of `t` does not depend on the source or on `t`; the list as a whole
  reads the board.
- **A8 (D5.2 permutation claim).** New [sanity] lemma L5.1 `mem_legalMovesBySpec : m ∈
  legalMovesBySpec p ↔ Legal p m`, in a new `section Testing`; the note now says a `true` makes
  `legalMoves p` a permutation of `legalMovesBySpec p`.

**[B] Ambiguity.**
- **B1.** L3.1–L3.5 name the lists (`m` is in `pseudoMoves p` …; `legalMoves p` is `candidates p`
  filtered by `Legal`, in the same order; every entry of `legalMoves p` …).
- **B2.** D1.2's docstring defines the ray (1, 2, … steps, `s` excluded, to the edge), the all-empty
  case and the edge case. D1.1 and D1.2 both say "occupied".
- **B3, B4.** D1.3: "would reach from `s` on `b`, whatever stands on `s`"; "Jumps and steps that would
  leave the board give no square." D2.1: "Squares that would be off the board are left out."
- **B5.** D2.4 now matches `some ⟨c, k⟩`, tests `c = p.turn` positively first, and uses `p.turn` in
  both branches, so D2.1's "character for character" note holds without a rewrite (the note now
  says "with `c := p.turn` and `s := m.src`"). The docstring says castling is not proposed here.
- **B6.** D2.5's docstring binds `w`, names `Move.castle p.turn w` and "that colour's king home square
  (e1 or e8)", and adds "kingside first".
- **B7.** L2.1: "for colour `c`".
- **B8, B9.** L1.1 in the words of `upToBlocker`; L1.2 and L1.3 bind `d b s` and `k c b s`.
- **B10.** D6.1's docstring describes the position after d7d5 (White to move, in check from d5,
  target d6); the Lean writes `CastlingRights.none`.
- **B11.** `castleRookPos 3` (Black rook d7) and `castleRookPos 4` (Black rook e7, White in check).
- **B12.** Design choice 6: "kingside before queenside (`Wing.all` order)"; theorems "meant for
  clients" are about membership, L3.3 and L4.2 fix the order only internally. D1.3's note: slider
  directions in `k.slideDirections` order.
- **B13.** `isLegal`: builds the candidate list (about 0.3 ms) and decides legality for one move.
- **B14.** Letters: `pk`, `o`, `ts` added; `u` dropped; `j` is a knight jump in D1.3, as in
  `Reaches` (kept as `j` rather than renamed, so D1.3's knight arm stays the same expression as
  `Reaches`' knight arm).

**[C] Edge cases now stated.**
- **C1.** A paragraph after D3.2: `legalMoves` is total and faithful to `Legal` everywhere; with no
  king of the side to move it equals `pseudoMoves`; with the opponent in check it lists captures of
  that king, as `Legal` does.
- **C2.** D2.6's note and a new test: on the empty board (even with full rights) `candidates` is
  empty.
- **C3.** D2.1's notes: a pawn on its own back rank proposes a push to relative rank 1 and
  `PushMove` accepts it (the specification, not the generator, differs from FIDE there); a pawn on
  its last rank proposes nothing. Checked in scratch: a White pawn on a1 lists a1a2; one on a8 has no
  candidates.
- **C4.** D2.2's notes: the promotion choice depends only on `t`; double-push and en passant
  destinations are on relative ranks 3 and 5.

**[D] Wording.** The header names "the perft definitions and equations that M7's tests use"; §10's
"Main statements" lists `mem_slideTargets`; D5.1 says "or with each of the four in turn"; D2.2's
note says "cannot arise once L7.1 is proved".

---

## Round 3: translation feedback

Date: 2026-11-01. Author role: translator. Lean written: `Chess/MoveGen.lean` (17 definitions,
15 theorems, the tests; 390 lines), and `import Chess.MoveGen` added to `Chess.lean`. `lake build`
succeeds with no errors, no warnings, no `sorry`, no `native_decide`; the module elaborates in
about 23–24 s. Every [core] and [sanity] lemma is proved (L1.1–L1.3, L2.1–L2.2, L3.1–L3.5,
L4.1–L4.4, L5.1); [later] lemmas and the Stage 2 plan (L7.1–L7.7) are not written, as the spec
says. Nothing is marked `-- TARGET:`. Exactly `perft_zero` carries `@[simp]`; no instances are
defined. A script compared the two files: every Lean docstring occurs word for word in the spec,
and every definition docstring and every lemma row of the spec occurs in the Lean except the
[later] and §7 rows.

`#print axioms`: `Board.mem_upToBlocker`, `CastleMove.eq_castle`, `legalMoves_eq_filter`,
`legalMoves_sound`, `perft_one`, `sum_perftDivide` and `mem_legalMovesBySpec` use only `propext`
and `Quot.sound`; `mem_slideTargets`, `mem_reachTargets` and `mem_pawnMovesTo` also use
`Classical.choice` (through `omega`, `simp` and `grind`). A fact about the proofs, not the
statements.

The places where the Lean forced a decision the English had not made, or where the translation was
awkward, and what changed in the spec:

1. **`candidatesFrom`'s arms in docstring order.** After B5 the docstring speaks of an occupied
   square first (pawn, other piece) and of the empty square last, but the body matched `none` first,
   so a reader checking one against the other read them in opposite orders. The `match` now puts
   `some ⟨c, k⟩` first and `none` last; Lean accepts either order and nothing else changed (the
   build and all tests are unaffected). *Spec change:* D2.4's body, and a note saying why.
2. **L1.2 needs no edge-of-board argument.** The Round 1 proof unfolded `Slides`, whose index is
   bounded by `i < 8`, and recovered the bound from `shift_eq_none_of_eight_le` with
   `Nat.lt_or_ge`. Rewriting with Rules' `slides_iff` (the unbounded form, proved in Rules for
   exactly this kind of use) removes the bound from the goal, and the proof is two index shifts with
   `omega`. *Spec change:* L1.2's proof note.
3. **L5.1's proof shape.** The `if` inside `legalMovesBySpec`'s `filterMap` compares a built move
   `⟨s', t', o'⟩` with `m`; the proof only goes through after destructuring `m` into `⟨s, t, o⟩`
   first, then `split at h` forward; backward, the filter's `decide` is discharged by `simpa using
   h.1.colorAt_src`. *Spec change:* L5.1's proof note, marked *(checked)*.
4. **Moves written as anonymous constructors need a type ascription in the tests.** `⟨⟨4, 4⟩, ⟨3, 5⟩,
   none⟩ ∈ legalMoves epCheckPos` does not elaborate: on the left of `∈` nothing fixes the type of
   `⟨…⟩`. The Lean writes `(⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ : Move) ∈ …`; `Move.castle …` needs none (one more
   reason for D2.3). *Spec change:* §6 says so, with the example.
5. **One `#guard` per position for the agreement tests.** The English said "for each of the 17
   positions"; a single `#guard` over a list would report a failure without naming the position.
   The Lean writes 17 lines, `castleRookPos 3` and `4` with a comment naming the rook's square (B11).
   *Spec change:* §6 says "one `#guard agreesWithLegal p` line per position, so that a failure names
   its position", and that each test carries a one-line comment as in Rules §10.
6. **Measured cost of the module.** The checklist asked for under 30 s, with the named-move examples
   demoted to `#guard`s otherwise. Measured with the profiler: about 16 s of kernel checking for the
   eight `decide +kernel` examples (0.7–3.4 s each) and about 6 s of interpretation for the
   `#guard`s; 23–24 s in all under `lake build`. No demotion was needed. *Spec change:* a paragraph
   at the head of §6's test list.

Checked and needing no change: every definition elaborated as Round 2 wrote it, including the new
`some ⟨c, k⟩` pattern of D2.4 and `CastlingRights.none` in D6.1; the Round 1 proofs of L1.1, L1.3,
L2.1, L2.2, L3.1–L3.5 and L4.1–L4.4 went through unchanged (L1.1's `some` branch closes by `simpa
[hu] using hj 0 (by omega)`); all tests pass, including the regression counts `[20, 0, 23, 15, 23,
4, 7, 4, 2, 13, 9, 4, 7, 15, 2, 8, 15]` and the new empty-board test.

**Still open for others** (spec §9): pulling `Correct.lean` into Stage 1 (item 1); M1's placement
against DESIGN §8 (item 2 of Round 1's questions); faster instances in `Chess.Rules` (item 4); the
DESIGN and THEOREMS edits (items 5 and 6), to which L5.1 `mem_legalMovesBySpec` should be added
under M7.

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner, answering the Lean critique (F1–F6, R1–R6, P1–P6). Edited:
`Chess/MoveGen.lean`, `docs/spec/MoveGen.md`, `docs/THEOREMS.md` (M1, M3, M4, M6, G1, the
dependency map, open question 3). `lake build` succeeds (7 jobs), no `sorry`, no `native_decide`,
no warnings; the module builds in about 29–30 s (24 s before; the new kernel-checked agreement on
`kingsPos` costs about 5 s). Every proposed change was first checked in scratch
(`scratchpad/r4mg/`). A script checked again that every Lean docstring occurs word for word in the
spec and every spec definition docstring occurs in the Lean.

**English first: where the English was wrong or claimed too much.**
- **F1 (the "only tests" sentence was false).** The generator also tests the piece's colour and
  kind, empty squares, blockers and the edge of the board. The module docstring, the spec's idea
  paragraph and design choice 1 now say what matters: every test outside `PseudoLegal` and king
  safety *only removes candidates*, so none can add an illegal move (soundness, L3.5), and
  completeness needs only that none removes a pseudo-legal move (the cover, L7.1), which is what a
  reader trusts until L7.1 is proved.
- **F2 (docstrings claiming completeness).** `pseudoMoves` is now "The pseudo-legal candidates of
  `p`: …", `legalMoves` "The legal candidates of `p`: the entries of `pseudoMoves p` after which …",
  each followed by the sentence naming the Stage 2 theorem (M2, M4) that will justify the stronger
  reading. The spec notes give the wording to restore when L7.2 and L7.4 land.
- **F4 (the rights guard's speed claim was wrong).** Core's `And` instance is `@[macro_inline]` and
  stops at the first false conjunct; `CastleMove.decidable` tests `IsCastle` first and `CanCastle`
  starts with the right itself, so without the guard a missing right costs about one flag read, not
  "two attack scans per wing". The claim is withdrawn in D2.5 and design choice 5; the guard stays
  because it makes `candidates` tighter and changes nothing downstream. No compiled benchmark was
  run.
- **F5, D5.2's note.** "A `true` makes `legalMoves p` a permutation of `legalMovesBySpec p`" leaned on
  an unstated "no repeats by construction". The note now cites two new theorems instead (P2 below),
  and the "by construction" sentence is gone.
- **R6.** "No move clock and no history *are* read" (D4.1).

**Then the Lean, to match and to read better.**
- **R1, `castleCandidates`.** Now `if` king on its home square `then (Wing.all.filter
  (p.castling.get p.turn)).map (Move.castle p.turn) else []`. The king clause, which does not depend
  on the wing, is tested once, outside; the `= true` is gone. The docstring was reordered to read in
  the body's order ("If a king … stands on …: the move … for each wing … Otherwise none."). Proved
  equal to the Round 3 body in scratch; the tests and counts are unchanged.
- **R2, `legalMovesBySpec`.** Now three named steps: `sources`, every move from them (`moves`), then
  `moves.filter fun m => decide (Legal p m)`, which is the docstring's shape. L5.1's proof lost its
  destructuring of `m` and its `split at h`: `simp only [...]`, then the backward direction builds
  the witness from `m.src`, `m.dst`, `m.promo`.
- **R3, proofs.**
  - `mem_pawnMovesTo`: `by_cases h : t.relRank c = 7 <;> cases o <;> simp [h, PromoKind.mem_all,
    eq_comm] <;> rintro rfl rfl <;> omega`. No `grind`, no `simp_all`; after `simp` every case is
    "same source and target imply the rank fact". (The critic's attempt without the last two steps
    left exactly those four goals.)
  - `legalMoves_eq_filter`: `rw [legalMoves, pseudoMoves, List.filter_filter]; congr 1; funext m;
    simp [Legal, Bool.and_comm]`, with a comment giving the reason for `Bool.and_comm`.
  - `mem_slideTargets`: the two `obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩` became
    `cases j` and an `rintro ⟨_ | i, …⟩` pattern, each with an `omega` for the impossible zero case.
- **F3, the "So: …" sentences are now tested.** Two `#guard`s after the test positions: `epCheckPos`
  has White to move, `InCheck`, en passant target d6 and rights `"-"`; `promoKnightPos` has Black to
  move and rights `"k"`. `epCheckPos`'s squares carry `-- e4` style comments (R6), and the two
  positions' defining moves carry `-- d7d5`, `-- b7a8=N`.
- **P2, agreement as a theorem.** New [core] lemmas L5.2 `mem_legalMoves_of_agreesWithLegal (h :
  agreesWithLegal p = true) : m ∈ legalMoves p ↔ Legal p m` and L5.3
  `nodup_legalMoves_of_agreesWithLegal … : (legalMoves p).Nodup`: design choice 8 applied to
  `agreesWithLegal`. One test uses it: `∀ m, m ∈ legalMoves kingsPos ↔ Legal kingsPos m` by
  `decide +kernel` (about 5 s; M4 at `kingsPos`, kernel-checked rather than interpreted). The other
  sixteen positions keep their `#guard`s, to hold the build near 30 s.
- **P4, the en passant rule as a theorem.** New [core] lemma L2.5 `candidates_ignores_epTarget (e :
  Option Square) : candidates { p with epTarget := e } = candidates p`, proved by `rfl`, and design
  choice 13 ("the candidates read the board, the side to move and the castling rights, never the en
  passant target"). It is why G16 `legalMoves_normalize` can be list equality, and it makes a later
  optimization that reads `epTarget` in `candidates` fail to build rather than quietly break G16.
- **Line lengths.** `mem_pawnMovesTo`'s statement (105 characters, from Round 3) was wrapped.

**Recorded for others, not decided here.**
- **P3 (kernel cost of king safety), spec open item 4, rewritten.** Design choice 10 no longer says
  speed-ups *must* go in Rules: they can go in Rules' instances (C3.1) or in this module as a
  Boolean `kingSafeAfter` built from `reachTargets` from the king's square, with an `_iff` lemma
  (THEOREMS M3 revived); `legalMoves_eq_filter` is then one `List.filter_congr` away and Rules' text
  stays the obviously correct version. Measured: `legalMoves Position.initial` 3.4 s and
  `legalMoves foolsMate = []` 3.9 s in the kernel, about 90 % in the king-safety filter. The owner of
  the Rules/MoveGen boundary should choose before certificate (C-tier) work starts measuring.
- **P5.** Spec open item 8: a `Nodup`-and-same-members-implies-`Perm` helper (about 10 lines;
  core lacks Mathlib's `perm_ext_iff_of_nodup`) for M9, to sit in Basic or a list-utilities module.
- **R4.** Spec open item 10: a shared `pawnCaptureSquares c s` for the pawn diagonals in Rules'
  `Reaches .pawn`, `reachTargets .pawn` and `pawnTargets`. Not done: it changes Rules' trusted text,
  and the repetition is deliberate (the cover is `simp [pawnTargets, h]`).
- **R5.** Spec open item 9: move `legalMovesBySpec`, `agreesWithLegal`, L5.1–L5.3 and the two test
  positions to the test library when it exists.
- **F6, THEOREMS.** Edited: M1 now states `mem_slideTargets : t ∈ slideTargets d b s ↔ Slides d b s
  t` and `mem_reachTargets`, one `↔` each, Stage 1 (done); M3 is marked deferred (no executable
  `inCheck`), and would return as `kingSafeAfter_iff` only if P3 goes that way; M4's "Forces" gives
  the actual filter and the cover, and its "Meta" no longer depends on M3; M6 is stated with
  `InCheck p` / `¬ InCheck p`; `Chess.game`'s `Mated` (G1) is `InCheck p ∧ legalMoves p = []`; the
  dependency map and open question 3 match. Still open: the M2 "Forces" remark on the cover and
  M7's list of named positions.

**Checked and kept.** P1 (the cover traced case by case needs no attack or pin reasoning) and P6
(nothing here forces `WellFormed` onto Stage 2) needed no change. `CastleMove.eq_castle` stays here
until open item 3 (moving `Move.castle` to Rules) is decided.
