# Process log: `Chess.Basic`

The record of the back-and-forth between the English specification (`docs/spec/Basic.md`) and the
Lean (`Chess/Basic.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written: none yet.

**Inputs read.** `docs/DESIGN.md` (§1, §2, §4.1–4.2, §5.2–5.5, §5.7, §6.1, §8, §9, §11),
`docs/THEOREMS.md` (§0.5, R1–R6, M1, §9), `docs/research/lean-engineering.md` (§4, §6–§10),
`docs/research/representation.md` (§0, §1, §4, §5, recommendations), and the prototype's
`chess-lean/ChessProof/Basic.lean` (for what not to repeat: biased offsets, sentinel square 64,
hard-coded castling squares). No module of the library exists yet.

**What the draft fixes.** 42 definition entries (D1.1–D8.3), each with a docstring sentence and a
Lean name and type, and 71 lemma entries (B1.1–B7.10, several grouping two or three Lean lemmas),
each with an English statement, a Lean statement shape and a tag ([core], [sanity], [later]). Section
order in the file: Colours first (for `Chess.Game`), then kinds and pieces, squares, offsets,
directions/shifts/rays/knight jumps, colour geometry, wings and castling squares, display.

**Facts checked in Lean 4.28 before writing them down** (scratch files only, nothing in the
library):
- `decide` proves `∀ i j : Fin 8, …` and `∃ i : Fin 8, …`, so the `Square` quantifier instances
  can go through core `Fin` quantifiers.
- `@[ext]` on the structure generates `Square.ext_iff : s = t ↔ s.file = t.file ∧ s.rank = t.rank`.
- `Square.all.Nodup` for `Square.all := (List.finRange 64).map ofIndex` closes by `decide +kernel`
  quickly. Core has no `List.nodup_finRange` and no `List.Nodup.map`.
- `addCoord?_eq_some_iff` closes by `unfold; split <;> simp [Fin.ext_iff] <;> omega`; the
  `offset` definition and its `some` characterization elaborate and evaluate under `decide` and
  `decide +kernel`.
- `mem_knightJumps_iff` (with `Int.natAbs`) closes by `simp [knightJumps]; omega`;
  `∀ j ∈ knightJumps, (j.1 + j.2) % 2 = 1` closes by `decide`.
- `(x.rev).val = 7 - x.val` for `x : Fin 8` by `simp [Fin.rev]`.

**Decisions taken in the English, beyond DESIGN** (each argued in spec §9):
1. `Square.offset` is built from a coordinate helper `Square.addCoord?` and is used only through
   its characterization `offset_eq_some_iff` (B4.2).
2. The square is the first argument of every function on squares (`s.offset df dr`,
   `s.shift d i`, `s.relRank c`). DESIGN's written types put it last; dot notation is identical.
3. `Direction` has eight compass constructors (north = towards rank 8) with `df`, `dr`,
   `opposite`, and the named lists `orthogonals`, `diagonals`, `all`.
4. New name `Kind.slideDirections` (bishop ↦ diagonals, rook ↦ orthogonals, queen ↦ all, others
   ↦ `[]`), so `Reaches` has one slider clause.
5. `Square.ray` is `walk` with fuel 7; the bridge to the index form is `getElem?_ray`
   (`(s.ray d)[k]? = s.shift d (k + 1)`), from which `mem_ray_iff` (M1) follows.
6. New names `Wing.direction` and `betweenKingAndRook`; the castling squares are file literals
   with theorems that they are FIDE 3.8.2.1's squares (`shift_kingHome_two`,
   `shift_kingHome_one`, `getLast?_ray_kingHome`, `betweenKingAndRook_eq`).
7. Geometric halves of later theorems are proved here once: square colour under offsets
   (`isLight_of_offset`, for R5), shift symmetry and in-between matching (for R3), and
   `relRank_of_offset` (pawn direction meets rank arithmetic in one lemma, for R6 and R9).
8. `Piece.all` with quantifiers through colour and kind, so `Chess.Position` can prove its piece
   code round trip by `decide`.
9. Pieces are named `pc` in statements, since THEOREMS reserves `p q` for positions.
10. `Square.flip` and its lemmas are deferred to Stage 2 (R6) with their home fixed here.

**Questions for the translator and the critic.**
- Is `Kind.slideDirections` better in `Basic` (as drafted) or as a local definition in `Rules`?
- Is `betweenKingAndRook` a `Basic` concern, or should `Rules` state "strictly between" itself?
  Drafted here because it is computed from colour and wing alone.
- `offset` through `addCoord?` and a `match`, or one `if` with four conjuncts? The draft prefers
  the helper for reading; the translator should switch if the proof of B4.2 is much shorter the
  other way, and record it here.
- Are the [later] lemmas (`getElem?_ray`, `mem_ray_iff`, `ray_nodup`, the shift uniqueness
  lemmas) cheap enough for the first draft? If not, they move to `Chess/MoveGen/Correct.lean`.

**Next.** Round 2: translate into `Chess/Basic.lean`, record every place the English had to be
made more precise or changed for a proof to go through, then criticize the English again.

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator. Input: the Round 1 critique of `docs/spec/Basic.md`
(sections A–D below refer to it). Every point was accepted; the table says how each was resolved.

**FIDE numbers checked against the handbook** (E012023, fetched 2026-11-01): promotion is 3.7.3.3
(not 3.7.5.1); castling is defined in 3.8.2 (3.8.2.1 is "right to castle lost", 3.8.2.2 "prevented
temporarily"); the colours of the players' pieces are in 2.2 (2.1 is the board's light and dark
squares). §0 now pins the edition and lists every article the spec cites.

| Critique | Change in the spec |
|---|---|
| A1, A2 | D5.8 cites B5.10 for the fuel bound and B5.18/B5.19 (M1 `mem_ray_iff`) for the link to shifts. |
| A3 | D5.6's gloss of the slider spec says `i ≥ 1` and "none when `i = 1`". |
| A4 | New file table on `Wing` (D7.3: `rookFile`, `kingCastleFile`, `rookCastleFile`, and also `betweenFiles`); every castling square is the literal `⟨file, c.homeRank⟩`, so the B7.2 rank lemmas really are `rfl`. Definitions D7.3–D7.7 renumbered D7.3–D7.8. |
| A5 | D1.4 lists Kind, PromoKind, Direction, Wing only, and says Piece and Square do not follow the pattern. |
| A6 | §1 opening rewritten: Lean imports whole modules; a *reader* of `Game` needs only §1. |
| A7 | §4 opening narrowed to "no definition in the specification layer computes one square from another except through `offset`", castling literals checked by B7.4–B7.6. |
| A8 | FIDE edition pinned in §0; promotion 3.7.3.3 (D2.3, B2.3); castling 3.8.2 (B7.4, B7.5, §7, §9.8); Color cites 2.2. DESIGN still says 3.7.5 for promotion (DESIGN §4.4 line ~260, §5.4 line ~400): **not edited here** (outside this module's files); flagged for the DESIGN owner. |
| B1 | `df`/`dr` docstrings name the three directions with each component. |
| B2 | B4.9 is now `(t.IsLight ↔ s.IsLight) ↔ (df + dr) % 2 = 0`, read "keeps its colour exactly when even"; §0 says `%` is `Int.emod`. |
| B3 | B6.7 restated for every offset, with the pawn step as the special case. |
| B4, B5 | §0 gains the binding rule (every name a docstring mentions is bound before the colon; cases by `match` on it). Every definition signature in the spec now binds its docstring's names (`Color.other (c)`, `Kind.slideDirections (k)`, `Square.walk … (n)`, `Square.relRank … (c)`, `Color.forward (c)`, `Color.homeRank (c)`, `Wing.direction (w)`, `Piece.promote (pc) (o)`, …). D2.8 docstring fixed ("The piece that `pc` becomes…", "kind `pk.toKind`"). |
| B6 | D5.8 docstring: "up to and including the last square on the board, … empty if `s` is on that edge". |
| B7 | D5.5 docstring: "moves any number of squares without passing over another piece"; it cites 3.2–3.4 (3.5 is not about sliders). |
| B8 | D7.7 (`rookCastleSquare`) docstring names colour `c` and "the square next to `kingHome c` towards wing `w`"; D7.2 says "from the king's home square towards the rook's home square". |
| B9 | B1.5 states the iff first, then the reason. |
| B10 | D5.1: "each group clockwise, starting from the direction nearest north (north; northEast)". |
| B11 | D3.4: "the order can be read off the definition". |
| B12 | D3.2: "the standard little-endian rank-file (LERF) numbering". The same overclaim in DESIGN §4.2 is flagged, not edited. |
| C1 | `addCoord?`'s integer is `δ`; §0 reserves `x y` for coordinates and `δ` for a coordinate step. |
| C2 | §0 letters: `k k'` kinds, `pk pk'` promotion choices, `o` an optional choice, `jmp` a knight jump, `i j n m` counts. B2.2, B2.5, D2.8, B5.18 renamed accordingly. |
| C3 | B4.8 renamed `Square.offset_injective_steps` and `Square.offset_injective_source`. |
| C4 | `addCoord?` and both of its lemmas are `private`; B4.2 is the only interface. |
| C5 | D5.9 says `Chess.knightJumps` is deliberately top level (a list of offsets, not a function of a square). |
| D1 | New [core] lemma B5.10a `Square.shift_add`; the proof notes of B5.11, B5.14 and B5.18 use it. |
| D2 | B3.8 by `decide +kernel`. |
| D3 | `@[simp]` is now written in every table cell that carries it (§0 says so). The asymmetry is resolved by making every `_other` lemma simp (`homeRank_other`, `relRank_other` join `forward_other`): each pushes `other` outward into `-` or `rev`. |
| D4 | Each `all` is followed immediately by its `mem_all`, `all_nodup` and then the D1.4 instances; B1.6 moved to the top of its table. |
| D5 | D1.4 states the derived `Inhabited` defaults once. |
| D6 | "Why B7.9 is here" lists which lemma serves which clause of DESIGN §5.5; added `rookCastleSquare_ne_rookHome`. |
| D7 | D6.3 lists the en passant target on relative rank 2 and ties it to rank 5 through B6.5 (`rev 2 = 5`); a test checks e3. |
| D8 | §9 item 8: Chess960 would change the types, not just the values, and B7.4 would fail. |
| D9 | §9 item 5: the direction quantifiers "follow the D1.4 pattern". |

**Answers to the Round 1 questions.**
- `Kind.slideDirections` stays in `Basic`: its sanity lemma B5.7 is a one-line `decide`.
- `betweenKingAndRook` stays in `Basic`: with `Wing.betweenFiles` it is one line, and B7.6 ties it
  to `ray`.
- `offset` stays as helper plus `match`: the proof of B4.2 is three lines (see Round 3), so the
  four-conjunct `if` buys nothing.
- All [later] lemmas turned out cheap and are proved in `Basic` (Round 3).

---

## Round 3: translation feedback

Date: 2026-11-01. `Chess/Basic.lean` written definition by definition in spec order; `lake build`
succeeds (Basic builds in about 2 s). No `sorry`, no `native_decide`; every [core], [sanity] and
[later] lemma is proved. Places where the Lean forced a decision the English had not made, or where
the translation was awkward, each now fixed in the spec:

1. **Name clash, B5.10.** The monotonicity lemma "once off the board, further steps stay off" was
   needed by name (see 3). Its natural name `shift_eq_none_of_le` clashed with B5.10. B5.10 is
   renamed `shift_eq_none_of_eight_le`, which says more anyway; the new lemma is B5.12a
   `shift_eq_none_of_le (hji : j ≤ i) (h : s.shift d j = none) : s.shift d i = none`.
2. **B5.9a `isSome_shift_iff` added.** B5.10 and B5.12 are about `isSome`; without a shift form of
   B4.3 each proof would unfold `shift` first. It is the term `isSome_offset_iff`.
3. **B5.12a added; B5.11 reordered.** With B5.10a and B5.12a, `shift_succ` needs no arithmetic at
   all (case on `s.shift d i`), and the `none` case of B5.18a is the same lemma. The spec's old note
   ("each coordinate moves by −1, 0 or +1 per step: a coordinate that has left 0..7 cannot come
   back") was the right idea but not a proof plan. Tables are now in proof order, with letter
   suffixes for new IDs.
4. **Products are atoms for `omega`.** The spec said "rewrite with B5.9, then `cases d` and
   `omega`"; precisely, `cases d` must be followed by `simp [Direction.df, Direction.dr]` to turn
   `↑i * 1` and `↑i * -1` into linear terms. B5.10a and B5.13 avoid the case split entirely
   (`Int.natCast_add`, `Int.add_mul`; `Int.mul_neg` keeps `i * d.df` as one atom on both sides).
   The proof notes now say which lemmas split and why.
5. **B5.18a `getElem?_walk` promoted from proof note to stated lemma.** The induction needs the
   statement for arbitrary fuel `n`; B5.18 is its `n = 7` case. Named and tagged [later].
6. **Equations between `Option Square`s.** B4.5's first proof was a three-way case split. The clean
   proof is `Option.ext fun u => by rw [offset_eq_some_iff, offset_eq_some_iff]; omega`. Recorded
   in §4 as the one pattern for such equations.
7. **B4.3 is not a pure rewrite.** The backwards direction needs a witness square
   `⟨(s.file + df).toNat, (s.rank + dr).toNat⟩`. Proof note corrected.
8. **B4.9 renamed `isLight_offset_iff`.** After the B2 restatement the conclusion is an iff, and
   `isLight_of_offset` read as an implication. Lean naming convention: `_iff` for an iff conclusion.
9. **B5.23 proved directly, not through B4.9.** Core 4.28 has no `Iff.not`, so getting from
   `(t.IsLight ↔ s.IsLight) ↔ (df + dr) % 2 = 0` and an odd `df + dr` to `t.IsLight ↔ ¬ s.IsLight`
   costs more than unfolding `IsLight` and running `omega` on B4.2 and B5.21. The note in §4 still says B4.9 is "the content of R5"; the knight half
   is in fact closed by B5.21 plus B4.2.
10. **`Fin.rev` and `simp`.** `simp [Fin.ext_iff, Fin.val_rev]` on `s.rank.rev = 0 ↔ s.rank = 7`
    hits `maxRecDepth`. B6.6 uses `rw [relRank_black, Fin.ext_iff, Fin.ext_iff, Fin.val_rev]; simp;
    omega` for Black and `rfl` for White. Proof note and warning added. Also, core's `Fin.val_rev`
    reads `8 - (x.val + 1)`, not `7 - x.val`; D6.3 now quotes it as it is.
11. **`omega` knows `Fin` bounds.** D3.2's bound and D3.3's are plain `by omega`; the spec's caveat
    that the bounds "need to be introduced" was wrong and is removed. B3.3 is
    `ext <;> simp <;> omega`.
12. **Instances need docstrings too.** The spec gave docstrings for definitions only; the Lean gives
    every instance a docstring, and the spec now states them (D1.4 pattern, D2.7, D3.5, D3.6, D8.3),
    as well as the field docstrings of `Piece` and `Square`.
13. **Lemma docstrings.** Every theorem carries its English column as a docstring (§0, §11), so a
    reader of the Lean file sees the English next to each statement.
14. **D3.5/D3.6 order.** `IsLight` is defined before the `namespace Square` block that holds the
    instances and lemmas; the spec's two entries swapped to match.
15. **`walk` shadowing.** The binding rule made `n` a named argument; the recursive arm is then
    `| m + 1 => … t.walk d m` so the docstring's `n` is never shadowed. Spec D5.7 shows it.
16. **Private helper and `decide`.** Checked from a scratch module importing `Chess.Basic`: `decide`
    still evaluates `offset` (and proves `∀ s : Square, s.shift .north 8 = none`) although
    `addCoord?` is private. Recorded in D4.1 and D3.6.
17. **Tests.** Added the en passant rank test (D7) and `toString (Square.mk 0 7) == "a8"`; B7.4 for
    all colours and wings is also checked by one `decide` using the `Color` and `Wing` quantifiers.

**Open items for others (not edited, outside this module's files).**
- DESIGN cites FIDE 3.7.5 for promotion (§4.4, §5.4); the 2023 Laws number it 3.7.3.3.
- DESIGN §4.2 says LERF is "the numbering of every chess-programming source".
- DESIGN writes `Square.relRank c s` and `(df dr : Int) : Square → Option Square`; the module puts
  the square first (§9 item 9).

**Next.** File-level design review (`docs/reviews/Basic.md`), then `Square.flip` with R6.

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner. Input: the Lean-level critique of `Chess/Basic.lean`
against `docs/spec/Basic.md` (items F1–F11, R1–R6, P1–P4 below refer to it). English fixed first,
then the Lean matched to it. `lake build` is green; `lake env lean Chess/Basic.lean` reports no
warnings. Meaning is unchanged except for the one weakened hypothesis (B5.16) and the two added
lemmas (B5.7a, B6.7a).

**English corrected (spec).**

| Item | Change |
|---|---|
| F1 | B5.6 now reads "A direction's opposite is orthogonal (diagonal) exactly when the direction is." The Lean docstrings match. |
| F2 | §4's closing paragraph: B4.9 is the bishop half of R5 (through B5.17); the knight half is B5.23, proved from B5.21 and B4.2. The claim that a lemma says "every knight jump has `df + dr` odd" is gone. |
| F3 | B5.23 proof note: the obstacle is getting from `¬ (t ↔ s)` to `t ↔ ¬ s`, which needs a decidable or classical step. Core does have `not_congr`. The Round 3 item 9 above gave the wrong reason; the conclusion stands. |
| F4 | B3.6 / `length_all`: "The list of all squares has 64 entries." |
| F5 | §1 proofs: `mem_all` is `cases c <;> decide`, since `rfl` cannot prove `∈`. |
| F6 | §11: "only core tactics (no Mathlib, no `native_decide`)", plus the `simp only` rule (R4 below). |
| F8 | B5.16 English: "for a positive step count". |
| P4 | §4 states the convention one level up: downstream modules use B5.8–B5.17 and never unfold `shift`, because products are `omega` atoms and their case split is paid once, here. |
| — | D4.2 and D6.3 no longer say DESIGN uses another argument order (fixed there, F11). |

**Lean changed.**

| Item | Change |
|---|---|
| R1 | New section "Decidable quantifiers from a complete list" before "Colours", with `decidableForallOfMemAll` and `decidableExistsOfMemAll` (spec D1.0). The ten instances of Color, Kind, PromoKind, Direction and Wing are now one line each, for example `decidableForallOfMemAll Color.all mem_all P`; their docstrings are unchanged. The instance bodies lose about 20 lines; the file as a whole grows (1032 to 1052 lines) because of the helper section, two new lemmas and a test. Helpers rather than a class `Enumerated α`, so no instance search is added to each `decide` (spec §9 item 10 says why). Checked from a downstream module: `∀ d : Direction, ∀ c : Color, …`, `∃ w : Wing, …` and `∀ s, ofIndex s.index = s` all go by plain `decide`. |
| R2 | Renames following item 8 of Round 3 (`_iff` for an iff, `eq_of` named after what is concluded): `offset_injective_steps` → `steps_eq_of_offset_eq`, `offset_injective_source` → `eq_of_offset_eq`, `eq_of_shift_eq` → `steps_eq_of_shift_eq`, `eq_of_shift_eq_dir` → `dir_eq_of_shift_eq`, `isLight_of_mem_knightJumps` → `isLight_iff_of_mem_knightJumps`. Docstrings of B4.8 rewritten to say what the lemmas conclude. No other module uses the old names. |
| F8 | `dir_eq_of_shift_eq` drops `hj : 0 < j`; the same proof goes through (`omega` derives it from `hi`). |
| R3 | Unused `variable`s removed: `u` in "Squares"; `u`, `n`, `df`, `dr` in the shifts block; the whole `variable {c c' : Color} {w w' : Wing}` line in `Castling` (only `rookHome_inj` used it, and now binds them itself). |
| R4 | `ofIndex_index`, `index_ofIndex`, `length_all` and `mem_knightJumps_iff` use `simp only [...]` with the lemmas they need. `relRank_eq_zero_iff` and `relRank_eq_seven_iff` are now `revert s; cases c <;> decide`, with no `Fin.rev` rewriting and so no `maxRecDepth` hazard; `#print axioms` shows only `propext`. |
| R6 | `isSome_offset_iff`: bare `simp only` replaced by `dsimp only`. |
| F7 | New test: `example : ∀ s : Square, s.shift .north 8 = none := by decide`. |
| P3a | New B5.7a `Kind.opposite_mem_slideDirections : d.opposite ∈ k.slideDirections ↔ d ∈ k.slideDirections` (`cases k <;> cases d <;> decide`), for R3's `reaches_symm`. |
| P1 | New B6.7a `Square.relRank_of_offset_forward (h : s.offset df (dr * c.forward) = some t) : relRank t = relRank s + dr`, by rewriting B6.7 with `Int.mul_assoc`, `forward_mul_forward`, `Int.mul_one`. A double step `s.offset 0 (2 * c.forward)` matches it with `dr := 2`. `dr` rather than a new letter: it is a number of ranks, measured in `c`'s forward direction. |
| — | Module docstring: one implementation note on the quantifier helpers. Two lines over 100 characters wrapped. |

**THEOREMS and DESIGN (outside the module, but they quote it).**
- F9: THEOREMS R6 `Square.flip` uses `s.rank.rev`, the normal form of spec §10 and `relRank`.
- F10: THEOREMS M1 no longer names `Direction.offset`; it says directions have steps `d.df`, `d.dr`
  and one step is `s.shift d 1`. M10's `mem_shift` uses `s.shift d 1` instead of `s.step d`. No
  `step` alias was added.
- F11: THEOREMS R3 and DESIGN §4.1–4.2 write the square first: `Square.offset (s : Square)
  (df dr : Int)`, `Square.relRank (s : Square) (c : Color)`, `s.shift d i`, `s.ray d`. This
  closes the Round 3 open item on argument order.
- P2: spec §10 now lists everything R6 will need here, so the R6 author does not rediscover it:
  `Direction.mirror` (north ↔ south, NE ↔ SE, NW ↔ SW, east and west fixed) with its step lemmas,
  `offset_flip`, `shift_flip`, and the closure of `slideDirections` and `knightJumps` under
  mirroring, alongside the earlier `Square.flip` lemmas. Still not written.

**Not done, and why.**
- R5 (`ray` as `(List.range' 1 7).filterMap (s.shift d ·)`, removing `walk`) and the larger form
  of P1 (`Color.pawnDirection : Direction` and `pawnCaptureDirections`, which would remove the
  `dr * c.forward` products) both change DESIGN §5.2/§5.4/§5.7 and the shape of `MoveGen` and
  `Rules`. They are **owner decisions**, to settle before those modules are written. B6.7a is
  useful under either choice.
- R6, second point (`isLight_shift_of_mem_diagonals` through `mem_diagonals_iff`): the current
  proof is fine, as the critique says.
- Axioms: `offset_eq_some_iff`, `mem_ray_iff` and others use `Classical.choice` through `omega`
  and `simp_all`. Whether the geometry should be choice-free is a project-wide policy question,
  recorded here and not acted on.

**Open items for others.**
- DESIGN still cites FIDE 3.7.5 for promotion and calls LERF the numbering "of every
  chess-programming source" (Round 3 open items, unchanged).
- Owner: decide P1 (pawn directions) and R5 (`ray` by `filterMap`) before `Rules` and `MoveGen`.

**Next.** File-level design review (`docs/reviews/Basic.md`), then R6's flip lemmas.

---

## Round 5: file-level design review

Date: 2026-11-01. Author role: file-level design reviewer. Full review: `docs/reviews/Basic.md`.

**Lean changed (one fix, C1).** The 14 whole-type quantifier instances (`decidableForall` and
`decidableExists` of `Color`, `Kind`, `PromoKind`, `Piece`, `Square`, `Direction`, `Wing`) now have
`priority := low`. Before, they also matched bounded quantifiers (`∀ s ∈ l, P s` is
`∀ s, s ∈ l → P s`) and, being declared after core's `List.decidableBAll`, won: a check over a
three-square list swept all 64 squares (58 ms vs 2 ms on the `betweenKingAndRook` example). Two
`rfl` tests at the end of the file pin the instance choice for `Square`; one implementation note
added to the module docstring. No docstring, statement or proof changed.

**English changed.** Spec D1.4, D2.7 and D3.6 state the priority and the reason; §11 lists the two
new tests.

**Open for the owner** (review C2–C4): pawn direction as a `Direction`; keep `walk` and close R5;
a `sq!e4` square literal elaborator.
