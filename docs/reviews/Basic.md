# File-level design review: `Chess.Basic`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/Basic.lean` (whole file), `docs/spec/Basic.md`, `docs/process/Basic.md` (Rounds 1–4),
`docs/DESIGN.md` (§1–§5, §8), `docs/THEOREMS.md` (R1–R7, M1), and the prototype's
`chess-lean/ChessProof/Basic.lean` for comparison. No other library module exists yet.

State after this review: `lake build` green; `lake env lean Chess/Basic.lean` gives no warnings;
no `sorry`, no `native_decide`. 1076 lines, 43 definitions, 118 lemmas. Basic builds in about 2.4 s.

---

## 1. Verdict

**Sound foundation; build on it.** The file does what DESIGN §8.1 asks, the English and the Lean
match line for line, and the shape is right for the later layers:

- one geometric primitive (`Square.offset`) with one characterization (`offset_eq_some_iff`), and
  a private helper underneath it, so the *implementation* of offsets can change later without
  touching a single downstream proof;
- slider geometry in two forms (index form `shift` for the specification, list form `ray` for the
  generator) already joined by `getElem?_ray` / `mem_ray_iff` (M1's geometric half is done);
- the geometric halves of R3 (shift symmetry, in-between matching, `opposite_mem_slideDirections`,
  `neg_mem_knightJumps`), R5 (`isLight_offset_iff`, `isLight_iff_of_mem_knightJumps`) and the pawn
  rank arithmetic for R6/R9 (`relRank_of_offset`, `relRank_of_offset_forward`) are proved here once;
- castling squares are readable literals with theorems tying them to FIDE 3.8.2, and the
  disjointness facts `play` needs (DESIGN §5.5) are already proved;
- `Fin 64` is only a proved bijection (R1), which is exactly the seam a bitboard layer needs.

I checked every chess fact by hand (light squares, knight jumps, direction steps, castling files,
`betweenFiles`, relative ranks, the en passant ranks) and found no error.

One real problem was found and fixed (C1 below). The rest are decisions to take before `Rules` and
`MoveGen` are written, plus small conveniences.

---

## 2. Change made in this review

### C1 (fixed). Whole-type quantifier instances hijacked bounded quantifiers

**Problem.** `∀ s ∈ l, P s` *is* `∀ s, s ∈ l → P s`, so the instance
`Square.decidableForall (P : Square → Prop) …` matches it with `P := fun s => s ∈ l → P s`. Being
declared after core's `List.decidableBAll`, at the same priority, it was tried first and won.
Checked with `#synth` before the fix:

```
#synth Decidable (∀ s ∈ l, s.rank = 0)          -- Square.decidableForall fun s => s ∈ l → …
#synth Decidable (∀ d ∈ Direction.diagonals, …) -- Direction.decidableForall …
#synth Decidable (∃ s ∈ l, s.rank = 0)          -- Square.decidableExists …
```

So every bounded quantifier over a list of squares was decided by sweeping all 64 squares and
testing list membership for each. Measured on
`∀ c w, ∀ s ∈ betweenKingAndRook c w, s.rank = c.homeRank`: **58 ms before, 2 ms after**.

**Why it mattered beyond `Basic`.** The pattern recurs everywhere downstream:
`∀ s ∈ betweenKingAndRook c w, b s = none` (CastleMove), `∃ d ∈ k.slideDirections, …` (Reaches),
`∃ jmp ∈ knightJumps, …`, and DESIGN §5.7's generator soundness test
`∀ m ∈ legalMoves p, Legal p m`. DESIGN §5.6 plans a whole-type enumeration of the
64 × 64 × 5 candidate moves; if that becomes a `Move` instance at default priority, the soundness
test would silently enumerate 20 480 candidates instead of the ~30 listed moves. It would still be
*correct*, just slow enough to make kernel-checked certificates impractical, and nobody would see
why.

**Fix.** All 14 whole-type instances (`decidableForall`/`decidableExists` of `Color`, `Kind`,
`PromoKind`, `Piece`, `Square`, `Direction`, `Wing`) now carry `(priority := low)`. After the fix
the same `#synth`s return `List.decidableBAll` / `List.decidableBEx`, and plain unbounded
quantifiers (`∀ s : Square, …`, `∀ c w, …`, `∀ pc : Piece, …`) still go through the library's
instances (all file tests pass, including `∀ s : Square, s.shift .north 8 = none` by plain
`decide`). Two regression tests were added at the end of the file:

```lean
example (l : List Square) (P : Square → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∀ s ∈ l, P s)) = List.decidableBAll P l := rfl
example (l : List Square) (P : Square → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∃ s ∈ l, P s)) = List.decidableBEx P l := rfl
```

Also edited: one implementation note in the module docstring; spec D1.4, D2.7, D3.6 and the §11
test list now say `priority := low` and why; process log Round 5. No docstring, statement or
proof changed.

**Convention for later modules (please adopt in DESIGN §4.1):** *every* instance of the form
`Decidable (∀ x : T, P x)` or `Decidable (∃ x : T, P x)` for a whole type `T` (in particular a
future `Move` or `Board` enumeration) is declared with `priority := low`, and its module adds the
two `rfl` tests above for `T`.

---

## 3. Concerns, in priority order

### C2 (high, owner decision before `Rules`). Pawn direction: `Int` or `Direction`?

Process Round 4 left this open (item P1). My recommendation: **add
`Color.pawnDirection : Direction` (north for White, south for Black) and state pushes with
`shift`**, keeping `Color.forward` as the lemma `c.pawnDirection.dr = c.forward`.

- Single push `s.shift c.pawnDirection 1`; double push `s.shift c.pawnDirection 2`; the square
  passed over is `s.shift c.pawnDirection 1`, and "the double push passes over the single push
  square" is `shift_add`, already proved. With `Int` the same facts are about
  `s.offset 0 (2 * c.forward)`, products that `omega` treats as atoms (spec §4, P4), so every
  pawn proof starts with `cases c`.
- R6 becomes `c.other.pawnDirection = c.pawnDirection.mirror`, the same shape as the
  `Direction.mirror` lemmas spec §10 already plans for sliders.
- Captures can stay `s.offset df c.forward` with `df = ±1` (two offsets), or become two directions
  (`northEast/northWest` vs `southEast/southWest`). Either is fine; pick one and use it in both
  `Reaches` and `EnPassantMove`.

This is cheap now (one definition, three lemmas) and painful after `Rules`, `MoveGen` and
`Invariants` are written against the other shape.

### C3 (medium, owner decision before `MoveGen`). Close R5: keep `walk`

Process Round 4 also left open replacing `walk` by `(List.range' 1 7).filterMap (s.shift d ·)`.
I recommend **keeping `walk`** and closing the item: `filterMap` shifts list positions whenever an
entry is dropped, so `getElem?_ray` would need the monotonicity lemma
(`shift_eq_none_of_le`) inside an index argument, while the current proof is a clean induction.
`walk` also stops at the edge, which is what the generator wants. If `walk` stays, consider making
`Square.walk` and `getElem?_walk` implementation details (private, or documented "use `ray`") so
that nothing downstream depends on the fuel parameter; `ray`, `getElem?_ray`, `mem_ray_iff` and
`ray_nodup` are the interface.

### C4 (medium). Readable square literals for tests and statements

Tests read `(Square.mk 4 3).index = 28` and `Square.mk 0 7`. The owner plays chess; `e4` and `a8`
are what should appear. DESIGN rules out 64 named constants, rightly. A tiny term elaborator
`sq!e4` (or `sq "e4"`) that expands *at elaboration time* to the structure literal `⟨4, 3⟩` keeps
the kernel term unchanged, adds nothing to the trusted base (what is checked is the literal), and
makes every later test and per-node lemma readable. It belongs in the "Display" section, or in a
small `Chess/Notation.lean` imported by tests. Decide before `Position` and `Rules` accumulate
tests in the `Square.mk` style.

### C5 (low). `Repr Square` prints `{ file := 4, rank := 1 }`

`#eval` of a list of moves will print nested records. Since nothing in the specification reads
`Repr`, a hand-written `Repr Square` that prints `e2` (via `Square.name`) and a `Repr Move` that
prints UCI (`e2e4`) would make `#eval` output of the generator usable for debugging. Spec D8.3
currently says "`Repr Square` stays derived"; this is the one place I would change it. Zero proof
impact.

### C6 (low, measured). Kernel cost of `Int` offsets

`Square.offset` computes with `Int`. Measured under `decide +kernel`, one offset from each of the
512 (square, direction) pairs: **174 ms with the current `Int` helper, 70 ms with a `Nat`-only
helper** (`match δ with | .ofNat n => … | .negSucc n => …`); all 512 rays: 799 ms vs 304 ms. A
factor of about 2.5. Speed is the owner's last priority, and the design already makes this a local
change: `addCoord?` is private and every proof goes through `offset_eq_some_iff`, so swapping the
helper means re-proving the two private lemmas and nothing else. **Do it only if** certificate
benchmarks (DESIGN §7.4) show offsets dominate. Recorded here so the option is not rediscovered.

### C7 (low). Seams the fast layer will need

`index` is the bitboard seam and is in place. When `Chess/Fast` starts it will want, here:
`index_offset : s.offset df dr = some t → (t.index.val : Int) = s.index.val + 8 * dr + df`
(a shift of a bitboard is an offset of every square), and `index_flip` (already planned in spec
§10). Both are one-line `omega` / `decide` proofs. Related: `val_index` is `@[simp]`, so `simp`
will rewrite every `s.index.val` into `8 * s.rank.val + s.file.val`. That is right for this file
but may fight bitboard proofs that want `s.index` atomic; revisit then (use `simp [-val_index]` or
drop the attribute).

### C8 (low). Conventions worth writing down in DESIGN

- The derived `Inhabited` defaults (white, pawn, a1, north, kingside) are arbitrary. The
  specification layer must never use `default`, `get!`, `[i]!` or `Option.get!`; these defaults
  exist only so that `deriving` and `#eval` work.
- Downstream modules use the `offset` / `shift` characterizations and never unfold `shift`
  (spec §4, P4). Worth a sentence in DESIGN §4.2 so the `Rules` author sees it.
- Tests live at the end of `Basic.lean` until a test library exists; when it does, move them so
  that `Game`, which imports all of `Basic` for `Color`, does not re-elaborate them.

### C9 (accepted, not a concern). Things I checked and would not change

- **Two `Fin 8`, not `Fin 64`**: right. Nested 4096-pair sweeps (`∀ s t : Square, …`) take about
  0.3 s under either `decide` or `decide +kernel`, so R3's leaper checks by `decide` are feasible.
- **`Classical.choice` in theorem axioms** (through `omega` and `simp_all`): harmless. Definitions
  used in computation (`offset`, `ray`, the quantifier instances) depend on no `Classical.choice`
  (`#print axioms`); proofs are never reduced by `decide`.
- **Castling squares as literals** with characterizing theorems rather than defined via `shift`:
  right (no `Option` in their types). Chess960 would change their types; out of scope, and the
  spec says so.
- **Helpers instead of a class `Enumerated α`**: right for five small types.
- **`Kind.slideDirections`** in `Basic`: right; it gives `Reaches` one slider clause.
- **Section order** (Colours first) for `Game`: fine. `Game` still rebuilds when anything in
  `Basic` changes (2.4 s), which is negligible.

---

## 4. Stale text outside this module (flagged, not edited)

- DESIGN §4.4 (line ~260) and §5.4 (line ~400) still cite FIDE **3.7.5** for promotion; the 2023
  Laws number it **3.7.3.3** (process Rounds 2–4).
- DESIGN §4.2 still calls LERF "the numbering of every chess-programming source"; it is the common
  convention, not universal.
- DESIGN §4.1 lists the enumerated types as `Color, Kind, PromoKind, Wing, Square`; `Direction`
  and `Piece` also have the full R2 trio.

## 5. Summary of recommendations

| # | Priority | Action | Who |
|---|---|---|---|
| C1 | high | Low-priority whole-type instances | **done here**; adopt as DESIGN convention |
| C2 | high | `Color.pawnDirection : Direction`; pushes via `shift` | owner, before `Rules` |
| C3 | medium | Keep `walk`; close R5; treat `walk` as internal | owner, before `MoveGen` |
| C4 | medium | `sq!e4` literal elaborator | owner, before `Position` tests |
| C5 | low | `Repr Square` as name, `Repr Move` as UCI | `Position` author |
| C6 | low | `Nat` helper for `addCoord?` if benchmarks demand | later |
| C7 | low | `index_offset`, `index_flip`; reconsider `@[simp] val_index` | `Fast` author |
| C8 | low | Write the conventions into DESIGN | DESIGN owner |
