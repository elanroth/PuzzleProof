# File-level design review: `Chess.Rules`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/Rules.lean` (whole file), `docs/spec/Rules.md` (whole file), `docs/process/Rules.md`
(Rounds 1–4), `Chess/Position.lean` and `Chess/Basic.lean` (declaration outlines, plus `Move`,
`Position`, `Board.unpack`, `Square.offset`, `Square.shift`), `docs/reviews/Basic.md` and
`docs/reviews/Position.md`, `docs/DESIGN.md` (§3, §5), and `docs/THEOREMS.md` (R3–R11, M4–M6,
G16, C3).

State at review time: `lake build` green; `lake env lean Chess/Rules.lean` prints no warnings; no
`sorry`, no `native_decide`. 1 218 lines before this review (75 theorems, 71 definitions and
instances including the test positions). Every one of the 137 non-test Lean docstrings occurs word
for word in the spec (checked by script, whitespace-insensitive; the 9 test-position docstrings are
exempt by spec §10). No line is longer than 100 characters.

Experiments behind the findings were run in scratch files outside the library. Kernel timings are
`decide +kernel` with `set_option profiler true`, on this machine, one process at a time.

---

## 1. Verdict

**Faithful, readable, and well shaped for the theorems that follow. Build on it.** I found no
chess error. The concerns below are about what later modules will pay for, not about what this
file says.

What is right and should not change:

- **Shapes shared by the rules and by `play`** (`IsEnPassant`, `IsCastle`, `IsDoublePush`), with
  the bridge lemmas `PseudoLegal.isEnPassant_iff` / `isCastle_iff` / `isDoublePush_iff`. This is
  the single most important design decision for R7, R9 and M4: `play` and `PseudoLegal` cannot
  disagree about what en passant or castling is, and the proof that they agree already exists.
- **`play` as write lists carried out by one `Board.setMany`, every step reading the position
  before the move.** R4 is one list lemma, `touched` is the write list's squares by definition, and
  the Position review's C1 hazard (eta-expanded `Board`-valued conditionals) is avoided without
  waiting for that decision. The same shape maps one-to-one onto a bitboard implementation
  (step 1, 2, 3 = three XOR updates), so the Stage 5 refinement can be stated step by step.
- **Revocation by squares** (`Move.Revokes`). It is Stockfish's `castlingRightsMask`, so the fast
  layer can use the classical mask table with a one-line refinement; R8 is two lines; and rights
  held after a move are always backed by an untouched king and rook. I checked the argument in
  design choice 8 and agree with it.
- **`Slides` in index form, `reaches_congr`, `Board.attacked_iff`.** The statements R3 needs are
  already in the form R3 will use. `reaches_congr` is exactly DESIGN §5.2's sentence.
- **`Position.CanCastle`** isolates FIDE 3.8.2.1–3.8.2.2 from the move; a FEN validator and the
  generator want precisely this predicate.
- **Totality with honest junk.** No `get!`, no sentinel, no `findKing`; kingless sides are
  characterised (L9.4–L9.8) instead of being silently stalemated as in the prototype.
- **Hand-written `CastleMove.decidable`** is justified by measurement and documented; every other
  instance is `unfold; infer_instance`.

Fidelity checks I ran beyond the file's tests, all passing (five are now in the file, §2): Black
en passant on rank 3 (d4xe3 after e2e4, victim removed); an en passant target with no victim
permits nothing; castling with the rook attacked is legal; a piece on g1, or an attack on g1,
forbids O-O; a king may not capture a defended piece; e7e5 sets target e6.

---

## 2. Change made in this review

**Tests added** (end of `Chess/Rules.lean`, before "Attack geometry"; spec §10 gained a matching
bullet). Three named positions, each with a docstring in the §10 style, and nine `example`s:

- `blackEpPos`: all existing en passant tests were White capturing; this one exercises
  `relRank 5` and `epVictim` for Black (d4xe3), and that a target without a victim pawn gives no
  capture.
- `rookAttackedPos`: FIDE 3.8.2.2 lets the rook be attacked; the existing tests covered "b1 may be
  attacked" but not the rook's own square, nor "g1 occupied" / "g1 attacked" (the landing square,
  tested through `Legal`).
- `defendedPos`: a king may not capture a defended piece. This is the case where `Reaches`
  deliberately ignores what stands on the target (D2.2's "any target" note), so it deserved a test.

`lake build` stays green (module about 7.6 s), no new warnings, all lines at most 100 characters.
Nothing else in the Lean, the spec or the process log was changed.

---

## 3. Concerns, in priority order

### C1 (high, decide before `MoveGen`). Make the six rules Prop-valued structures with named fields

Design choice 14 deferred this to M2/M5. I recommend doing it **before** `MoveGen`, because that is
where the cost lands. This file already contains eight six-way positional destructurings such as

```lean
rcases h with ⟨k, -, -, -, h, -⟩ | ⟨-, -, he, -⟩ | ⟨-, -, -, he, -⟩ | ⟨-, -, h, -⟩ |
  ⟨⟨-, -, he, -⟩, -⟩ | ⟨w, ⟨-, -, hd⟩, ⟨-, -, hb, -⟩, -⟩
```

M2 (each rule ↔ its generator branch), M5 (fifteen pairwise exclusions, L4.6), R7 and R9 will add
dozens more. Each one encodes the conjunct order of six trusted definitions; reordering or adding
a clause breaks all of them.

The change is cheap and improves the trusted text, which is the deciding argument: one field per
English clause, each with its own docstring, is a closer translation of FIDE than a five-way `∧`.
Measured in a scratch file with `PushMove` rewritten as

```lean
structure PushMove (p : Position) (m : Move) : Prop where
  /-- `m.src` holds a pawn of the side to move. -/
  pawn : p.board m.src = some ⟨p.turn, .pawn⟩
  /-- `m.dst` is one square straight forward from `m.src`. -/
  forward : m.src.offset 0 p.turn.forward = some m.dst
  /-- `m.dst` is empty. -/
  dst_empty : p.board m.dst = none
  /-- The move names a promotion choice exactly when it reaches the last rank. -/
  promo : m.PromotionRule p.turn
```

with `decidable_of_iff (… ∧ … ∧ … ∧ …) ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, …⟩`:
the existing anonymous-constructor `rcases` patterns still work unchanged, `h.dst_empty` works,
`decide` and `decide +kernel` work, and the compiled sweep gives the same 8 pushes from the
initial position. So the migration can be done rule by rule, with proofs moving to field names
only as they are touched. `StepMove`'s `∃ k` becomes a field `kind : Kind`. `CastleMove` keeps
its hand-written instance (guard on `isCastle`, then `decidable_of_iff` on the rest).

### C2 (high, before the module is called final). Prove L4.11, the castling landing-square lemma

This is the one place where the Lean does not say literally what FIDE says (the landing square is
tested after the move, through `Legal`, not before it). The argument in the D4.6 note is right, but
it is an argument, and this is trusted text. Two observations that should make the proof short:

- **It may not need a one-king hypothesis.** e1/e8 and h1/a1 (h8/a8) are edge squares: they are
  interior points only of their rank. So emptying them opens no file or diagonal to any square, and
  along the home rank the rook lands on the crossed square, which blocks everything that emptying
  the king's home square could open. Hence for every target square `t` (not only the landing
  square, and not only the castling king's), an attack by the other colour after castling implies
  one before, except on the squares the king and rook themselves occupy. A statement of the form
  `CastleMove p w m → (¬ (p.play m).board.KingAttacked p.turn ↔ ¬ p.board.Attacked p.turn.other
  (kingCastleSquare p.turn w))` under `¬ InCheck p` (already in `CanCastle`) looks provable for
  every board.
- **The tool is already here:** `reaches_congr` on the two boards, which agree off
  `{kingHome, rookCastleSquare, rookHome, kingCastleSquare}`, plus `Square.shift` arithmetic for the
  single rank-line case. Leapers and pawns do not read the board at all.

### C3 (medium-high, for `Game` and certificates). The kernel cannot afford the specification's terminal tests

Measured (kernel, Fool's mate, `foolsMate` from the test section):

| Decision | Kernel time |
|---|---|
| `Legal pre Qd8h4` (the mating move) | 0.40 s |
| `InCheck foolsMate` | 0.26 s |
| 64 candidates from an empty square (`¬ Legal …`) | 0.30 s |
| own-piece sources only: `∀ s, colorAt s = some turn → ∀ t, ¬ Legal ⟨s, t, none⟩` (1 024 candidates) | 28 s |
| `Checkmate foolsMate` (20 480 candidates) | did not finish in 500 s |
| the same 1 024 candidates with the board as a packed literal (`Board.unpack N`) | 28 s |

The last row shows the cost is in the rules themselves, not in reading a chained board. So any
certificate node that must show "these are all the legal moves" (every defender node of a forced
win, every mate leaf) is out of reach through `Legal`'s own instance. DESIGN already routes this
through the generator (M6) and accepts trusting the generator until M4. Two cheap steps would
shrink that gap, neither changing a trusted definition:

1. **Faster `Decidable` instances, proved equal.** Instances are not trusted text, so they can be
   swapped for faster ones with `decidable_of_iff`. The slider test is the hot spot: index form
   recomputes `shift d j` for every `j < i` (quadratic, with `Int` arithmetic in the kernel). A
   prototype ray walk (`shift d 1` repeatedly, stop at the first occupied square) decides the 64
   targets of a queen on d4 in 0.40 s against 1.14 s for `Reaches.decidable` (about 3×). M1 has to
   prove ray-walk ↔ `Slides` anyway; when it does, register the walk as `Slides.decidable`.
   `Board.Attacked` on all 64 squares of the initial board costs 5.4 s; the super-piece form (R3.3)
   from the king's square is the next instance to swap in, after R3.
2. **A candidate cover, proved before M4.** `PseudoLegal p m → m ∈ candidates p` for a crude list
   (own-piece sources; targets on the source's queen lines, knight jumps and pawn offsets, ignoring
   blockers; promotion choices only on the last rank) is far easier than M4's completeness (no
   walking, no blocker reasoning: each rule's geometry implies membership). It cuts the 20 480
   candidates to a few hundred and gives kernel-checked "no legal move" without trusting the
   generator. It belongs in `MoveGen` (or a small `Rules/Cover.lean`), stated against this file.

### C4 (medium, owner sign-off now). The en passant target is set after every double push; positions are not FIDE-identical

`Move.epTargetAfter` follows the PGN/FEN convention (Position's field docstring). Consequently two
`Position` values that FIDE treats as the same position (9.2.3: same possible moves) can differ
in a dead target. THEOREMS G16 says the decision about `play` "belongs to Stage 1", and this file
has made it by default. I agree with the choice (it is the simplest faithful rule, and G16 shows
that Stockfish's convention does not remove the need for a normalisation anyway), but it should be
recorded as a decision in DESIGN, because changing step 5 later changes trusted text and every
theorem about `epTarget`. Consequences to plan for: certificate DAG sharing (C6) and any repetition
or draw certificate (G9) must key positions by `Position.normalize`, not by `Position` equality.

### C5 (medium). Fix names and homes before anything imports them

Renaming after `MoveGen`, `Game` and certificates use these names is painful; now it is a sed.

- **`StepMove` covers slides of any length.** The docstring has to say "A step move is any non-pawn
  move other than castling"; a name that needs that sentence is the wrong name. `PieceMove`
  (noted in Round 4 as the alternative) says it.
- **Write the namespace convention down.** The file's current rule is coherent but implicit:
  relations of a position and a move are top level (`Legal p m`, `PseudoLegal p m`, the six rules),
  properties of a position alone are mixed (`InCheck p`, `Checkmate p` top level, but
  `Position.CanCastle`, `Position.play` in the namespace). Either keep it and state it in DESIGN §2,
  or move `InCheck`, `Checkmate`, `Stalemate` to `Position.` (giving `p.InCheck`). I lean to keeping
  the current names and writing the rule down; the point is to settle it once.
- **Move the general helpers to their modules** (spec §12 items 5 and 7): `Board.colorAt`,
  `Board.kindAt`, `Board.setMany` and its lemmas, `CastlingRights.ofGet`/`get_ofGet` to Position;
  `Color.forward_ne_zero`, `rookCastleSquare_ne_kingHome`, `shift_kingHome_one_ne`,
  `Square.file_eq_of_offset_zero` to Basic. No statement changes; `MoveGen` will need several of
  the private ones, which it cannot currently see.
- **Position's `CastlingRights` docstring is now false** ("changed only with `revoke` and
  `revokeAll`"): `play` changes rights through `ofGet`. A false sentence in trusted text is a
  fidelity defect, even if no theorem depends on it. Spec §12 item 7 has the replacement wording.

### C6 (medium-low). `play` must only be applied to legal moves downstream

`play` is total and its junk is real junk: `Move.IsEnPassant` reads no rank, so a non-pseudo-legal
move onto a hand-written target removes whatever stands on `epVictim`, possibly the mover's own
piece. That is fine here (only R4's frame lemma, `play_turn` and `castling_play_le` hold without
`PseudoLegal`, and they are stated so), but it means the game layer and every certificate checker
must guard each `play` with `Legal` (or with generator membership). Worth one sentence in DESIGN
§6.4, so that nobody writes a checker that replays an unchecked move list.

### C7 (low). Stale or false text outside this module (flagged, not edited)

- DESIGN §5.4, en passant note: "A hand-written FEN with a nonsensical target cannot produce a
  capture FIDE forbids." Round 2 (critique A1) showed this is false; the spec's D4.5 note has the
  corrected wording ("some previous double push would explain").
- DESIGN §5.4 cites promotion as FIDE 3.7.5 (pre-2023 numbering); this module uses 3.7.3.3.
- DESIGN §5.4 does not mention `IsDoublePush` or `CanCastle` (already spec §12 item 6), and §5.5
  defines `IsCapture` with `.isSome` where the Lean has `≠ none`.
- DESIGN §5.6 says the 20 480-candidate decision is "fine for tests under `native_decide`", which
  contradicts the no-`native_decide` policy (§7.3); C3's numbers say what it actually costs.
- Spec §11 lists design choices in the order 1–10, 13, 14, 11, 12. Renumbering would break
  references; moving 13 and 14 after 12 would not.

### C8 (low). Put the docstring-sync check in the repository

Every round of the process relies on "a script compared the two files", and no script is checked
in. Without it, the English and the Lean will drift silently. Ten lines are enough (this is the one
used for this review):

```python
import re, sys
lean, spec = open(sys.argv[1]).read(), open(sys.argv[2]).read()
norm = lambda s: re.sub(r'\s+', ' ', s).strip()
nspec = norm(spec.replace('|', ' '))
docs = re.findall(r'/--(.*?)-/', lean, re.S)
miss = [d for d in docs if norm(d) not in nspec]
print(len(docs), "docstrings;", len(miss), "missing")
for d in miss: print("  -", norm(d)[:110])
```

(`scripts/` is the untrusted directory in DESIGN §3, which is the right home.) A second check worth
adding: every theorem statement in a spec table occurs in the Lean.

### C9 (low, for later). What the fast layer will need from this file

Nothing here blocks Stage 5, and two choices actively help (write lists; square-mask revocation).
For the record: the refinement of `play` should be stated per step (`pieceWrites`,
`enPassantWrites`, `castleWrites`, `castlingAfter`, `epTargetAfter`), mirroring this file, rather
than for `play` as a whole; and the fast attack test should be related to `Board.attacked_iff`
(squares and kinds), not to the `match` inside `AttacksFrom`.

---

## 4. Checked and accepted (not concerns)

- **`@[simp]` lemmas with hypotheses** (`colorAt_of_eq_some`, `kindAt_of_eq_some`): their
  variable `pc` does not occur in the left-hand side, which can make a simp lemma inert. Checked: it
  is not; `simp [h]` with `h : b s = some ⟨c, .rook⟩` proves `b.colorAt s = some c` through it, and
  `simp [-Board.colorAt_of_eq_some, h]` makes no progress.
- **Compiled cost of `play`.** Write lists are built once per move (strict evaluation), so a
  square read after `n` plies walks `O(n)` closures; the process log's 32-ply measurement agrees.
- **Kingless sides, two kings, king capture.** Every place the file meets them is stated (L9.4–L9.8,
  `KingAttacked`'s docstring, design choice 11) and none of it relies on `WellFormed`.
- **Revocation by squares versus DESIGN's original rule**: differ only on rights not backed by
  king and rook at home, or after a king capture on its home square; neither permits a castling
  FIDE forbids.
- **`Reaches` ignores the target's contents**: correct for 3.9 (defended pieces), now tested
  (`defendedPos`).

---

## 5. Summary of recommendations

| ID | Priority | When | Recommendation |
|---|---|---|---|
| C1 | high | before `MoveGen` | Rules as Prop-valued structures, one documented field per clause; existing patterns keep working. |
| C2 | high | before calling `Rules` final | Prove L4.11; likely needs no one-king hypothesis (edge-square argument plus `reaches_congr`). |
| C3 | medium-high | with M1, R3, before certificates | Faster proved-equal `Decidable` instances (ray walk: about 3×); a candidate-cover lemma for kernel "no legal move". |
| C4 | medium | now (owner) | Record the en passant convention as a decision; plan `Position.normalize` for certificate keys. |
| C5 | medium | before `MoveGen` | Rename `StepMove` → `PieceMove`; write the namespace rule down; move helpers to Basic/Position; fix Position's false `CastlingRights` docstring. |
| C6 | medium-low | with `Game` | State in DESIGN that downstream code applies `play` only to legal moves. |
| C7 | low | next DESIGN edit | Remove the false en passant claim, fix FIDE numbering, `native_decide` remark, `IsCapture` form; reorder spec §11. |
| C8 | low | now | Check in the docstring-sync script. |
| C9 | low | Stage 5 | State the fast-layer refinement per step of `play`, and against `attacked_iff`. |
