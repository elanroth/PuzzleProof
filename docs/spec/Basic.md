# Specification of `Chess.Basic`

Roles: English specification writer (Round 1), translator (Rounds 2 and 3), refiner (Round 4).
Date: 2026-11-01.
Status: Round 4, matched to `Chess/Basic.lean`, which builds with every lemma proved (see
`docs/process/Basic.md`).

File: `Chess/Basic.lean`. Depends on: nothing (core Lean 4.28 only, no `Std` needed).
Refines DESIGN §4.1, §4.2 and §8.1. Theorem targets: **R1**, **R2** (THEOREMS §2), plus the geometric
lemmas that R3, R5, R6 and M1 will need, stated here once so that `Rules`, `MoveGen` and
`Invariants` never redo square arithmetic.

## 0. How to read this document

- Each definition has an ID (`D3.2`), its Lean name and type, and a **docstring** sentence in
  quotation marks. The Lean docstring is that sentence, word for word, so the English and the Lean
  can be compared by eye (DESIGN Principle 1).
- Each lemma has an ID (`B3.4`), an English statement, the Lean statement, and a tag:
  - **[core]**: later modules depend on it; proved in this file.
  - **[sanity]**: checks that the definition says what the English says (FIDE or folklore); proved,
    usually by `decide`.
  - **[later]**: wanted by Stage 2 proofs; proved here because it turned out cheap.
- The Lean docstring of a lemma is its English column, word for word, when the table cell holds
  that lemma alone. A cell that groups several lemmas gives one sentence for the group, and each
  lemma's docstring is the part of that sentence about it, reworded to stand alone (B1.1: "The
  opponent of White is Black." and "The opponent of Black is White.").
- Lemma tables are in **proof order**, which is also the order in the Lean file. IDs are stable from
  Round 1; lemmas added later carry a letter suffix (`B5.10a`), so IDs are not always consecutive.
- **Binding rule.** Every name a docstring mentions is bound in the signature before the colon.
  A definition by cases is written with `match` on that name
  (`def Color.other (c : Color) : Color := match c with …`), never with an anonymous argument after
  the colon.
- Implicit variables are not automatic (`autoImplicit = false`). Each section of the Lean file opens
  with `variable` declarations from the list of letters below, as needed.
- Letters:
  - `s t u v` squares; `x y` coordinates (`Fin 8`); `c c'` colours; `d d'` directions; `w w'` wings.
  - `k k'` kinds; `pk pk'` promotion choices; `o` an optional promotion choice; `pc` a piece (not
    `p` or `q`, which THEOREMS reserves for positions).
  - `i j n m` step counts (`Nat`); `df dr df' dr'` file and rank differences (`Int`); `δ` a single
    coordinate step (`Int`); `jmp` a knight jump (a pair of `Int`s).
- Casts: `(x : Int)` for `x : Fin 8` means `((x.val : Nat) : Int)`; Lean elaborates it as `↑↑x`.
- `%` on `Int` is `Int.emod`, so `(-1) % 2 = 1`; `omega` understands it.
- Namespace: everything lives in `namespace Chess`. Names below are given without the `Chess.`
  prefix.
- Rules are cited from the FIDE Laws of Chess, effective 1 January 2023 (handbook E012023),
  checked against the handbook on 2026-11-01: colours of the pieces 2.2, light and dark squares 2.1,
  bishop 3.2, rook 3.3, queen 3.4, knight 3.6, pawn 3.7.1 (one step), 3.7.2 (double step), 3.7.3
  (capture), 3.7.3.1–3.7.3.2 (en passant), 3.7.3.3 (promotion), king 3.8.1 (adjoining square), 3.8.2
  (castling), 3.8.2.1 (right to castle lost), 3.8.2.2 (castling prevented temporarily).
- `@[simp]` is written on every lemma that carries it; a lemma without it in its table cell does not
  carry it.

## 1. Section "Colours" (first in the file)

This section is first so that a reader of `Chess.Game`, which needs only `Color`, needs only this
section (DESIGN §8). `Basic` has no dependencies, so importing it is cheap whatever its length. The
section mentions nothing else from the file except the two quantifier helpers of D1.0, which sit
just above it.

**D1.0 Quantifier helpers** (their own short section, "Decidable quantifiers from a complete
list", before "Colours").
```lean
def decidableForallOfMemAll {α : Type} (all : List α) (mem_all : ∀ a, a ∈ all)
    (P : α → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a ∈ all, P a) ⟨fun h a => h a (mem_all a), fun h a _ => h a⟩
```
and `decidableExistsOfMemAll` the same with `∃`.
Docstrings: "`∀ a, P a` is decided by checking `P` on every entry of `all`, a list that contains
every value (`mem_all`)." and "`∃ a, P a` is decided by searching the entries of `all`, a list
that contains every value (`mem_all`)."
They are plain `def`s, not instances: each enumeration chooses to use them (D1.4). `decide` in a
downstream module unfolds them (checked: `∀ d : Direction, ∀ c : Color, …` and `∃ w : Wing, …` by
plain `decide`).

**D1.1 `Color : Type`.** `inductive Color | white | black`, `deriving DecidableEq, Repr, Inhabited`.
Docstring: "The colour of a player and of that player's pieces: White or Black (FIDE 2.2)."

**D1.2 `Color.other (c : Color) : Color`.** `match c with | .white => .black | .black => .white`.
Docstring: "The opponent of colour `c`."

**D1.3 `Color.all : List Color`.** `[.white, .black]`.
Docstring: "Both colours, White first."
Its `mem_all` and `all_nodup` (B1.6) come immediately after it, before the instances of D1.4.

**D1.4 Decidable quantifiers.** Two instances, named `Color.decidableForall` and
`Color.decidableExists`:
`instance (priority := low) (P : Color → Prop) [DecidablePred P] : Decidable (∀ c, P c)` and the
same for `∃ c, P c`. **Every whole-type quantifier instance in this file (D1.4, D2.7, D3.6) has
`priority := low`**, so that a bounded quantifier `∀ c ∈ l, P c` (which is `∀ c, c ∈ l → P c`)
is decided by core's `List.decidableBAll` over `l`, not by sweeping the whole type (review C1;
two tests in §11 check the choice for `Square`).
Each is one line: `decidableForallOfMemAll Color.all mem_all P` (respectively
`decidableExistsOfMemAll Color.all mem_all P`), which decides the quantifier over the list
`Color.all`.
Docstrings: "`∀` over colours is decided by checking both colours in `Color.all`." and "`∃` over
colours is decided by searching both colours in `Color.all`."
`Kind`, `PromoKind`, `Direction` and `Wing` get the same two instances by the same pattern, each
placed right after that type's `all`, `mem_all` and `all_nodup`, with these docstrings:
- "`∀` over kinds is decided by checking the six kinds in `Kind.all`." and "`∃` over kinds is
  decided by searching the six kinds in `Kind.all`."
- "`∀` over promotion choices is decided by checking the four choices in `PromoKind.all`." and
  "`∃` over promotion choices is decided by searching the four choices in `PromoKind.all`."
- "`∀` over directions is decided by checking the eight directions in `Direction.all`." and "`∃`
  over directions is decided by searching the eight directions in `Direction.all`."
- "`∀` over wings is decided by checking both wings in `Wing.all`." and "`∃` over wings is
  decided by searching both wings in `Wing.all`."

`Piece` (D2.7) and `Square` (D3.5)
do not use this pattern.

Derived `Inhabited` defaults are the first constructor (`white`, `pawn`, `knight`, `north`,
`kingside`; for `Square` it is a1, for `Piece` a white pawn). No proof uses them.

Lemmas:

| ID | English | Lean | Tag |
|---|---|---|---|
| B1.6 | (R2) Every colour is listed, once. | `theorem Color.mem_all (c : Color) : c ∈ Color.all` and `theorem Color.all_nodup : Color.all.Nodup` | core |
| B1.1 | The opponent of White is Black, and of Black is White. | `@[simp] theorem Color.other_white : Color.white.other = .black` and `@[simp] theorem Color.other_black : Color.black.other = .white` | core |
| B1.2 | The opponent's opponent is the colour itself. | `@[simp] theorem Color.other_other (c : Color) : c.other.other = c` | core |
| B1.3 | No colour is its own opponent. | `@[simp] theorem Color.other_ne_self (c : Color) : c.other ≠ c` and `@[simp] theorem Color.self_ne_other (c : Color) : c ≠ c.other` | core |
| B1.4 | Two colours with the same opponent are equal. | `@[simp] theorem Color.other_inj {c c' : Color} : c.other = c'.other ↔ c = c'` | core |
| B1.5 | `c` is the opponent of `c'` exactly when it differs from `c'`, since there are only two colours. | `theorem Color.eq_other_iff_ne {c c' : Color} : c = c'.other ↔ c ≠ c'` | core |

Proofs: `mem_all` by `cases c <;> decide` (`rfl` cannot prove `∈`); B1.1 and B1.2 by `rfl` and
`cases c <;> rfl`; B1.3–B1.5 by `cases c <;> decide` or `cases c <;> cases c' <;> decide`;
`all_nodup` by `decide`.

## 2. Section "Kinds, promotion choices, pieces"

**D2.1 `Kind : Type`.** `inductive Kind | pawn | knight | bishop | rook | queen | king`,
`deriving DecidableEq, Repr, Inhabited`.
Docstring: "The kind of a piece, without its colour (FIDE 2.2)."

**D2.2 `Kind.all : List Kind`.** `[.pawn, .knight, .bishop, .rook, .queen, .king]`.
Docstring: "All six kinds, in the order pawn, knight, bishop, rook, queen, king."
Followed by `Kind.mem_all`, `Kind.all_nodup` and the D1.4 instances.

**D2.3 `PromoKind : Type`.** `inductive PromoKind | knight | bishop | rook | queen`,
`deriving DecidableEq, Repr, Inhabited`.
Docstring: "What a pawn may be promoted to: a knight, bishop, rook or queen (FIDE 3.7.3.3)."

**D2.4 `PromoKind.toKind (pk : PromoKind) : Kind`.** `match pk with`, each constructor to the
`Kind` constructor of the same name.
Docstring: "The kind of piece that promotion choice `pk` produces."

**D2.5 `PromoKind.all : List PromoKind`.** `[.knight, .bishop, .rook, .queen]`.
Docstring: "All four promotion choices." (This is the order in which the generator lists
promotions; nothing depends on it.) Followed by `PromoKind.mem_all`, `PromoKind.all_nodup` and the
D1.4 instances.

**D2.6 `Piece : Type`.** `structure Piece where color : Color; kind : Kind`,
`deriving DecidableEq, Repr, Inhabited`. Field order is colour, then kind, so a literal reads
`⟨.white, .king⟩`. The fields have docstrings "The colour of the piece." and "The kind of the
piece."
Docstring: "A piece: a colour and a kind, for example a white knight."

**D2.7 `Piece.all : List Piece`.** `Color.all.flatMap fun c => Kind.all.map (Piece.mk c)`.
Docstring: "All twelve pieces, the white ones first."
Its `Decidable ∀`/`∃` instances go through the two component quantifiers instead of the list:
`decidable_of_iff (∀ c k, P ⟨c, k⟩) …` (with `priority := low`, see D1.4), with docstrings "`∀` over pieces is decided through the
colour and kind quantifiers, not a list." and "`∃` over pieces is decided through the colour and
kind quantifiers, not a list." (`Chess.Position` uses this to
prove the round trip of its piece code table by `decide`.)

**D2.8 `Piece.promote (pc : Piece) (o : Option PromoKind) : Piece`.**
```lean
def Piece.promote (pc : Piece) (o : Option PromoKind) : Piece :=
  match o with
  | none    => pc
  | some pk => ⟨pc.color, pk.toKind⟩
```
Docstring: "The piece that `pc` becomes after a move with promotion choice `o`: `pc` itself if `o`
is `none`, and the piece of `pc`'s colour and of kind `pk.toKind` if `o` is `some pk`."
It is total and makes no claim that `pc` is a pawn; whether a promotion is allowed is a rule in
`Chess.Rules` (the promotion rule, DESIGN §5.4). `play` uses it as
`(p.board m.src).map (·.promote m.promo)`.

Lemmas:

| ID | English | Lean | Tag |
|---|---|---|---|
| B2.1 | (R2) Every kind, promotion choice and piece is listed, once. | `Kind.mem_all`, `Kind.all_nodup`, `PromoKind.mem_all`, `PromoKind.all_nodup`, `Piece.mem_all`, `Piece.all_nodup`, each of the shape of B1.6 | core |
| B2.2 | Different promotion choices give different kinds. | `@[simp] theorem PromoKind.toKind_inj {pk pk' : PromoKind} : pk.toKind = pk'.toKind ↔ pk = pk'` | core |
| B2.3 | A promotion never produces a pawn or a king (FIDE 3.7.3.3). | `@[simp] theorem PromoKind.toKind_ne_pawn (pk : PromoKind) : pk.toKind ≠ .pawn` and `@[simp] theorem PromoKind.toKind_ne_king (pk : PromoKind) : pk.toKind ≠ .king` | sanity |
| B2.4 | Without a promotion choice the piece is unchanged. | `@[simp] theorem Piece.promote_none (pc : Piece) : pc.promote none = pc` | core |
| B2.5 | With choice `pk` the piece keeps its colour and takes kind `pk.toKind`. | `@[simp] theorem Piece.promote_some (pc : Piece) (pk : PromoKind) : pc.promote (some pk) = ⟨pc.color, pk.toKind⟩` | core |
| B2.6 | Promotion never changes colour. | `@[simp] theorem Piece.color_promote (pc : Piece) (o : Option PromoKind) : (pc.promote o).color = pc.color` | core |

Proofs: `cases`, `rfl`, `decide`. `Piece.mem_all` is the term
`List.mem_flatMap.mpr ⟨pc.color, pc.color.mem_all, List.mem_map.mpr ⟨pc.kind, pc.kind.mem_all, rfl⟩⟩`.

## 3. Section "Squares"

**D3.1 `Square : Type`.**
```lean
@[ext] structure Square where
  file : Fin 8
  rank : Fin 8
deriving DecidableEq, Repr, Inhabited
```
Docstring: "A square of the board, given by its file (0 is the a-file, 7 the h-file) and its rank
(0 is rank 1, White's back rank; 7 is rank 8)." So a1 is `⟨0, 0⟩`, e4 is `⟨4, 3⟩` and h8 is
`⟨7, 7⟩`. Field docstrings: "The file: 0 is the a-file, 7 the h-file." and "The rank: 0 is rank 1,
7 is rank 8." `@[ext]` gives `Square.ext` and `Square.ext_iff : s = t ↔ s.file = t.file ∧ s.rank =
t.rank`. The derived `Inhabited` value is a1.

**D3.2 `Square.index (s : Square) : Fin 64`.** `⟨8 * s.rank.val + s.file.val, by omega⟩` (`omega`
knows the bounds of `Fin.val` by itself).
Docstring: "The number of square `s`, from 0 for a1 to 63 for h8: `8 · rank + file`." This is the
standard little-endian rank-file (LERF) numbering (*representation* §1). It is the only bridge from
squares to numbers; `Chess.Position` reads packed boards through it, and the fast layer will read
bitboards through it.

**D3.3 `Square.ofIndex (i : Fin 64) : Square`.**
`⟨⟨i.val % 8, by omega⟩, ⟨i.val / 8, by omega⟩⟩`.
Docstring: "The square with number `i`: file `i % 8`, rank `i / 8`."

**D3.4 `Square.all : List Square`.** `(List.finRange 64).map Square.ofIndex`.
Docstring: "All 64 squares in index order: a1, b1, …, h1, a2, …, h8."
Defining it through `ofIndex` means the order can be read off the definition (entry `i` is
`ofIndex i`), which keeps the generator's move order predictable.

**D3.5 `Square.IsLight (s : Square) : Prop`.** `(s.file.val + s.rank.val) % 2 = 1`.
Docstring: "The square `s` is light: its file and rank add up to an odd number. (a1 is dark.)"
It is a `def`, not an `abbrev`, so that `simp` does not unfold it unasked; unfold it with
`simp only [Square.IsLight]`.
Instance: `instance : DecidablePred Square.IsLight :=
fun s => inferInstanceAs (Decidable ((s.file.val + s.rank.val) % 2 = 1))`, docstring "Whether a
square is light is decided by computing the parity of file plus rank."

**D3.6 Decidable quantifiers over squares.** `Square.decidableForall` and
`Square.decidableExists`, **not** through `Square.all` but through the core `Fin 8` quantifiers:
```lean
instance (priority := low) Square.decidableForall (P : Square → Prop) [DecidablePred P] :
    Decidable (∀ s, P s) :=
  decidable_of_iff (∀ f r : Fin 8, P ⟨f, r⟩) ⟨fun h s => h s.file s.rank, fun h f r => h ⟨f, r⟩⟩
```
and the same with `∃ f r : Fin 8, P ⟨f, r⟩` for `∃ s, P s`. Docstrings: "`∀` over squares is
decided through the core quantifiers over the two `Fin 8` coordinates, not through the 64-element
list (which exceeds `maxRecDepth` under `decide`)." and "`∃` over squares is decided through the
core quantifiers over the two `Fin 8` coordinates." Plain `decide` proves
`∀ s : Square, s.shift .north 8 = none` (a test in §11 checks this on every build; it was also
checked from a downstream module).

(D3.5 and D3.6 swapped places in Round 3: the Lean file defines `IsLight` before opening the
`Square` namespace for instances and lemmas.)

Lemmas:

| ID | English | Lean | Tag |
|---|---|---|---|
| B3.1 | The index is `8 · rank + file`. | `@[simp] theorem Square.val_index (s : Square) : s.index.val = 8 * s.rank.val + s.file.val` (`rfl`) | core |
| B3.2 | The file and rank of square number `i` are `i % 8` and `i / 8`. | `@[simp] theorem Square.val_file_ofIndex (i : Fin 64) : (Square.ofIndex i).file.val = i.val % 8` and `@[simp] theorem Square.val_rank_ofIndex (i : Fin 64) : (Square.ofIndex i).rank.val = i.val / 8` (`rfl`) | core |
| B3.3 | (R1) Numbering a square and taking the square of that number gives the square back. | `@[simp] theorem Square.ofIndex_index (s : Square) : Square.ofIndex s.index = s` | core |
| B3.4 | (R1) Taking the square of a number and numbering it gives the number back. | `@[simp] theorem Square.index_ofIndex (i : Fin 64) : (Square.ofIndex i).index = i` | core |
| B3.5 | Two squares with the same number are equal. | `@[simp] theorem Square.index_inj {s t : Square} : s.index = t.index ↔ s = t` | core |
| B3.6 | (R2) Every square is listed, once; the list of all squares has 64 entries. | `theorem Square.mem_all (s : Square) : s ∈ Square.all`, `theorem Square.all_nodup : Square.all.Nodup`, `@[simp] theorem Square.length_all : Square.all.length = 64` | core |
| B3.7 | The near right-hand corner is light for both players (FIDE 2.1): h1 and a8 are light, a1 is dark. | `theorem Square.isLight_h1 : (Square.mk 7 0).IsLight`, `theorem Square.isLight_a8 : (Square.mk 0 7).IsLight`, `theorem Square.not_isLight_a1 : ¬ (Square.mk 0 0).IsLight` | sanity |
| B3.8 | Exactly 32 squares are light. | `theorem Square.count_isLight : (Square.all.filter fun s => decide s.IsLight).length = 32` | sanity |

Proof notes: B3.3 by `ext <;> simp only [val_file_ofIndex, val_rank_ofIndex, val_index] <;> omega`;
B3.4 by `ext; simp only [val_index, val_file_ofIndex, val_rank_ofIndex]; omega`. Both name the
B3.1 and B3.2 lemmas they use instead of relying on the default simp set. B3.5 from B3.3: `⟨fun h => by rw [← ofIndex_index s, h, ofIndex_index],
congrArg index⟩`. B3.6: `mem_all` is the term `List.mem_map.mpr ⟨s.index, List.mem_finRange _,
ofIndex_index s⟩`; `all_nodup` and B3.8 by `decide +kernel`; `length_all` by `simp only [Square.all, List.length_map, List.length_finRange]`.
Core 4.28 has **no** `List.nodup_finRange` and no `List.Nodup.map`, so do not plan a structural
proof of `all_nodup` around them.

## 4. Section "Offsets: the one geometric primitive"

Every leaper move, every slider step and every pawn step in the library is defined from
`Square.offset` (DESIGN §4.2, *representation* §4). No definition in the specification layer
computes one square from another by coordinate arithmetic except through `offset`. The castling
squares are literals, checked against `shift` by B7.4–B7.6.

**D4.1 `Square.addCoord? (x : Fin 8) (δ : Int) : Option (Fin 8)`, private.**
```lean
private def Square.addCoord? (x : Fin 8) (δ : Int) : Option (Fin 8) :=
  if h : 0 ≤ (x : Int) + δ ∧ (x : Int) + δ < 8 then some ⟨((x : Int) + δ).toNat, by omega⟩
  else none
```
Docstring: "The coordinate `δ` steps from the coordinate `x`, if it is still between 0 and 7."
A helper for D4.2 only. It is `private`, and so are its two lemmas (B4.1 and its `none`
counterpart), so no other module can name it; the interface of offsets is B4.2 alone. `decide` in
other modules still evaluates `offset` through it (checked).

**D4.2 `Square.offset (s : Square) (df dr : Int) : Option Square`.**
```lean
def Square.offset (s : Square) (df dr : Int) : Option Square :=
  match Square.addCoord? s.file df, Square.addCoord? s.rank dr with
  | some f, some r => some ⟨f, r⟩
  | _, _ => none
```
Docstring: "The square `df` files and `dr` ranks away from `s`, or `none` if that is off the board.
Positive `df` is towards the h-file, positive `dr` towards rank 8."
The square comes first so that `s.offset df dr` reads left to right (§9 item 9; DESIGN §4.2 and
THEOREMS R3 now use the same order).
B4.2 below is the interface: every later proof rewrites with it and never unfolds the `match`.
The same holds one level up: downstream modules use the shift lemmas B5.8–B5.17 and never unfold
`shift`. Products such as `i * d.df` are opaque atoms to `omega`, so every lemma about them costs an
eight-way case split on the direction; that cost is paid once, inside this file.

Lemmas:

| ID | English | Lean | Tag |
|---|---|---|---|
| B4.1 | Adding `δ` to `x` gives `y` exactly when `y = x + δ` as integers; it leaves the board exactly when `x + δ` is not in 0..7. | `private theorem Square.addCoord?_eq_some_iff {x y : Fin 8} {δ : Int} : addCoord? x δ = some y ↔ (y : Int) = x + δ` and `private theorem Square.addCoord?_eq_none_iff {x : Fin 8} {δ : Int} : addCoord? x δ = none ↔ ¬ (0 ≤ (x : Int) + δ ∧ (x : Int) + δ < 8)` | core (private) |
| B4.2 | **The offset of `s` by `(df, dr)` is `t` exactly when `t`'s file is `s`'s file plus `df` and `t`'s rank is `s`'s rank plus `dr`.** Other proofs use this lemma instead of unfolding `offset`. | `theorem Square.offset_eq_some_iff : s.offset df dr = some t ↔ (t.file : Int) = s.file + df ∧ (t.rank : Int) = s.rank + dr` | core |
| B4.3 | The offset is on the board exactly when both new coordinates lie in 0..7. | `theorem Square.isSome_offset_iff : (s.offset df dr).isSome ↔ 0 ≤ (s.file : Int) + df ∧ (s.file : Int) + df < 8 ∧ 0 ≤ (s.rank : Int) + dr ∧ (s.rank : Int) + dr < 8` | core |
| B4.4 | Offsetting by nothing stays put. | `@[simp] theorem Square.offset_zero (s : Square) : s.offset 0 0 = some s` | core |
| B4.5 | Two offsets in a row are one offset by the sum, provided the first stays on the board. | `theorem Square.offset_offset (h : s.offset df dr = some t) : t.offset df' dr' = s.offset (df + df') (dr + dr')` | core |
| B4.6 | Offsets can be undone: `t` is `(df, dr)` from `s` exactly when `s` is `(−df, −dr)` from `t`. | `theorem Square.offset_eq_some_iff_neg : s.offset df dr = some t ↔ t.offset (-df) (-dr) = some s` | core |
| B4.7 | A nonzero offset never returns the same square. | `theorem Square.offset_ne_self (hd : df ≠ 0 ∨ dr ≠ 0) (h : s.offset df dr = some t) : t ≠ s` | core |
| B4.8 | Two offsets from the same square that reach the same target have the same steps; two squares that reach the same target by the same offset are equal. | `theorem Square.steps_eq_of_offset_eq (h : s.offset df dr = some t) (h' : s.offset df' dr' = some t) : df = df' ∧ dr = dr'` and `theorem Square.eq_of_offset_eq (h : s.offset df dr = some t) (h' : u.offset df dr = some t) : s = u` | later |
| B4.8a | An offset with no file step stays on the file. | `theorem Square.file_eq_of_offset_zero (h : s.offset 0 dr = some t) : s.file = t.file` | core |
| B4.9 | An offset by `(df, dr)` keeps the square's colour exactly when `df + dr` is even. (Here `%` is `Int.emod`, so `(-1) % 2 = 1`.) | `theorem Square.isLight_offset_iff (h : s.offset df dr = some t) : (t.IsLight ↔ s.IsLight) ↔ (df + dr) % 2 = 0` | core |

Proof notes.
- B4.1: `unfold addCoord?; split <;> simp [Fin.ext_iff] <;> omega` for `some`, and
  `unfold addCoord?; split <;> simp_all` for `none`.
- B4.2: `unfold offset`, then `cases hf : addCoord? s.file df <;> cases hr : addCoord? s.rank dr`,
  then `simp_all [B4.1, Square.ext_iff, Fin.ext_iff] <;> omega`.
- B4.3 is not a pure rewrite. Forwards: take the witness from `Option.isSome_iff_exists`, apply
  B4.2, then `omega`. Backwards: build the square `⟨(s.file + df).toNat, (s.rank + dr).toNat⟩`,
  then B4.2, `dsimp only` (to reduce the structure projections of the witness) and `omega`.
- **Equal `Option Square`s.** To prove two offsets equal (B4.5, and later B5.10a), use
  `Option.ext fun u => by rw [offset_eq_some_iff, offset_eq_some_iff]; omega`, with B4.2 already
  applied to the hypothesis. This is the one pattern for equations between `Option Square`s.
- Every other lemma of this section: rewrite with B4.2, unfold `IsLight` where needed, then
  `omega`.

B4.9 is the content of R5's bishop half at the level of squares: Rules' bishop proof reduces to
"the bishop's offset is `(i·df, i·dr)` with `df + dr` even" (B5.17, proved from B4.9). The knight
half is B5.23, proved directly from B5.21 and B4.2, not from B4.9.

## 5. Section "Directions, shifts, rays, knight jumps"

**D5.1 `Direction : Type`.**
`inductive Direction | north | east | south | west | northEast | southEast | southWest | northWest`,
`deriving DecidableEq, Repr, Inhabited`.
Docstring: "One of the eight compass directions on the board. North is towards rank 8 (up the
board from White's side), east is towards the h-file."
Orthogonal directions first, then diagonal ones, each group clockwise, starting from the direction
nearest north (north; northEast).

**D5.2 `Direction.df (d : Direction) : Int` and `Direction.dr (d : Direction) : Int`.** By
`match d with`:

| `d` | `north` | `east` | `south` | `west` | `northEast` | `southEast` | `southWest` | `northWest` |
|---|---|---|---|---|---|---|---|---|
| `d.df` | 0 | 1 | 0 | −1 | 1 | 1 | −1 | −1 |
| `d.dr` | 1 | 0 | −1 | 0 | 1 | −1 | −1 | 1 |

Docstrings: "The file step of direction `d`: +1 for the three directions with an eastward component
(east, northEast, southEast), −1 for the three with a westward one, 0 for north and south." and
"The rank step of direction `d`: +1 for the three directions with a northward component (north,
northEast, northWest), −1 for the three with a southward one, 0 for east and west."

**D5.3 `Direction.opposite (d : Direction) : Direction`.** North ↔ south, east ↔ west, northEast ↔
southWest, southEast ↔ northWest (eight `match` arms).
Docstring: "The direction pointing the opposite way to `d`."

**D5.4 Named lists of directions.**
- `Direction.orthogonals : List Direction := [.north, .east, .south, .west]`.
  Docstring: "The four directions along a file or a rank: those a rook moves in (FIDE 3.3)."
- `Direction.diagonals : List Direction := [.northEast, .southEast, .southWest, .northWest]`.
  Docstring: "The four diagonal directions: those a bishop moves in (FIDE 3.2)."
- `Direction.all : List Direction := Direction.orthogonals ++ Direction.diagonals`.
  Docstring: "All eight directions: those a queen moves in, and those a king steps in (FIDE 3.4,
  3.8.1)."
  Followed by `Direction.mem_all`, `Direction.all_nodup` and the D1.4 instances.

**D5.5 `Kind.slideDirections (k : Kind) : List Direction`.**
```lean
def Kind.slideDirections (k : Kind) : List Direction :=
  match k with
  | .bishop => Direction.diagonals
  | .rook   => Direction.orthogonals
  | .queen  => Direction.all
  | .pawn | .knight | .king => []
```
Docstring: "The directions along which a piece of kind `k` moves any number of squares without
passing over another piece (FIDE 3.2–3.4): none for pawns, knights and kings." The empty list for
non-sliders is a true statement (a knight slides in no direction), not a sentinel. The three
non-sliders are listed explicitly, not by `_`, so a reader sees all six kinds. `Chess.Rules` states
the slider clause of `Reaches` as `∃ d ∈ k.slideDirections, …`, so the three sliders share one
clause.

**D5.6 `Square.shift (s : Square) (d : Direction) (i : Nat) : Option Square`.**
`s.offset ((i : Int) * d.df) ((i : Int) * d.dr)`.
Docstring: "The square `i` steps from `s` in direction `d`, or `none` if that is off the board."
This is the **index form** the specification of sliders uses (DESIGN §5.2): "`t` is `i ≥ 1` steps
from `s` in direction `d`, and the squares 1, …, `i − 1` steps away are empty (none when `i = 1`)".

**D5.7 `Square.walk (s : Square) (d : Direction) (n : Nat) : List Square`.**
```lean
def Square.walk (s : Square) (d : Direction) (n : Nat) : List Square :=
  match n with
  | 0 => []
  | m + 1 =>
    match s.shift d 1 with
    | none   => []
    | some t => t :: t.walk d m
```
Docstring: "The squares met by stepping from `s` in direction `d` at most `n` times, nearest first,
stopping at the edge of the board; `s` itself is not included."
Structural recursion on the fuel `n` (*lean-eng* §7: no well-founded recursion in anything
`decide` must evaluate). The predecessor is named `m`, not `n`, so the docstring's `n` is never
shadowed.

**D5.8 `Square.ray (s : Square) (d : Direction) : List Square`.** `s.walk d 7`.
Docstring: "The squares met stepping from `s` in direction `d`, up to and including the last square
on the board, nearest first, `s` excluded; empty if `s` is on that edge."
The fuel 7 suffices because eight or more steps in any direction leave the board (B5.10). This is
the form the **generator** uses (DESIGN §5.7); B5.18 and B5.19 (M1 `mem_ray_iff`) link it to the
index form.

**D5.9 `knightJumps : List (Int × Int)`.**
`[(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]` (clockwise from
"one file right, two ranks up").
Docstring: "The eight (file, rank) offsets of a knight's move: two squares along a file or rank and
one across (FIDE 3.6)." Pairs, not a structure: they are only ever passed to `Square.offset` as
`s.offset jmp.1 jmp.2`. It is deliberately at top level (`Chess.knightJumps`), not
`Square.knightJumps`: it is a list of offsets, not a function of a square.

Lemmas about directions:

| ID | English | Lean | Tag |
|---|---|---|---|
| B5.1 | (R2) Every direction is listed in `all`, once. | `theorem Direction.mem_all (d : Direction) : d ∈ Direction.all`, `theorem Direction.all_nodup : Direction.all.Nodup` | core |
| B5.2 | The opposite of the opposite is the direction itself; the opposite negates both steps. | `@[simp] theorem Direction.opposite_opposite (d : Direction) : d.opposite.opposite = d`, `@[simp] theorem Direction.df_opposite (d : Direction) : d.opposite.df = -d.df`, `@[simp] theorem Direction.dr_opposite (d : Direction) : d.opposite.dr = -d.dr` | core |
| B5.3 | A direction is determined by its two steps. | `theorem Direction.ext_iff_steps : d = d' ↔ d.df = d'.df ∧ d.dr = d'.dr` | core |
| B5.4 | Each step is −1, 0 or 1, and at least one is nonzero. | `theorem Direction.natAbs_df_le_one (d : Direction) : d.df.natAbs ≤ 1`, `theorem Direction.natAbs_dr_le_one (d : Direction) : d.dr.natAbs ≤ 1`, `theorem Direction.df_ne_zero_or_dr_ne_zero (d : Direction) : d.df ≠ 0 ∨ d.dr ≠ 0` | core |
| B5.5 | Orthogonal directions are those with a zero step; diagonal ones are those with two nonzero steps. | `theorem Direction.mem_orthogonals_iff : d ∈ Direction.orthogonals ↔ d.df = 0 ∨ d.dr = 0` and `theorem Direction.mem_diagonals_iff : d ∈ Direction.diagonals ↔ d.df ≠ 0 ∧ d.dr ≠ 0` | core |
| B5.6 | A direction's opposite is orthogonal (diagonal) exactly when the direction is. | `theorem Direction.opposite_mem_orthogonals : d.opposite ∈ Direction.orthogonals ↔ d ∈ Direction.orthogonals` and `theorem Direction.opposite_mem_diagonals : d.opposite ∈ Direction.diagonals ↔ d ∈ Direction.diagonals` | later |
| B5.6a | Two directions along a rank (neither changes rank) are equal or opposite. | `theorem Direction.eq_or_eq_opposite_of_dr_eq_zero (hd : d.dr = 0) (hd' : d'.dr = 0) : d' = d ∨ d' = d.opposite` | core |
| B5.7 | A queen slides in exactly the directions of a rook and of a bishop (FIDE 3.4). | `theorem Kind.mem_slideDirections_queen {d : Direction} : d ∈ Kind.queen.slideDirections ↔ d ∈ Kind.rook.slideDirections ∨ d ∈ Kind.bishop.slideDirections` | sanity |
| B5.7a | A piece slides in a direction exactly when it slides in the opposite one. | `theorem Kind.opposite_mem_slideDirections {k : Kind} {d : Direction} : d.opposite ∈ k.slideDirections ↔ d ∈ k.slideDirections` | core |

Proofs: `cases d <;> rfl` or `cases d <;> decide` (with `cases d'` for B5.3, `cases k` for B5.7a;
B5.6a by `revert hd hd'; cases d <;> cases d' <;> decide`). B5.6a was added in the L4.11 round
(2026-11-02) for Rules' castling lemma: a line through a square of the home rank that runs along
that rank runs along the wing's direction or against it.
B5.7a is what R3's `reaches_symm` needs for the slider clause: without it that proof would split on
the kind to reach B5.6.

Lemmas about shifts (they are what makes R3 "plain arithmetic", as DESIGN §5.2 promises). Table
order is proof order:

| ID | English | Lean | Tag |
|---|---|---|---|
| B5.8 | Zero steps stay put; one step is the offset by the direction's steps. | `@[simp] theorem Square.shift_zero : s.shift d 0 = some s` and `theorem Square.shift_one : s.shift d 1 = s.offset d.df d.dr` | core |
| B5.9 | `t` is `i` steps from `s` in direction `d` exactly when the coordinates differ by `i` times the steps. | `theorem Square.shift_eq_some_iff : s.shift d i = some t ↔ (t.file : Int) = s.file + i * d.df ∧ (t.rank : Int) = s.rank + i * d.dr` | core |
| B5.9a | The shift is on the board exactly when both new coordinates lie in 0..7. | `theorem Square.isSome_shift_iff : (s.shift d i).isSome ↔ 0 ≤ (s.file : Int) + i * d.df ∧ (s.file : Int) + i * d.df < 8 ∧ 0 ≤ (s.rank : Int) + i * d.dr ∧ (s.rank : Int) + i * d.dr < 8` | core |
| B5.10 | Eight or more steps in any direction leave the board. | `theorem Square.shift_eq_none_of_eight_le (h : 8 ≤ i) : s.shift d i = none` | core |
| B5.10a | Shifts compose: if `t` is `i` steps from `s`, then `j` steps from `t` is `i + j` steps from `s`. | `theorem Square.shift_add (h : s.shift d i = some t) : t.shift d j = s.shift d (i + j)` | core |
| B5.12 | If the square `i` steps away is on the board, so is every square `j ≤ i` steps away (DESIGN §5.2: a square between two on-board squares is on the board). | `theorem Square.isSome_shift_of_le (hji : j ≤ i) (h : (s.shift d i).isSome) : (s.shift d j).isSome` | core |
| B5.12a | Once off the board, further steps stay off. | `theorem Square.shift_eq_none_of_le (hji : j ≤ i) (h : s.shift d j = none) : s.shift d i = none` | core |
| B5.11 | One more step is the next step from where `i` steps led. | `theorem Square.shift_succ : s.shift d (i + 1) = (s.shift d i).bind (·.shift d 1)` | core |
| B5.13 | **Symmetry:** `t` is `i` steps from `s` in direction `d` exactly when `s` is `i` steps from `t` in the opposite direction. | `theorem Square.shift_eq_some_iff_opposite : s.shift d i = some t ↔ t.shift d.opposite i = some s` | core |
| B5.14 | **The in-between squares match up:** if `t` is `i` steps from `s`, then for `j ≤ i` the square `j` steps from `s` is the square `i − j` steps back from `t`. | `theorem Square.shift_eq_shift_opposite (h : s.shift d i = some t) (hji : j ≤ i) : s.shift d j = t.shift d.opposite (i - j)` | core |
| B5.15 | A positive number of steps never returns to the start. | `theorem Square.shift_ne_self (hi : 0 < i) : s.shift d i ≠ some s` | core |
| B5.16 | A square reached from `s` in some direction is reached by one number of steps only, and, for a positive step count, in one direction only. | `theorem Square.steps_eq_of_shift_eq (h : s.shift d i = some t) (h' : s.shift d j = some t) : i = j` and `theorem Square.dir_eq_of_shift_eq (hi : 0 < i) (h : s.shift d i = some t) (h' : s.shift d' j = some t) : d = d' ∧ i = j` | later |
| B5.16a | If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, and `u` is on the first or the last rank, then `d` does not change rank. | `theorem Square.dr_eq_zero_of_between {u : Square} (hj0 : 0 < j) (hj : j < i) (hu : s.shift d j = some u) (ht : s.shift d i = some t) (hr : u.rank = 0 ∨ u.rank = 7) : d.dr = 0` | core |
| B5.16b | If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, and `u` is on the a-file or the h-file, then `d` does not change file. | `theorem Square.df_eq_zero_of_between {u : Square} (hj0 : 0 < j) (hj : j < i) (hu : s.shift d j = some u) (ht : s.shift d i = some t) (hf : u.file = 0 ∨ u.file = 7) : d.df = 0` | core |
| B5.16c | If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, then the square `v` one step from `u` in direction `d'`, which is `d` or its opposite, is `s`, `t`, or `j'` steps from `s` for some `j'` with `0 < j' < i`. | `theorem Square.shift_one_of_between {u v : Square} (hj0 : 0 < j) (hj : j < i) (hu : s.shift d j = some u) (ht : s.shift d i = some t) (hd' : d' = d ∨ d' = d.opposite) (hv : u.shift d' 1 = some v) : v = s ∨ v = t ∨ ∃ j', 0 < j' ∧ j' < i ∧ s.shift d j' = some v` | core |
| B5.17 | A diagonal shift keeps the square's colour. | `theorem Square.isLight_shift_of_mem_diagonals (hd : d ∈ Direction.diagonals) (h : s.shift d i = some t) : t.IsLight ↔ s.IsLight` | core |

Proof notes for shifts.
- B5.9 and B5.9a are B4.2 and B4.3 with `i * d.df` for `df` (the proof is the term
  `offset_eq_some_iff`, resp. `isSome_offset_iff`).
- **Products.** `i * d.df` is a product of two variables, which `omega` treats as an opaque atom.
  So every lemma that needs arithmetic on it first does `cases d <;> simp [Direction.df,
  Direction.dr]`, which turns `↑i * 1`, `↑i * -1`, `↑i * 0` into linear terms, then `omega`. This
  is how B5.10, B5.12, B5.15, B5.16 and B5.17 are proved. The second half of B5.16 needs no `0 < j`: if
  `j = 0` then `t = s`, which `0 < i` and B5.15 rule out, and `omega` sees this by itself.
- B5.10a needs no case split: unfold `shift`, apply B4.5, then rewrite
  `((i + j : Nat) : Int) * df = i * df + j * df` with `Int.natCast_add` and `Int.add_mul`.
- B5.12a is the contrapositive of B5.12. B5.11 then needs no arithmetic: case on `s.shift d i`;
  `some t` is B5.10a with `j = 1`, `none` is B5.12a.
- B5.13 needs no case split either: B5.9 twice, `Direction.df_opposite`, `Direction.dr_opposite`,
  `Int.mul_neg`, then `omega` (the atom `i * d.df` appears on both sides).
- B5.14: B5.12 gives a square `u` that is `j` steps from `s`; then B5.13 for `u` and `t`, and B5.10a
  with `j + (i − j) = i` (`Nat.add_sub_cancel'`).
- B5.16a, B5.16b (added in the L4.11 round, 2026-11-02): turn `hr` (resp. `hf`) into a statement
  about `u.rank.val` (`rcases hr with h | h <;> simp [h] <;> decide`), rewrite `hu` and `ht` with
  B5.9, then `cases d <;> simp [Direction.df, Direction.dr] at hu ht ⊢ <;> omega`, with
  `t.rank.isLt` (resp. `t.file.isLt`) in context: if `d` changed rank, `u` would lie strictly
  between the ranks of `s` and `t`, so neither on rank 0 nor on rank 7. They say that a line
  through an edge square, with that square strictly inside the segment, runs along the edge; a
  corner (both) lies strictly inside no segment.
- B5.16c (same round): for `d' = d`, B5.10a turns `hv` into `s.shift d (j + 1) = some v`, which is
  `t` when `j + 1 = i`; for `d' = d.opposite`, B5.14 with `j - 1 ≤ j` turns it into
  `s.shift d (j - 1) = some v`, which is `s` when `j = 1`. Together with B5.16a it is the geometry
  of Rules' L4.11: the neighbours along a line of a square strictly inside a segment are inside the
  segment or at its ends.
- B5.17: B4.9, then the four diagonal directions one by one; `i * 1 + i * 1` is even.

Lemmas about rays and knight jumps:

| ID | English | Lean | Tag |
|---|---|---|---|
| B5.18a | Entry `i` of `s.walk d n` (counting from 0) is the square `i + 1` steps away, if `i < n`. | `theorem Square.getElem?_walk (s : Square) (d : Direction) (n i : Nat) : (s.walk d n)[i]? = if i < n then s.shift d (i + 1) else none` | later |
| B5.18 | Entry `i` of the ray (counting from 0) is the square `i + 1` steps away. | `theorem Square.getElem?_ray (s : Square) (d : Direction) (i : Nat) : (s.ray d)[i]? = s.shift d (i + 1)` | later |
| B5.19 | `t` is on the ray from `s` in direction `d` exactly when it is a positive number of steps from `s` in that direction (the geometric half of M1). | `theorem Square.mem_ray_iff : t ∈ s.ray d ↔ ∃ i, 0 < i ∧ s.shift d i = some t` | later |
| B5.20 | A ray does not contain its start and has no repeats. | `theorem Square.not_mem_ray_self : s ∉ s.ray d` and `theorem Square.ray_nodup : (s.ray d).Nodup` | later |
| B5.21 | The knight jumps are exactly the offsets whose absolute values are 1 and 2 in some order. | `theorem mem_knightJumps_iff {df dr : Int} : (df, dr) ∈ knightJumps ↔ (df.natAbs = 1 ∧ dr.natAbs = 2) ∨ (df.natAbs = 2 ∧ dr.natAbs = 1)` | sanity |
| B5.22 | The jumps are closed under reversal: a knight can jump back. | `theorem neg_mem_knightJumps {df dr : Int} (h : (df, dr) ∈ knightJumps) : (-df, -dr) ∈ knightJumps` | core |
| B5.24 | There are eight distinct jumps. | `theorem knightJumps_nodup : knightJumps.Nodup` | sanity |
| B5.23 | A knight jump always changes the square's colour. | `theorem Square.isLight_iff_of_mem_knightJumps {s t : Square} {df dr : Int} (hj : (df, dr) ∈ knightJumps) (h : s.offset df dr = some t) : t.IsLight ↔ ¬ s.IsLight` | core |

Proof notes for rays and jumps.
- B5.18a by induction on `n` generalizing `s` and `i`. In the step, case on `s.shift d 1`:
  - `none`: both sides are `none`, by B5.12a.
  - `some t`: for `i = 0` both sides are `some t`; for `i + 1` use the induction hypothesis for `t`
    and B5.10a.
- B5.18: B5.18a with `n = 7`; for `i ≥ 7` the right side is `none` by B5.10.
- B5.19: `List.mem_iff_getElem?` and B5.18; shift the index by one in each direction.
- B5.20: `not_mem_ray_self` from B5.19 and B5.15. `ray_nodup` from `List.pairwise_iff_getElem`,
  `List.getElem?_eq_getElem`, B5.18 and the first half of B5.16 (two entries that are equal are the
  same number of steps away, so have the same index).
- B5.21: `simp only [knightJumps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]`,
  then `omega`. B5.22: rewrite both sides with B5.21, then `omega`.
- B5.23 directly: rewrite `hj` with B5.21 and `h` with B4.2, unfold `IsLight`, then `omega`. Going
  through B4.9 is longer: B4.9 and an odd `df + dr` give `¬ (t.IsLight ↔ s.IsLight)`, and getting
  from there to `t.IsLight ↔ ¬ s.IsLight` needs a decidable (or classical) step. (Core does have
  `not_congr`; it goes the other way and does not help.)

## 6. Section "Colour geometry"

**D6.1 `Color.forward (c : Color) : Int`.** `match c with | .white => 1 | .black => -1`.
Docstring: "The rank step of a pawn of colour `c`: +1 (towards rank 8) for White, −1 for Black
(FIDE 3.7.1)."

**D6.2 `Color.homeRank (c : Color) : Fin 8`.** `match c with | .white => 0 | .black => 7`.
Docstring: "The rank on which the king and rooks of colour `c` start: rank 1 for White, rank 8 for
Black."

**D6.3 `Square.relRank (s : Square) (c : Color) : Fin 8`.**
```lean
def Square.relRank (s : Square) (c : Color) : Fin 8 :=
  match c with
  | .white => s.rank
  | .black => s.rank.rev
```
Docstring: "The rank of `s` counted from colour `c`'s side of the board, 0 being `c`'s home rank."
`Fin.rev` is core's `x ↦ 7 − x` on `Fin 8` (`Fin.val_rev : (x.rev).val = 8 - (x.val + 1)`). A pawn
of colour `c` (relative ranks counted from 0, so relative rank 1 is `c`'s second rank):
- starts on relative rank 1 and double-pushes from it;
- after a double push leaves the en passant target on relative rank 2;
- promotes on relative rank 7;
- captures en passant onto relative rank 5 (DESIGN §4.1).

Ranks 2 and 5 are the same square seen from the two sides: `(Fin.rev 2 : Fin 8) = 5`, so by B6.5
the target of `c`'s double push is on the capturer's (`c.other`'s) relative rank 5. A test checks
this on e3. Call sites read `dst.relRank c = 5`. The square comes first, as for every function on
squares (§9 item 9; DESIGN §4.1 uses the same order).

Lemmas. Every `_other` lemma (B1.1-style `forward_other`, `homeRank_other`, `relRank_other`) is
`@[simp]`: each pushes `other` outwards into `-` or `rev`, which is the normal form.

| ID | English | Lean | Tag |
|---|---|---|---|
| B6.1 | White's pawns go up, Black's go down, and the two directions are opposite. | `@[simp] theorem Color.forward_white : Color.white.forward = 1`, `@[simp] theorem Color.forward_black : Color.black.forward = -1`, `@[simp] theorem Color.forward_other (c : Color) : c.other.forward = -c.forward` | core |
| B6.2 | The pawn direction is a unit: it squares to 1. | `@[simp] theorem Color.forward_mul_forward (c : Color) : c.forward * c.forward = 1` | core |
| B6.2a | A pawn's rank step is not zero; nor is its two-square rank step. | `theorem Color.forward_ne_zero (c : Color) : c.forward ≠ 0` and `theorem Color.two_mul_forward_ne_zero (c : Color) : 2 * c.forward ≠ 0` | core |
| B6.3 | White's home rank is rank 1 and Black's is rank 8; they are mirror images. | `@[simp] theorem Color.homeRank_white : Color.white.homeRank = 0`, `@[simp] theorem Color.homeRank_black : Color.black.homeRank = 7`, `@[simp] theorem Color.homeRank_other (c : Color) : c.other.homeRank = c.homeRank.rev` | core |
| B6.3a | A home rank is the first or the last rank. | `theorem Color.homeRank_eq_zero_or_seven (c : Color) : c.homeRank = 0 ∨ c.homeRank = 7` | core |
| B6.4 | Relative rank is the rank for White and the mirrored rank for Black. | `@[simp] theorem Square.relRank_white (s : Square) : s.relRank .white = s.rank`, `@[simp] theorem Square.relRank_black (s : Square) : s.relRank .black = s.rank.rev` | core |
| B6.5 | Counted from the other side, the relative rank is mirrored. | `@[simp] theorem Square.relRank_other (s : Square) (c : Color) : s.relRank c.other = (s.relRank c).rev` | core |
| B6.6 | Relative rank 0 is the colour's home rank; relative rank 7 is the opponent's home rank (where pawns promote). | `theorem Square.relRank_eq_zero_iff : s.relRank c = 0 ↔ s.rank = c.homeRank` and `theorem Square.relRank_eq_seven_iff : s.relRank c = 7 ↔ s.rank = c.other.homeRank` | core |
| B6.7 | **Any offset by `(df, dr)` changes `c`'s relative rank by `dr · c.forward`.** In particular a pawn step (`dr = c.forward`) raises it by one (B6.2), and a double step by two. | `theorem Square.relRank_of_offset (h : s.offset df dr = some t) (c : Color) : ((t.relRank c).val : Int) = (s.relRank c).val + dr * c.forward` | core |
| B6.7a | An offset by `dr` ranks forward, as `c` sees the board, raises `c`'s relative rank by `dr`. | `theorem Square.relRank_of_offset_forward (h : s.offset df (dr * c.forward) = some t) : ((t.relRank c).val : Int) = (s.relRank c).val + dr` | core |
| B6.8 | Files do not depend on colour: an offset by `(df, dr)` lands on file `s.file + df` whoever moves. | (no separate lemma: B4.2 says it) | — |

Proof notes: B6.1–B6.5 by `cases c <;> rfl` (B6.5 by `cases c <;> simp`, using core's simp lemma
`Fin.rev_rev`). B6.3a by `cases c <;> simp`; it is not `@[simp]`. Rules' castling proofs pass it,
for `c := p.turn`, as the edge-rank hypothesis of B5.16a: `(kingHome c).rank` and the other home
squares' ranks reduce to `c.homeRank` by `rfl` (B7.2). B6.6 by `revert s; cases c <;> decide`:
each case is a statement over all 64 squares, which the D3.6 instance decides. Do **not** call `simp [Fin.ext_iff]` on a goal containing `Fin.rev`
and a `Fin 8` literal: it hits `maxRecDepth` in 4.28. B6.7 by B4.2,
`cases c <;> simp [Fin.val_rev] <;> omega`. B6.7 is the single lemma through which `Rules` and
`Invariants` learn that pawns move forward. B6.7a is B6.7 rewritten with `Int.mul_assoc`, B6.2 and
`Int.mul_one`. It exists so that a double step, written `s.offset 0 (2 * c.forward)`, gives "relative
rank + 2" without each caller repeating `simpa [Int.mul_assoc]`.

## 7. Section "Wings and castling squares"

There are no 64 named square constants (DESIGN §4.2). The squares castling needs are computed
from colour and wing. Their **files** are written as literals once, in a table of four functions on
`Wing` (D7.3); every castling square is the structure literal `⟨file, c.homeRank⟩`. B7.4–B7.7 prove
that these squares are the ones FIDE 3.8.2 describes, so no reader has to trust the literals.

**D7.1 `Wing : Type`.** `inductive Wing | kingside | queenside`,
`deriving DecidableEq, Repr, Inhabited`.
Docstring: "The side of the board a castling goes to: kingside (towards the h-file) or queenside
(towards the a-file)."
`Wing.all : List Wing := [.kingside, .queenside]`, docstring "Both wings, kingside first.", followed
by `Wing.mem_all`, `Wing.all_nodup` and the D1.4 instances.
`Wing` lives here, not in `Chess.Position`, because the castling squares below need it
(DESIGN §4.1 lists it among `Basic`'s finite types).

**D7.2 `Wing.direction (w : Wing) : Direction`.** `match w with | .kingside => .east |
.queenside => .west`.
Docstring: "The direction from the king's home square towards the rook's home square on wing `w`:
east for kingside, west for queenside."

**D7.3 The file table.** Four functions on `Wing`, each by `match w with`:

| function | docstring | kingside | queenside |
|---|---|---|---|
| `Wing.rookFile (w : Wing) : Fin 8` | "The file on which the rook of wing `w` starts: h (7) for kingside, a (0) for queenside." | 7 | 0 |
| `Wing.kingCastleFile (w : Wing) : Fin 8` | "The file on which the king lands when castling to wing `w`: g (6) for kingside, c (2) for queenside." | 6 | 2 |
| `Wing.rookCastleFile (w : Wing) : Fin 8` | "The file on which the rook lands when castling to wing `w`: f (5) for kingside, d (3) for queenside." | 5 | 3 |
| `Wing.betweenFiles (w : Wing) : List (Fin 8)` | "The files strictly between the king's and the rook's home files on wing `w`, nearest the king first: f, g for kingside; d, c, b for queenside." | `[5, 6]` | `[3, 2, 1]` |

**D7.4 `kingHome (c : Color) : Square`.** `⟨4, c.homeRank⟩`.
Docstring: "The square on which the king of colour `c` starts: e1 for White, e8 for Black."

**D7.5 `rookHome (c : Color) (w : Wing) : Square`.** `⟨w.rookFile, c.homeRank⟩`.
Docstring: "The square on which the rook of colour `c` on wing `w` starts: the h-file (kingside) or
a-file (queenside) square of `c`'s home rank."

**D7.6 `kingCastleSquare (c : Color) (w : Wing) : Square`.** `⟨w.kingCastleFile, c.homeRank⟩`.
Docstring: "The square the king of colour `c` lands on when castling to wing `w`: g1 or c1 for
White, g8 or c8 for Black."

**D7.7 `rookCastleSquare (c : Color) (w : Wing) : Square`.** `⟨w.rookCastleFile, c.homeRank⟩`.
Docstring: "The square the king of colour `c` crosses when castling to wing `w`, which is where the
rook lands: the square next to `kingHome c` towards wing `w`; f1 or d1 for White, f8 or d8 for
Black."

**D7.8 `betweenKingAndRook (c : Color) (w : Wing) : List Square`.**
`w.betweenFiles.map fun f => ⟨f, c.homeRank⟩`.
Docstring: "The squares strictly between the king's and the rook's home squares of colour `c` on
wing `w`, nearest the king first. Castling needs them all empty (FIDE 3.8.2.2)."
On the queenside this includes the b-file square, which must be empty but may be attacked; the
square the king *crosses* is `rookCastleSquare c w` alone (DESIGN §5.4).

Lemmas (each by `cases c <;> cases w <;> rfl` or `… <;> decide`, with `cases c'` and `cases w'`
where they occur; the rank lemmas are `rfl` with `c` and `w` variables, because every castling
square is a structure literal):

| ID | English | Lean | Tag |
|---|---|---|---|
| B7.1 | (R2) Both wings are listed, once. | `theorem Wing.mem_all (w : Wing) : w ∈ Wing.all`, `theorem Wing.all_nodup : Wing.all.Nodup` | core |
| B7.2 | All castling squares are on the colour's home rank. | `@[simp] theorem rank_kingHome (c : Color) : (kingHome c).rank = c.homeRank`, `@[simp] theorem rank_rookHome (c : Color) (w : Wing) : (rookHome c w).rank = c.homeRank`, `@[simp] theorem rank_kingCastleSquare (c : Color) (w : Wing) : (kingCastleSquare c w).rank = c.homeRank`, `@[simp] theorem rank_rookCastleSquare (c : Color) (w : Wing) : (rookCastleSquare c w).rank = c.homeRank` (all `rfl`) | core |
| B7.3 | The king starts on the e-file. | `@[simp] theorem file_kingHome (c : Color) : (kingHome c).file = 4` | sanity |
| B7.4 | **FIDE 3.8.2, the king's move:** castling moves the king two squares from its home towards the rook. | `theorem shift_kingHome_two (c : Color) (w : Wing) : (kingHome c).shift w.direction 2 = some (kingCastleSquare c w)` | core |
| B7.5 | **FIDE 3.8.2, the rook's move:** the rook lands on the square the king crosses, one square from the king's home towards the rook. | `theorem shift_kingHome_one (c : Color) (w : Wing) : (kingHome c).shift w.direction 1 = some (rookCastleSquare c w)` | core |
| B7.5a | The king's castling square is not one king step from its home square. | `theorem shift_kingHome_one_ne (c : Color) (w : Wing) (d : Direction) : (kingHome c).shift d 1 ≠ some (kingCastleSquare c w)` | core |
| B7.6 | The rook's home is the last square on the king's ray towards it, and the squares between are the rest of that ray. | `theorem getLast?_ray_kingHome (c : Color) (w : Wing) : ((kingHome c).ray w.direction).getLast? = some (rookHome c w)` and `theorem betweenKingAndRook_eq (c : Color) (w : Wing) : betweenKingAndRook c w = ((kingHome c).ray w.direction).dropLast` | sanity |
| B7.7 | Both squares the king passes through or lands on are between the king and the rook. | `theorem rookCastleSquare_mem_between (c : Color) (w : Wing) : rookCastleSquare c w ∈ betweenKingAndRook c w` and `theorem kingCastleSquare_mem_between (c : Color) (w : Wing) : kingCastleSquare c w ∈ betweenKingAndRook c w` | core |
| B7.8 | The four rook home squares are distinct. | `@[simp] theorem rookHome_inj {c c' : Color} {w w' : Wing} : rookHome c w = rookHome c' w' ↔ c = c' ∧ w = w'` | core |
| B7.9 | No king square used by castling is a rook home square; the king's landing square is neither a king's home nor a rook's landing square; and no rook landing square is a rook home square or a king's home square. | `theorem kingHome_ne_rookHome (c c' : Color) (w : Wing) : kingHome c ≠ rookHome c' w`, `theorem kingCastleSquare_ne_rookHome (c c' : Color) (w w' : Wing) : kingCastleSquare c w ≠ rookHome c' w'`, `theorem kingCastleSquare_ne_kingHome (c c' : Color) (w : Wing) : kingCastleSquare c w ≠ kingHome c'`, `theorem rookCastleSquare_ne_kingCastleSquare (c c' : Color) (w w' : Wing) : rookCastleSquare c w ≠ kingCastleSquare c' w'`, `theorem rookCastleSquare_ne_rookHome (c c' : Color) (w w' : Wing) : rookCastleSquare c w ≠ rookHome c' w'`, `theorem rookCastleSquare_ne_kingHome (c c' : Color) (w : Wing) : rookCastleSquare c w ≠ kingHome c'` | core |
| B7.10 | The king's home square is on its own relative rank 0. | `@[simp] theorem relRank_kingHome (c : Color) : (kingHome c).relRank c = 0` | core |

Why B7.9 is here: DESIGN §5.5 needs two facts about `play`, and each is a fact about these squares
alone, proved once by `decide` (at most 2 × 2 × 2 × 2 cases each).
- "Steps 2 and 3 of `play` never write to `dst`" (`dst` is `kingCastleSquare c w` for a castling):
  `kingCastleSquare_ne_rookHome` (the rook is lifted from a square other than `dst`) and
  `rookCastleSquare_ne_kingCastleSquare` (the rook is put on a square other than `dst`).
- "Step 4 revokes rights only for rook home squares": `kingHome_ne_rookHome` and
  `kingCastleSquare_ne_rookHome` (the king's source and destination are never rook homes).
- `kingCastleSquare_ne_kingHome` (castling moves the king) and `rookCastleSquare_ne_rookHome`
  (castling moves the rook; added in Round 2 for symmetry) complete the picture.
- `rookCastleSquare_ne_kingHome` (the rook lands neither where the king stood) and B7.5a (the king
  does not reach its castling square by a king step) were proved in `Chess.Rules`, the second
  `private`, and moved here in the readability round of 2026-11-02 (Rules review C5), with B4.8a and B6.2a, so that later
  modules can use them.

## 8. Section "Notation"

Trusted (corrected by the library review, 2026-11-01; ChessGame review C1): the FEN and UCI guards
of `Chess.ChessGame` compare against `Square.fileChar`, `Square.rankChar` and `Square.name`, so they
are part of what `fen "…"` and `uci "…"` mean. They also let `#eval`, the `Position` diagram and the
UCI printer name squares. The Lean section heading reads "Notation (trusted: …)".

**D8.1 `Square.fileChar (s : Square) : Char`.** `Char.ofNat ('a'.toNat + s.file.val)`.
Docstring: "The letter of the file of `s`, from `a` to `h`."

**D8.2 `Square.rankChar (s : Square) : Char`.** `Char.ofNat ('1'.toNat + s.rank.val)`.
Docstring: "The digit of the rank of `s`, from `1` to `8`."

**D8.3 `Square.name (s : Square) : String`.** `s!"{s.fileChar}{s.rankChar}"`, and
`instance : ToString Square := ⟨Square.name⟩` with docstring "Squares print as their algebraic
names."
Docstring: "The algebraic name of `s`, such as `e4`."
`Repr Square` stays derived (DESIGN §4.1). Parsing names back is the job of the parsers in
`Chess.ChessGame` (DESIGN §8.6), not of this file.

## 9. Design choices, with reasons

1. **Two `Fin 8` coordinates, not `Fin 64`.** The rules are stated in file and rank differences;
   `Fin 8` makes "on the board" a type, so no rule carries a `< 64` side condition; the kernel cost
   equals `Fin 64` (*lean-eng* §4). `Fin 64` survives as `index`, a proved bijection (R1), used
   only at the packing and bitboard seams.
2. **One primitive, `offset`, characterized by one lemma (B4.2).** Every leaper, slider step and
   pawn step is built from it, and every castling square is proved equal to something built from
   it. Proofs rewrite with B4.2 and finish with `omega`; `addCoord?` is private, so nobody can
   unfold it. This replaces the prototype's biased offsets ("0..4 means −2..2") and its sentinel
   square 64 by `Int` steps and `Option`.
3. **`Int` steps, not `Fin` arithmetic.** `Fin 8` subtraction wraps around; `Int` addition with a
   range check says "off the board" honestly. The wrap-around is exactly the "warping pawn" bug of
   *representation* §4.
4. **Index form for sliders, list form for the generator, both here.** `shift d i` makes R3
   symmetry plain arithmetic (B5.13, B5.14); `ray` is what the generator walks. B5.18 joins them,
   so neither layer has to trust the other.
5. **Directions are an enumeration with steps, not pairs of integers.** "The four rook directions"
   is a named list of four named values (THEOREMS M1, "Forces"), `opposite` is a function, and the
   decidable quantifiers over directions follow the D1.4 pattern. Knight jumps, which are not
   directions, stay pairs.
6. **`Kind.slideDirections` in `Basic`.** It only joins two `Basic` types, and it lets `Reaches`
   state one slider clause for bishop, rook and queen. The queen's moves being the rook's plus the
   bishop's is then a sanity theorem (B5.7), not a third copy of the rule.
7. **Colour-dependent geometry is a function of colour.** `forward`, `homeRank` and `relRank`
   replace every "if White then … else …" in the rules; B6.7 is the only place pawn direction meets
   rank arithmetic. This is what makes R6 (colour flip) a lemma about these three functions rather
   than a case split over the rules.
8. **Castling squares as literals with characterizing theorems.** The files are one table on
   `Wing` (D7.3); `⟨w.kingCastleFile, c.homeRank⟩` is what a chess player recognizes as g1/c1/g8/c8;
   B7.4–B7.6 prove that it is the square FIDE 3.8.2 describes (two squares towards the rook, the
   rook onto the crossed square). Defining the squares through `shift` instead would put `Option`
   into their types. Chess960 is out of scope; it would change these functions' types (the homes
   would depend on the starting position, not on `Color × Wing`), not just their values, and B7.4
   would no longer hold.
9. **Square first in every function on squares** (`s.offset df dr`, `s.shift d i`, `s.relRank c`),
   so that dot notation reads left to right and partial application over the square is never
   needed.
10. **Finite types without `Fintype`.** Each enumeration has `all`, `mem_all`, `all_nodup` and
    `Decidable ∀/∃` instances (R2). Small enumerations go through their list, by the D1.0 helpers;
    `Square` goes through the core `Fin` quantifiers and `Piece` through its two components, so that
    plain `decide` works on statements over all squares or all pieces. The helpers are plain
    functions, not a class `Enumerated α` with generic instances: a class would add an instance
    search to every `decide`, and five types do not need one.
11. **`deriving DecidableEq, Repr, Inhabited`, never `BEq`.** A separately derived `BEq` is not
    `LawfulBEq` (*lean-eng* §6); `==` comes from `DecidableEq`.
12. **`IsLight` is a `Prop` with a decidable instance**, as all predicates in the library are
    (DESIGN Principle 2), and a `def`, so `simp` leaves it folded.

## 10. Not in this module, on purpose

- No board, move, position or castling-rights type (`Chess.Position`).
- No `Reaches`, attack or legality notion (`Chess.Rules`). This file provides only the geometry
  those definitions quote.
- No square parser (`Chess.ChessGame`).
- No bitboards or `BitVec` (Stage 5 fast layer).
- **Deferred to Stage 2 (R6), with its home here.** Not written yet. `Reaches` is stated in
  directions, so R6 needs both a square flip and a direction mirror:
  - `Square.flip s := ⟨s.file, s.rank.rev⟩` ("the square mirrored top to bottom"), with
    `flip_flip`, `relRank_flip : s.flip.relRank c.other = s.relRank c`,
    `index_flip : s.flip.index.val = s.index.val ^^^ 56` (by `decide` over all squares), and
    `kingHome_other : kingHome c.other = (kingHome c).flip` (and the same for the other castling
    squares);
  - `Direction.mirror` ("the direction mirrored top to bottom": north ↔ south, northEast ↔
    southEast, northWest ↔ southWest, east and west fixed), with `mirror_mirror`,
    `df_mirror : d.mirror.df = d.df` and `dr_mirror : d.mirror.dr = -d.dr`;
  - `offset_flip : s.flip.offset df (-dr) = (s.offset df dr).map Square.flip` and
    `shift_flip : s.flip.shift d.mirror i = (s.shift d i).map Square.flip`;
  - closure under mirroring: `d.mirror ∈ k.slideDirections ↔ d ∈ k.slideDirections` and
    `(df, -dr) ∈ knightJumps ↔ (df, dr) ∈ knightJumps`.

## 11. Checklist for the translator

- Module docstring `/-! # Basic … -/` with `## Main definitions` and `## Main statements` listing
  R1 and R2, and `## Implementation notes` summarizing §9 items 1, 2 and 4.
- Section order: Colours; Kinds, promotion choices, pieces; Squares; Offsets; Directions, shifts,
  rays, knight jumps; Colour geometry; Wings and castling squares; Notation; Tests.
- Every `def`, `instance` and `theorem` has the docstring above (one-line companions such as
  `other_black` get the English of their row). Every lemma is proved; nothing is `sorry`.
- `@[simp]` exactly on the lemmas whose cells say so. In particular the `_iff` characterizations
  (B4.2, B4.3, B5.9, B5.9a) are **not** simp lemmas; they are used with `rw`/`simp only [...]` on
  purpose.
- Every proof uses only core tactics (no Mathlib, no `native_decide`). A plain `simp` is used only
  where the default simp set is not what the proof depends on; where a proof needs particular
  lemmas, it names them with `simp only`.
- Tests, as `example`s and `#guard`s at the end of the file, kept in the module (cheap: 1.7 s;
  decision of the test-library round, `docs/process/ChessTest.md` §1):
  `(Square.mk 4 3).index = 28`; `Square.ofIndex 63 = ⟨7, 7⟩`; `(Square.mk 4 0).ray .east =
  [⟨5, 0⟩, ⟨6, 0⟩, ⟨7, 0⟩]`; `(Square.mk 0 0).ray .southWest = []`; `(Square.mk 3 3).ray .northEast`
  has length 4; `(Square.mk 4 6).relRank .black = 1` (e7 is Black's pawn rank);
  `(Square.mk 4 2).relRank .white = 2 ∧ (Square.mk 4 2).relRank .black = 5` (e3, the en passant
  target of e2–e4); `(Square.mk 0 0).offset (-1) 0 = none`; `knightJumps.length = 8`;
  `∀ s : Square, s.shift .north 8 = none` by plain `decide` (D3.6); `∀ s ∈ l, P s` and
`∃ s ∈ l, P s` over `Square` resolve to `List.decidableBAll` / `List.decidableBEx` (by `rfl`, D1.4);
B7.4 for all
  colours and wings by one `decide`; `(Square.mk 4 3).name == "e4"`; `toString (Square.mk 0 7) ==
  "a8"`.
