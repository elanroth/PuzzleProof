# Specification of `Chess.Position`

Role: English specification writer (Round 1); revised by the translator (Rounds 2 and 3) and the
refiner (Round 4).
Date: 2026-11-01.
Status: Round 4. Translated into `Chess/Position.lean`, which builds with every lemma proved; the
English below has been brought into line with the Lean (`docs/process/Position.md`, Rounds 2–4).

File: `Chess/Position.lean`. Depends on: `Chess.Basic` only (core Lean 4.28, no `Std` package
needed: `Std.Format`, used by the display instances, is core's `Init` formatter).
Refines DESIGN §4.3–§4.6 and §8.2. Theorem targets: the foundations of **R4** (`Board.set` and its
lemmas), **R8** (`revoke_le`, `revokeAll_le`, the order on castling rights), **C3** (packed board
literals and `DecidableEq Position`), **R10** and **M7** (`Position.initial`), and the board half of
**R6** (`Board.initial_flip`, a sanity check now).

**R2 is met only in part here, on purpose.** `Move` and `CastlingRights` get the decidability half
of R2 (whole-type `∀` and `∃` instances, D3.2 and D4.7) but no `all` list and no `mem_all` or
`all_nodup`: a list of 20 480 candidate moves would only invite a generator to use it (§3), and a
list of the 16 castling rights has no use (D4.6). R2's full trio belongs to `Color`, `Kind`,
`PromoKind`, `Wing`, `Square` and `Piece`, all in `Basic` (§9 asks THEOREMS to say so).

`Wing` is **not** defined here: it is `Basic` D7.1, together with `kingHome`, `rookHome` and the
other castling squares. This module adds the castling *rights*, which are indexed by `Color` and
`Wing`.

## 0. How to read this document

The conventions of `docs/spec/Basic.md` §0 apply unchanged:

- Each definition has an ID (`D2.3`), its Lean name and type, and a **docstring** sentence in
  quotation marks; the Lean docstring is that sentence, word for word.
- Each lemma has an ID (`P2.4`), an English statement, the Lean statement, and a tag **[core]**
  (later modules depend on it), **[sanity]** (checks that a definition says what the English says),
  or **[later]** (wanted by Stage 2, proved here because it is cheap). The Lean docstring of a lemma
  is its English column. When a row holds several Lean lemmas, its English column gives one
  sentence per lemma, separated by " / " and in the same order, and each lemma's docstring is its
  own sentence. Bold in the English column marks a headline lemma in this document only; the
  docstring drops it.
- Tables are in proof order, which is also the order in the Lean file.
- **Binding rule.** Every name a docstring mentions is bound in the signature before the colon. A
  definition by cases uses `match` on that name.
- `autoImplicit = false`. Each section opens with the `variable` declarations it needs, from the
  letters below, and no others (Basic Round 4, R3). **Explicit or implicit.** The section
  `variable` line lists the names its lemmas take *implicitly*: those of a lemma with a hypothesis
  (`set_ne`, `get_revoke_of_ne`), found by unifying the hypothesis, and those of a rewrite lemma
  whose names all appear in its left-hand side (`set_set`). A lemma meant to be *applied* to
  particular values (`Board.set_same b s x`, `Board.initial_kingHome c`) binds them explicitly in
  its own signature, which shadows the section variable of the same letter. The Lean cell of each
  lemma is authoritative.
- **Ranks.** "Rank N", with N from 1 to 8, is always the chess name (rank 1 is White's back rank).
  A 0-based value is always written as code: `s.rank = 2`, `s.relRank c = 1`. So "`c`'s home
  rank" is `relRank c = 0` and "`c`'s second rank" is `relRank c = 1`.
- **Hexadecimal digits** are counted from the least significant, which is the 0th: "the `i`-th
  hexadecimal digit of `n`" is `n / 16 ^ i % 16`, and it is 0 beyond the most significant digit.
- **Pieces.** "Piece" includes pawns, as in Basic (`Piece` has a `Kind`, and `pawn` is a kind).
- `@[simp]` is written on every lemma that carries it; a lemma whose cell does not say `@[simp]` does
  not carry it.
- Everything lives in `namespace Chess`; names are given without the `Chess.` prefix. References like
  "Basic D7.4" are to `docs/spec/Basic.md`.
- **Whole-type quantifier instances have `priority := low`** (Basic D1.4, review C1), so that a
  bounded quantifier `∀ x ∈ l, P x` is decided by the list `l`, never by sweeping the type. Each such
  instance in this file gets the two `rfl` regression tests of §7.

Letters used in this module (they extend Basic's list; Basic's `x y` for coordinates do not occur
here, so the letters are reused):

- `b b'` boards; `s t s'` squares (`s'` a second square that is written, `t` a square that is read).
- `x y` the contents of a square, of type `Option Piece`; `pc pc'` pieces; `k` a kind; `pk` a
  promotion choice; `f` a file (`Fin 8`).
- `v` a code or hexadecimal digit (`Fin 16`); `n` a packed number (`Nat`); `i` a digit position
  (`Nat`); `l` a list of digits (`List (Fin 16)`); `acc` the accumulator of a fold.
- `m` a move; `cr cr' cr''` castling rights; `c c'` colours; `w w'` wings; `p q` positions.

FIDE references are to the Laws of Chess effective 1 January 2023, as in Basic §0: initial position
2.3; en passant 3.7.3.1, and only on the move after the two-square advance 3.7.3.2; promotion
3.7.3.3; castling 3.8.2, right to castle lost 3.8.2.1.

---

## 1. Section "Boards"

**D1.1 `Board : Type`.**
```lean
def Board : Type := Square → Option Piece
```
Docstring: "A board: for each square, the piece standing on it, or `none` if the square is empty."

Reading a board is function application: `b s` is what stands on `s`. `Board` is a `def`, not an
`abbrev` (DESIGN §4.3), so that the instances below are the only ones that apply to it and so that
`b.set …` resolves in the `Board` namespace. Checked: application `b s` and dot notation `b.set`
both elaborate with `Board` a `def`, and `funext` applies to boards directly.

**D1.2 `Board.ext`.**
```lean
@[ext] theorem Board.ext {b b' : Board} (h : ∀ s, b s = b' s) : b = b' := funext h
```
Docstring: "Two boards are equal when they hold the same thing on every square."
Proof note: the `ext` tactic does not stop at squares; `ext s` goes on to apply `Option.ext` to
`b s = b' s` and leaves an `↔` goal. In proofs write `refine Board.ext fun s => ?_` or `ext s : 1`
(checked). The module docstring's implementation notes repeat this, for readers of the Lean.

**D1.3 `Board.decEq : DecidableEq Board`.**
```lean
instance Board.decEq : DecidableEq Board := fun b b' =>
  decidable_of_iff (∀ s, b s = b' s) ⟨Board.ext, fun h _ => h ▸ rfl⟩
```
Docstring: "Two boards are compared square by square, through the decidable quantifier over
squares: at most 64 comparisons."
The quantifier is unbounded, so `Square.decidableForall` (Basic D3.6) is the instance found despite
its low priority. Core has no `DecidableEq` for function types, so nothing competes.

**D1.4 `Board.empty : Board`.** `fun _ => none`.
Docstring: "The board with nothing on it."
Followed by `instance : Inhabited Board := ⟨Board.empty⟩`, docstring "The default board is the empty
board."

**D1.5 `Board.set (b : Board) (s : Square) (x : Option Piece) : Board`.**
```lean
def Board.set (b : Board) (s : Square) (x : Option Piece) : Board :=
  fun t => if t = s then x else b t
```
Docstring: "The board `b` with square `s` made to hold `x`: `x` on `s`, and on every other square
what `b` has there."
This is the only way the library writes to a board (DESIGN §4.3). Every change a move makes is a
composition of `set`s, so every frame lemma of R4 is a `set_ne` rewrite.

Lemmas (`variable {b : Board} {s s' t : Square} {x y : Option Piece}`):

| ID | English | Lean | Tag |
|---|---|---|---|
| P1.1 | Reading a square of the empty board gives nothing. | `@[simp] theorem Board.empty_apply (s : Square) : Board.empty s = none` | core |
| P1.2 | What `b.set s x` holds on `t` is `x` if `t` is `s`, and what `b` holds on `t` otherwise. | `theorem Board.set_apply (b : Board) (s : Square) (x : Option Piece) (t : Square) : b.set s x t = if t = s then x else b t` | core |
| P1.3 | After setting `s` to `x`, square `s` holds `x`. | `@[simp] theorem Board.set_same (b : Board) (s : Square) (x : Option Piece) : b.set s x s = x` | core |
| P1.4 | Setting `s` does not change any other square. | `@[simp] theorem Board.set_ne (h : t ≠ s) : b.set s x t = b t` | core |
| P1.5 | Setting two different squares can be done in either order. | `theorem Board.set_comm (h : s ≠ s') : (b.set s x).set s' y = (b.set s' y).set s x` | core |
| P1.6 | Setting the same square twice keeps only the second value. | `@[simp] theorem Board.set_set : (b.set s x).set s y = b.set s y` | core |
| P1.7 | Setting a square to what it already holds changes nothing. | `@[simp] theorem Board.set_eq_self : b.set s (b s) = b` | later |

Proofs: P1.1 and P1.2 are `rfl`. P1.3 is `if_pos rfl` (or `simp [Board.set]`). P1.4 is
`if_neg h` (or `simp [Board.set, h]`). P1.5–P1.7: `refine Board.ext fun t => ?_`, then
`simp only [Board.set]` and `split <;> split <;> simp_all` (P1.5) or `split <;> simp_all` (P1.6,
P1.7). All checked.

`set_ne`'s hypothesis reads "the square read is not the square written", `t ≠ s`, the orientation
of Mathlib's `Function.update_of_ne`. **Orientation matters to `simp` (checked):** with
`h : t ≠ s` in hand, `simp [h]` rewrites `b.set s x t` to `b t`; with `h : s ≠ t`, `simp [h]` makes
no progress, and the proof must pass `Ne.symm h` (or `h.symm`). On concrete squares plain `simp`
suffices, because the side goal `t ≠ s` is closed by `decide`.
**`set_comm` is not `@[simp]`**, although DESIGN §4.3 lists it with the simp lemmas: a
commutativity lemma is a permutation lemma, which `simp` either refuses or applies by term order, so
the normal form of a chain of `set`s would depend on how the squares happen to be ordered. R4's
proofs need only `set_same` and `set_ne`; `set_comm` is used with `rw`.

---

## 2. Section "Piece codes and packed boards"

A board can be written as one natural number whose `i`-th hexadecimal digit (the least significant
is the 0th, §0) is the code of what stands on the square with index `i`. This is DESIGN §4.3's
packed-literal *notation*: it never replaces `Board`, and no headline statement mentions it. It
exists for the generated per-node checkpoint theorems of DESIGN §7.4.

**D2.1 `Piece.code (pc : Piece) : Fin 16`.**
```lean
def Piece.code (pc : Piece) : Fin 16 :=
  match pc.color, pc.kind with
  | .white, .pawn => 1 | .white, .knight => 2 | .white, .bishop => 3
  | .white, .rook => 4 | .white, .queen  => 5 | .white, .king   => 6
  | .black, .pawn => 7 | .black, .knight => 8 | .black, .bishop => 9
  | .black, .rook => 10 | .black, .queen => 11 | .black, .king  => 12
```
Docstring: "The code of piece `pc` in packed boards: 1 to 6 for the white pawn, knight, bishop, rook,
queen and king, and 7 to 12 for the black ones in the same order. Code 0 means an empty square, and
codes 13 to 15 are unused."

This match is **the** code table: it is the only place in the library where piece codes are written
(DESIGN Principle 5). The kinds are in `Kind.all` order, so the white codes are python-chess's
`piece_type` numbers and a black piece's code is its `piece_type` plus 6; the certificate scripts
can rely on that.

**D2.2 `Piece.ofCode (v : Fin 16) : Option Piece`.**
```lean
def Piece.ofCode (v : Fin 16) : Option Piece :=
  Piece.all.find? fun pc => pc.code = v
```
Docstring: "The piece whose code is `v`, or `none` if no piece has code `v` (code 0, which marks an
empty square, and the unused codes 13 to 15)."
It is defined by searching `Piece.all` (Basic D2.7) for the code, so the table D2.1 is written once
and its inverse cannot disagree with it. (The `Prop` `pc.code = v` is turned into a `Bool` by
`decide`, which the elaborator inserts.) See §8 item 4 for the measured cost and the fallback.

**D2.3 `contentsCode (x : Option Piece) : Fin 16`.**
```lean
def contentsCode (x : Option Piece) : Fin 16 :=
  match x with
  | none    => 0
  | some pc => pc.code
```
Docstring: "The code of what stands on a square: 0 if it is empty, and the piece's code otherwise."
Named for its argument, the *contents* of a square (letter `x`, §0); it takes no square. (Round 3
called it `squareCode`.)

**D2.4 `hexDigit (n i : Nat) : Fin 16`.**
```lean
def hexDigit (n i : Nat) : Fin 16 := ⟨n / 16 ^ i % 16, Nat.mod_lt _ (by decide)⟩
```
Docstring: "The `i`-th hexadecimal digit of `n`, the least significant being the 0th (0 beyond the
most significant digit)."
Division and remainder, not `>>>` and `&&&`: both forms are accelerated by the kernel
(*lean-eng* §2), and the division form is what core's lemmas speak about (P2.6's proof).
`hexDigit` and `ofHexDigits` (D2.5) are general `Nat` plumbing for packed literals; nothing outside
this section uses them.

**D2.5 `ofHexDigits (l : List (Fin 16)) : Nat`.**
```lean
def ofHexDigits (l : List (Fin 16)) : Nat := l.foldr (fun v acc => v.val + 16 * acc) 0
```
Docstring: "The number whose hexadecimal digits, from the least significant one up, are the entries
of `l`, followed by zeros."

**D2.6 `Board.unpack (n : Nat) : Board`.**
```lean
def Board.unpack (n : Nat) : Board := fun s => Piece.ofCode (hexDigit n s.index.val)
```
Docstring: "The board written as the number `n`: square `s` holds the piece whose code is the
`s.index`-th hexadecimal digit of `n`, and is empty if that digit is 0 or an unused code (13 to 15).
Digits beyond the 63rd are ignored."
A malformed literal is not rejected: every `n` unpacks to some board, and a kernel-checked equality
with the board a checkpoint expects simply fails.

**D2.7 `Board.pack (b : Board) : Nat`.**
```lean
def Board.pack (b : Board) : Nat := ofHexDigits (Square.all.map fun s => contentsCode (b s))
```
Docstring: "The packed form of board `b`: the number below 16 ^ 64 whose `s.index`-th hexadecimal
digit is the code of what stands on `s`."
Both halves of the docstring are lemmas: "below 16 ^ 64" is P2.10 (`Board.pack_lt`) and the digit
clause is P2.9 (`Board.hexDigit_pack`). Together they make "the number" unique, since a number below
16 ^ 64 is fixed by its 64 digits.
Many numbers unpack to the same board (§2's closing paragraph); `pack` picks the one with 64 digits
at most, each at most 12. So `pack (unpack n) = n` holds exactly when `n < 16 ^ 64` and every digit
of `n` is at most 12; that could be a [later] lemma if a certificate script ever needs it.
`Square.all` is in index order (Basic D3.4), so entry `i` of the list belongs to the square with
index `i`. `pack` is meant for `#eval` (to produce checkpoint literals, DESIGN §7.4); proofs use only
P2.12.

Lemmas (`variable {pc pc' : Piece} {v : Fin 16}`):

| ID | English | Lean | Tag |
|---|---|---|---|
| P2.1 | Reading back the code of a piece gives the piece. | `@[simp] theorem Piece.ofCode_code (pc : Piece) : Piece.ofCode pc.code = some pc` | core |
| P2.2 | Code 0 is no piece. | `@[simp] theorem Piece.ofCode_zero : Piece.ofCode 0 = none` | core |
| P2.3 | Reading back the code of a square's contents gives the contents. | `@[simp] theorem Piece.ofCode_contentsCode (x : Option Piece) : Piece.ofCode (contentsCode x) = x` | core |
| P2.4 | Different pieces have different codes. / No piece has code 0. | `@[simp] theorem Piece.code_inj : pc.code = pc'.code ↔ pc = pc'` and `theorem Piece.code_ne_zero (pc : Piece) : pc.code ≠ 0` | sanity |
| P2.5 | A code is read as empty exactly when it is 0 or one of the unused codes 13 to 15. | `theorem Piece.ofCode_eq_none_iff : Piece.ofCode v = none ↔ v = 0 ∨ 13 ≤ v.val` | sanity |
| P2.6 | The `i`-th hexadecimal digit of the number with digit list `l` is entry `i` of `l`, or 0 beyond its end. | `theorem hexDigit_ofHexDigits (l : List (Fin 16)) (i : Nat) : hexDigit (ofHexDigits l) i = l.getD i 0` | core |
| P2.7 | The number with digit list `l` is below `16 ^ l.length`. | `theorem ofHexDigits_lt (l : List (Fin 16)) : ofHexDigits l < 16 ^ l.length` | sanity |
| P2.8 | Entry `s.index` of the list of all squares is `s`. | `theorem Square.getElem?_all_index (s : Square) : Square.all[s.index.val]? = some s` | core |
| P2.9 | The `s.index`-th hexadecimal digit of a packed board is the code of what stands on `s`. | `theorem Board.hexDigit_pack (b : Board) (s : Square) : hexDigit b.pack s.index.val = contentsCode (b s)` | core |
| P2.10 | A packed board is below `16 ^ 64`: it has at most 64 hexadecimal digits. | `theorem Board.pack_lt (b : Board) : b.pack < 16 ^ 64` | sanity |
| P2.11 | Square `s` of an unpacked board is read from the `s.index`-th hexadecimal digit. | `theorem Board.unpack_apply (n : Nat) (s : Square) : Board.unpack n s = Piece.ofCode (hexDigit n s.index.val)` | core |
| P2.12 | **Unpacking the packing of a board gives the board back.** | `@[simp] theorem Board.unpack_pack (b : Board) : Board.unpack b.pack = b` | core |

Proofs (all checked):
- P2.1, P2.2, P2.4, P2.5: `revert` the variables, then `decide`. P2.1 and P2.4 go through the
  `Piece` quantifier of Basic D2.7 (12 and 144 cases); P2.5 through core's `Fin 16` quantifier.
- P2.3: `cases x`, then P2.2 or P2.1.
- P2.6: induction on `l`, generalizing `i`, then `cases i`. Case `nil`: `simp [hexDigit,
  ofHexDigits]`. Case `cons v l`, `i = 0`: `Fin.ext`, then `simp [hexDigit, ofHexDigits]`. Case
  `cons v l`, `i + 1`: rewrite the goal's right side with `List.getD_cons_succ` and the induction
  hypothesis backwards, so that both sides are digits; then `Fin.ext`, and one `simp only` with
  `hexDigit`, `ofHexDigits`, `List.foldr_cons`, `Nat.pow_succ`, `Nat.mul_comm (16 ^ i)`,
  `← Nat.div_div_eq_div_mul`, `Nat.add_mul_div_left` and `v.val / 16 = 0`. In words: dividing by
  `16 ^ (i + 1)` divides by 16 first, and that drops the low digit `v`, leaving the rest.
- P2.7: induction on `l`; in the `cons` case unfold `ofHexDigits`, `List.foldr_cons`,
  `List.length_cons` and `Nat.pow_succ` in the goal and the hypothesis, then `omega` with
  `v.isLt`.
- P2.8: `rw [List.getElem?_eq_getElem (by rw [Square.length_all]; exact s.index.isLt)]`, then
  `simp only [Square.all, List.getElem_map, List.getElem_finRange]` and
  `exact congrArg some (Square.ofIndex_index s)`. This is a fact about `Basic`; its natural home is
  next to `Square.mem_all` there (open item, §9).
- P2.9: unfold `Board.pack`, rewrite with P2.6, `List.getD_eq_getElem?_getD`, `List.getElem?_map`
  and P2.8, then `rfl` (`Option.map_some`, `Option.getD_some`).
- P2.10: P2.7 for the list of 64 codes, rewritten with `List.length_map` and `Square.length_all`.
- P2.11: `rfl`.
- P2.12: `refine Board.ext fun s => ?_`, then P2.11, P2.9 and P2.3.

`Board.pack (Board.unpack n) = n` is **not** a lemma: it fails when `n` has a digit 13–15 or more
than 64 digits. Nothing needs it.

---

## 3. Section "Moves"

**D3.1 `Move : Type`.**
```lean
@[ext] structure Move where
  src : Square
  dst : Square
  promo : Option PromoKind
  deriving DecidableEq, Inhabited
```
Docstring: "A move as data, as in UCI notation: a source square, a destination square, and an
optional promotion choice. Castling is written as the king's two-square move (e1g1, e1c1, e8g8,
e8c8), never as king-takes-rook; this library has no Chess960."
Field docstrings: "The source square.", "The destination square.", "The promotion choice, meaningful
only when a pawn reaches its last rank: `some pk` promotes it to kind `pk.toKind`. A move whose
`promo` does not match the position is not legal (`Chess.Rules`)."

`Move` is plain data: `a1a1`, a move from an empty square and `some .queen` on a knight move are all
values. The `promo` field docstring is a promise this module cannot check: the `Rules` review must
hold `PseudoLegal` to it both ways, no `promo` on a move that does not promote, and a `promo`
required when a pawn reaches its last rank. A move does not say what kind of move it is (capture, en passant, castling); `Chess.Rules`
works that out from the position (DESIGN §4.4). `Repr` is **not** derived: §6 gives a hand-written one
that prints UCI (`e2e4`), following review C5 of `Chess.Basic`. The derived `Inhabited` value is
`a1a1` without promotion; nothing uses it.

**D3.2 Decidable quantifiers over moves.** Two instances, `Move.decidableForall` and
`Move.decidableExists`, both `(priority := low)`:
```lean
instance (priority := low) Move.decidableForall (P : Move → Prop) [DecidablePred P] :
    Decidable (∀ m, P m) :=
  decidable_of_iff (∀ s t : Square, P ⟨s, t, none⟩ ∧ ∀ pk : PromoKind, P ⟨s, t, some pk⟩)
    ⟨fun h m => match m with
      | ⟨s, t, none⟩    => (h s t).1
      | ⟨s, t, some pk⟩ => (h s t).2 pk,
     fun h _ _ => ⟨h _, fun _ => h _⟩⟩

instance (priority := low) Move.decidableExists (P : Move → Prop) [DecidablePred P] :
    Decidable (∃ m, P m) :=
  decidable_of_iff (∃ s t : Square, P ⟨s, t, none⟩ ∨ ∃ pk : PromoKind, P ⟨s, t, some pk⟩)
    ⟨fun ⟨_, _, h⟩ => h.elim (fun h => ⟨_, h⟩) (fun ⟨_, h⟩ => ⟨_, h⟩),
     fun ⟨⟨s, t, o⟩, h⟩ => ⟨s, t, match o, h with
       | none, h    => .inl h
       | some pk, h => .inr ⟨pk, h⟩⟩⟩
```
Docstrings: "`∀` over moves is decided through the two squares and the five promotion choices
(`none` and the four `PromoKind`s): 64 × 64 × 5 candidates." and "`∃` over moves is decided through
the two squares and the five promotion choices."
They are what makes `Checkmate` and `Stalemate` decidable in Stage 1 (DESIGN §5.6). They have low
priority so that `∀ m ∈ legalMoves p, Legal p m` is decided by the list (Basic review C1). Checked:
both elaborate, and the bounded-quantifier test of §7 holds by `rfl`. A full sweep is slow (about
4 s for `∀ m : Move, …` under plain `decide`), so the tests of this file never do one.

No `Move.all` list and no lemmas: a list of 20 480 candidate moves would only invite a generator to
use it. So `Move` meets only the decidability half of R2 (header).

---

## 4. Section "Castling rights"

**D4.1 `CastlingRights : Type`.**
```lean
structure CastlingRights where
  whiteKingside : Bool
  whiteQueenside : Bool
  blackKingside : Bool
  blackQueenside : Bool
  deriving DecidableEq, Repr, Inhabited
```
Docstring: "The castling rights: for each colour and wing, the FEN flag saying whether that colour
still holds the right to castle on that wing. The four flags are in FEN order (K, Q, k, q). By
convention they are read with `get` and changed only with `revoke` and `revokeAll`; the fields stay
public for literals, so it is `Chess.Rules` (R8) that proves a move adds no right."
Field docstrings: "White's kingside castling flag (FEN `K`).", "White's queenside castling flag (FEN
`Q`).", "Black's kingside castling flag (FEN `k`).", "Black's queenside castling flag (FEN `q`)."

A flag is a right in the sense of FIDE 3.8.2.1 (lost for good), not a permission to castle now:
whether castling is possible on this move is decided by `Chess.Rules`.

**Interface rule (a convention, not enforced by Lean).** Outside this section, no definition or
theorem mentions the four fields; they read rights with `get` (D4.2). The constructor appears only
in literals `⟨K, Q, k, q⟩`, in FEN order: parsers, checkpoints and tests. No function in the
library takes castling rights and returns rights containing one its input lacked: the only functions
from `CastlingRights` to `CastlingRights` are `revoke` and `revokeAll`, and both are `≤` their
input (P4.11). Lean does not enforce any of this: the fields and the constructor are public, so
`{ cr with whiteKingside := true }` typechecks in any module. Making the constructor private would
enforce it, but literals and parsers need `⟨K, Q, k, q⟩`, so the rule stays a convention that
reviews check. The guarantee is R8 itself, proved in `Chess.Rules` from P4.11 by inspecting `play`
and showing that it builds its rights from `p.castling` with these two functions only.
The derived `Inhabited` value is all four flags `false`, that is `CastlingRights.none` (§8 item 12
on why this differs from the initial rights).

**D4.2 `CastlingRights.get (cr : CastlingRights) (c : Color) (w : Wing) : Bool`.**
```lean
def CastlingRights.get (cr : CastlingRights) (c : Color) (w : Wing) : Bool :=
  match c, w with
  | .white, .kingside  => cr.whiteKingside
  | .white, .queenside => cr.whiteQueenside
  | .black, .kingside  => cr.blackKingside
  | .black, .queenside => cr.blackQueenside
```
Docstring: "Whether `cr` holds colour `c`'s right to castle on wing `w`: the FEN flag, which is lost
when the king or that wing's rook moves, or that rook is captured on its home square (FIDE 3.8.2.1
and the FEN convention). It does not say that castling is possible now."

**D4.3 `CastlingRights.revoke (cr : CastlingRights) (c : Color) (w : Wing) : CastlingRights`.**
```lean
def CastlingRights.revoke (cr : CastlingRights) (c : Color) (w : Wing) : CastlingRights :=
  match c, w with
  | .white, .kingside  => { cr with whiteKingside := false }
  | .white, .queenside => { cr with whiteQueenside := false }
  | .black, .kingside  => { cr with blackKingside := false }
  | .black, .queenside => { cr with blackQueenside := false }
```
Docstring: "The rights `cr` with colour `c`'s right on wing `w` set to not held (whether or not it
was held), and every other right unchanged."

**D4.4 `CastlingRights.revokeAll (cr : CastlingRights) (c : Color) : CastlingRights`.**
`(cr.revoke c .kingside).revoke c .queenside`.
Docstring: "The rights `cr` with both of colour `c`'s rights set to not held, as after a move of
`c`'s king (FIDE 3.8.2.1)."

**D4.5 `CastlingRights.none : CastlingRights`.** `⟨false, false, false, false⟩`.
Docstring: "No castling rights: neither colour holds a right on either wing."
**Name hazard (checked).** Inside `namespace CastlingRights` or a declaration named
`CastlingRights.…`, a bare `none` means this value, not `Option.none`; write `Option.none` there.
Outside, write `CastlingRights.none` (or `.none` where the expected type is `CastlingRights`):
THEOREMS R6's `p.castling = none` would elaborate as `Option.none` and fail. Round 4 confirmed the
hazard: inside `namespace Chess`, `def CastlingRights.probe (_ : CastlingRights) : Option Nat :=
none` fails, because `none` resolves to `CastlingRights.none`. The name is DESIGN's (§4.5, R6); §9
item 6 recommends renaming it `CastlingRights.empty`, an owner decision.

**D4.6 `CastlingRights.full : CastlingRights`.** `⟨true, true, true, true⟩`.
Docstring: "All four castling rights, as at the start of a game."
Not `CastlingRights.all`: in this library `T.all` is the list of all values of a finite type (R2),
and `CastlingRights` has no such list (header).

**D4.7 Decidable quantifiers over castling rights.** `CastlingRights.decidableForall` and
`CastlingRights.decidableExists`, both `(priority := low)`, through the four flags:
```lean
instance (priority := low) CastlingRights.decidableForall (P : CastlingRights → Prop)
    [DecidablePred P] : Decidable (∀ cr, P cr) :=
  decidable_of_iff (∀ a b c d : Bool, P ⟨a, b, c, d⟩)
    ⟨fun h cr => h cr.1 cr.2 cr.3 cr.4, fun h a b c d => h ⟨a, b, c, d⟩⟩
```
and the same for `∃`: `decidable_of_iff (∃ a b c d : Bool, P ⟨a, b, c, d⟩)
⟨fun ⟨_, _, _, _, h⟩ => ⟨_, h⟩, fun ⟨cr, h⟩ => ⟨cr.1, cr.2, cr.3, cr.4, h⟩⟩`. (The bound names `a b c d` are local to this one instance; `c` is a `Bool`
here, not a colour.)
Docstrings: "`∀` over castling rights is decided through the four flags: 16 cases." and "`∃` over
castling rights is decided through the four flags: 16 cases."
These are what make every lemma below a one-line `decide`: there are only 16 values, so a statement
about all rights, colours and wings is a finite check (checked, all of P4.1–P4.13 together in under
a second).

**D4.8 The order on castling rights.**
```lean
instance : LE CastlingRights :=
  ⟨fun cr cr' => ∀ c w, cr.get c w = true → cr'.get c w = true⟩

instance CastlingRights.decidableLE (cr cr' : CastlingRights) : Decidable (cr ≤ cr') :=
  inferInstanceAs (Decidable (∀ c w, cr.get c w = true → cr'.get c w = true))
```
Docstrings: "`cr ≤ cr'` when every right held in `cr` is also held in `cr'`." and "Whether
`cr ≤ cr'` is decided by checking both colours and both wings."
This is the pointwise order of DESIGN §4.5, in which R8 is stated. This module supports R8 in
DESIGN §4.5's **unconditional** form, `(p.play m).castling ≤ p.castling` for every `p` and `m`,
which was stronger than THEOREMS R8's former `castling_play_le (h : Legal p m)`; THEOREMS R8 now
states the unconditional form.

After P4.10 (the order lemmas) comes
```lean
instance : Trans (α := CastlingRights) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans⟩
```
with docstring "Inequalities between castling rights chain in `calc`.", so that R8's proof through a
chain of revocations can be written as a `calc`.

Lemmas (`variable {cr cr' cr'' : CastlingRights} {c c' : Color} {w w' : Wing}`). Unless the cell
says otherwise, each is proved by `revert`ing its variables and `decide` (through D4.7 and Basic's
`Color` and `Wing` quantifiers):

| ID | English | Lean | Tag |
|---|---|---|---|
| P4.1 | Two castling rights are equal when they agree for every colour and wing. | `@[ext] theorem CastlingRights.ext_get (h : ∀ c w, cr.get c w = cr'.get c w) : cr = cr'` | core |
| P4.2 | `CastlingRights.none` holds no right. | `@[simp] theorem CastlingRights.get_none (c : Color) (w : Wing) : CastlingRights.none.get c w = false` | core |
| P4.3 | `CastlingRights.full` holds every right. | `@[simp] theorem CastlingRights.get_full (c : Color) (w : Wing) : CastlingRights.full.get c w = true` | core |
| P4.4 | A revoked right is not held. | `@[simp] theorem CastlingRights.get_revoke_self (cr : CastlingRights) (c : Color) (w : Wing) : (cr.revoke c w).get c w = false` | core |
| P4.5 | Revoking one right leaves every other right as it was. | `theorem CastlingRights.get_revoke_of_ne (h : c' ≠ c ∨ w' ≠ w) : (cr.revoke c w).get c' w' = cr.get c' w'` | core |
| P4.6 | After `revokeAll c`, colour `c` holds no right. | `@[simp] theorem CastlingRights.get_revokeAll_self (cr : CastlingRights) (c : Color) (w : Wing) : (cr.revokeAll c).get c w = false` | core |
| P4.7 | `revokeAll c` leaves the other colour's rights as they were. | `theorem CastlingRights.get_revokeAll_of_ne (h : c' ≠ c) : (cr.revokeAll c).get c' w = cr.get c' w` | core |
| P4.8 | After revoking colour `c`'s right on wing `w`, a right is held exactly when it was held before and is not that one. / After revoking all of colour `c`'s rights, a right is held exactly when it was held before and is not one of `c`'s. | `theorem CastlingRights.get_revoke (cr : CastlingRights) (c c' : Color) (w w' : Wing) : (cr.revoke c w).get c' w' = (cr.get c' w' && !(c' == c && w' == w))` and `theorem CastlingRights.get_revokeAll (cr : CastlingRights) (c c' : Color) (w : Wing) : (cr.revokeAll c).get c' w = (cr.get c' w && !(c' == c))` | core |
| P4.9 | `cr ≤ cr'` means every right of `cr` is a right of `cr'`. | `theorem CastlingRights.le_def : cr ≤ cr' ↔ ∀ c w, cr.get c w = true → cr'.get c w = true` (`Iff.rfl`) | core |
| P4.10 | The order is reflexive. / The order is transitive. / The order is antisymmetric. | `@[simp] theorem CastlingRights.le_refl (cr : CastlingRights) : cr ≤ cr` (`fun _ _ h => h`), `theorem CastlingRights.le_trans (h : cr ≤ cr') (h' : cr' ≤ cr'') : cr ≤ cr''` (`fun c w hc => h' c w (h c w hc)`), `theorem CastlingRights.le_antisymm (h : cr ≤ cr') (h' : cr' ≤ cr) : cr = cr'` | core |
| P4.11 | **(R8) Revoking never adds a right.** / **(R8) Revoking all of a colour's rights never adds a right.** | `theorem CastlingRights.revoke_le (cr : CastlingRights) (c : Color) (w : Wing) : cr.revoke c w ≤ cr` and `theorem CastlingRights.revokeAll_le (cr : CastlingRights) (c : Color) : cr.revokeAll c ≤ cr` | core |
| P4.12 | No rights is below everything. / All rights are above everything. | `@[simp] theorem CastlingRights.none_le (cr : CastlingRights) : CastlingRights.none ≤ cr` and `@[simp] theorem CastlingRights.le_full (cr : CastlingRights) : cr ≤ CastlingRights.full` | sanity |
| P4.13 | Revocations can be made in any order. / Revoking twice is revoking once. | `theorem CastlingRights.revoke_comm (cr : CastlingRights) (c c' : Color) (w w' : Wing) : (cr.revoke c w).revoke c' w' = (cr.revoke c' w').revoke c w` and `@[simp] theorem CastlingRights.revoke_revoke_self (cr : CastlingRights) (c : Color) (w : Wing) : (cr.revoke c w).revoke c w = cr.revoke c w` | later |

Notes:
- P4.1 is the extensionality lemma of the interface: with it, R6's colour swap and any statement
  about rights is proved through `get`, never through fields. It is `@[ext]` on the theorem, not on
  the structure, so that `ext` produces `∀ c w, …` goals rather than four field goals.
- P4.5 and P4.7 are not `@[simp]`: their hypotheses are disjunctions or disequalities that `simp`
  cannot be relied on to discharge. With concrete colours and wings, `simp [get_revoke_of_ne]` or a
  `decide` does it.
- The two lemmas of P4.8 are unconditional equations, for the converse direction that R9.3's preservation needs:
  from `(p.play m).castling.get c w = true`, conclude that no revocation hit `(c, w)`. P4.4–P4.7
  only go forward. `simp [get_revoke, get_revokeAll]` pushes a `true` read through a chain of
  revocations (checked on a two-step chain with concrete colours and wings). They are not `@[simp]`,
  so the readable forms P4.4–P4.7 stay the default and a proof opts in to the case split.
- `revokeAll_le` follows from `revoke_le` twice and `le_trans`; either proof is fine. The Lean uses
  `le_trans (revoke_le _ c .queenside) (revoke_le cr c .kingside)`: `revokeAll` revokes kingside
  first, so the queenside step is the outer one.
- P4.13 is for `play`'s step 4 (DESIGN §5.5): it revokes once per rook-home square touched, and the
  order of those revocations must not matter.

---

## 5. Section "Positions"

**D5.1 `Position : Type`.**
```lean
@[ext] structure Position where
  board : Board
  turn : Color
  castling : CastlingRights
  epTarget : Option Square
```
Docstring: "A position of the move layer: the board, the side to move, the castling rights and the
en passant target. It holds what decides which moves are legal and what they do; no move clocks and
no history (DESIGN §4.6)."
Field docstrings:
- `board`: "What stands on each square."
- `turn`: "The side to move."
- `castling`: "The castling rights: for each colour and wing, the FEN flag saying whether that right
  is still held (FIDE 3.8.2.1). Whether castling is possible on this move is decided by the rules."
- `epTarget`: "The en passant target: `some t` means the previous move was a pawn's two-square
  advance over `t`, so a capture onto `t` may be considered this move (FIDE 3.7.3.2); `none` means
  it was not. Set after every two-square advance, whether or not any pawn can capture (the
  PGN-standard convention, not Stockfish's)."

No `deriving`: `Board` has no derived instances. `@[ext]` gives `Position.ext` and
`Position.ext_iff : p = q ↔ p.board = q.board ∧ p.turn = q.turn ∧ p.castling = q.castling ∧
p.epTarget = q.epTarget` (checked). The field docstrings describe what `play` maintains; `Position`
itself is plain data and carries no invariant (`WellFormed` is Stage 2, DESIGN §4.6). **For a
literal position** (`Position.initial`, a FEN, an `unpack` checkpoint), which has no previous move,
these field meanings are a convention the literal's author must follow; `Position` enforces none of
them. In particular a checkpoint generator must set `epTarget` after every double push, as python-
chess's `fen(en_passant="fen")` does, not only when a capture is possible (Stockfish, and
python-chess's default `fen()`).

**D5.2 `Position.decEq : DecidableEq Position`.**
```lean
instance Position.decEq : DecidableEq Position := fun p q =>
  decidable_of_iff
    (p.turn = q.turn ∧ p.castling = q.castling ∧ p.epTarget = q.epTarget ∧ p.board = q.board)
    ⟨fun ⟨h1, h2, h3, h4⟩ => Position.ext h4 h1 h2 h3, fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩⟩
```
Docstring: "Two positions are compared field by field, the three small fields first and the board
(at most 64 comparisons) last."
Hand-written for one reason, the order of comparison: a derived instance compares the fields in
declaration order, so the board first, while this one compares it last, so that most unequal
positions are told apart without reading the board. (Deriving would work: `Board.decEq` exists
before `Position`, and a `structure … deriving DecidableEq` with the same four fields builds and
decides; Round 4 checked this. Round 3's second reason, that deriving was impossible, was wrong.)
Checked: `decide` and `decide +kernel` both use the hand-written instance.

**D5.3 `backRankKind (f : Fin 8) : Kind`.**
```lean
def backRankKind (f : Fin 8) : Kind :=
  match f with
  | 0 => .rook | 1 => .knight | 2 => .bishop | 3 => .queen
  | 4 => .king | 5 => .bishop | 6 => .knight | 7 => .rook
```
Docstring: "The kind of piece that starts on file `f` of either colour's home rank (the same for
both): rook, knight, bishop, queen, king, bishop, knight, rook from the a-file to the h-file
(FIDE 2.3)."
Checked: Lean 4.28 accepts `Fin 8` literal patterns, sees the match as exhaustive, and evaluates it
under `decide`.

**D5.4 `startingPiece (c : Color) (s : Square) : Option Piece`.**
```lean
def startingPiece (c : Color) (s : Square) : Option Piece :=
  if s.relRank c = 0 then some ⟨c, backRankKind s.file⟩
  else if s.relRank c = 1 then some ⟨c, .pawn⟩
  else none
```
Docstring: "The piece of colour `c` that stands on `s` at the start of a game, if any: on `c`'s
home rank (`relRank` 0) the piece of kind `backRankKind s.file`, on the next rank (`relRank` 1) a
pawn, and elsewhere nothing."
Colour enters only through `relRank` (Basic D6.3), so White's and Black's set-ups are one
definition (DESIGN Principle 5).

**D5.5 `Board.initial : Board`.**
```lean
def Board.initial : Board := fun s => (startingPiece .white s).or (startingPiece .black s)
```
Docstring: "The board at the start of a game (FIDE 2.3): each square holds the starting piece of
whichever colour has one there; no square has both (`startingPiece_white_or_black`)."
`Option.or` (core) takes the first `some`. No square has both a white and a black starting piece
(P5.9), so the order is immaterial; it is White first only to fix one. (This settles open item 4 in
favour of `Option.or`.)

**D5.6 `Position.initial : Position`.**
```lean
def Position.initial : Position :=
  { board := Board.initial, turn := .white, castling := .full, epTarget := none }
```
Docstring: "The position at the start of a game: the initial board, White to move, all four castling
rights, and no en passant target."
Followed by `instance : Inhabited Position := ⟨Position.initial⟩`, docstring "The default position
is the initial position."

Lemmas (`variable {s : Square} {c : Color}`):

| ID | English | Lean | Tag |
|---|---|---|---|
| P5.1 | The initial position has the initial board. / The initial position has White to move. / The initial position has all four castling rights. / The initial position has no en passant target. | `@[simp] theorem Position.initial_board : Position.initial.board = Board.initial`, `@[simp] theorem Position.initial_turn : Position.initial.turn = .white`, `@[simp] theorem Position.initial_castling : Position.initial.castling = .full`, `@[simp] theorem Position.initial_epTarget : Position.initial.epTarget = none` (all `rfl`) | core |
| P5.2 | Each king starts on its home square. | `theorem Board.initial_kingHome (c : Color) : Board.initial (kingHome c) = some ⟨c, .king⟩` (`cases c <;> rfl`) | core |
| P5.3 | Each rook starts on its home square. | `theorem Board.initial_rookHome (c : Color) (w : Wing) : Board.initial (rookHome c w) = some ⟨c, .rook⟩` (`cases c <;> cases w <;> rfl`) | core |
| P5.4 | Each queen starts on the d-file of its home rank. | `theorem Board.initial_queen (c : Color) : Board.initial ⟨3, c.homeRank⟩ = some ⟨c, .queen⟩` (`cases c <;> rfl`) | sanity |
| P5.5 | A colour's pawns fill its second rank (`relRank c = 1`). | `theorem Board.initial_of_relRank_one (h : s.relRank c = 1) : Board.initial s = some ⟨c, .pawn⟩` (`revert s; cases c <;> decide`) | sanity |
| P5.6 | The squares on ranks 3 to 6 (`rank` 2 to 5) are empty, and no others. | `theorem Board.initial_eq_none_iff : Board.initial s = none ↔ 2 ≤ s.rank.val ∧ s.rank.val ≤ 5` | sanity |
| P5.7 | A queen starts on a square of its own colour: the white queen on a light square, the black queen on a dark one. | `theorem Board.isLight_of_initial_queen (h : Board.initial s = some ⟨c, .queen⟩) : s.IsLight ↔ c = .white` | sanity |
| P5.8 | There are 32 pieces at the start, pawns included. / There are 16 pieces of each colour at the start, pawns included. | `theorem Board.count_initial : (Square.all.filter fun s => (Board.initial s).isSome).length = 32` and `theorem Board.count_initial_color (c : Color) : (Square.all.filter fun s => (Board.initial s).map (·.color) = some c).length = 16` (`cases c <;> decide`) | sanity |
| P5.9 | No square has both a white and a black starting piece. | `theorem startingPiece_white_or_black (s : Square) : startingPiece .white s = none ∨ startingPiece .black s = none` | sanity |
| P5.10 | Mirroring the initial board top to bottom swaps the colours of its pieces. | `theorem Board.initial_flip (s : Square) : Board.initial ⟨s.file, s.rank.rev⟩ = (Board.initial s).map fun pc => ⟨pc.color.other, pc.kind⟩` | sanity |

Proofs: where the cell gives none, `revert` the variables and `decide` (through Basic's `Square`,
`Color` and `Piece` quantifiers). All checked; together they take about a second.

P5.2 and P5.3 are what R10 needs to show that the initial castling rights are backed by king and
rook (`WellFormed Position.initial`, R9.3). P5.10 is the board half of R6 for the initial position;
when `Square.flip` exists (Basic §10) it reads `Board.initial s.flip = …`.

---

## 6. Sections "Notation" and "Display"

Corrected by the library review, 2026-11-01 (ChessGame review C1). The letters (`Kind.letter`,
`Piece.letter`, `PromoKind.letter`), `Move.toUCI` and `CastlingRights.letters` are **trusted**: the
FEN and UCI guards of `Chess.ChessGame` compare against them, so they are part of what `fen "…"` and
`uci "…"` mean. The Lean puts them under the heading "Notation (trusted: …)". `Color.name`,
`Board.rankLine`, the diagrams and the `Repr`/`ToString` instances of boards and positions are
untrusted display: nothing in the specification reads them; they exist so that `#eval` prints
boards and positions. The Lean puts them under "Display (untrusted: …)", with `Color.name` moved
there from between the letters and `Move.toUCI`.

**D6.1 `Kind.letter (k : Kind) : Char`.** `match k with`: pawn `'P'`, knight `'N'`, bishop `'B'`,
rook `'R'`, queen `'Q'`, king `'K'`.
Docstring: "The upper-case FEN letter of kind `k`: P, N, B, R, Q or K. Algebraic notation uses the
same letters but omits P."

**D6.2 `Piece.letter (pc : Piece) : Char`.**
`match pc.color with | .white => pc.kind.letter | .black => pc.kind.letter.toLower`.
Docstring: "The FEN letter of piece `pc`: its kind's letter, upper case for White and lower case for
Black."

**D6.3 `PromoKind.letter (pk : PromoKind) : Char`.** `pk.toKind.letter.toLower`.
Docstring: "The UCI letter of promotion choice `pk`: n, b, r or q."

**D6.4 `Color.name (c : Color) : String`.** `match c with | .white => "White" | .black => "Black"`.
Docstring: "The name of colour `c`: White or Black."

**D6.5 `Move.toUCI (m : Move) : String`.**
```lean
def Move.toUCI (m : Move) : String :=
  m.src.name ++ m.dst.name ++
    match m.promo with
    | none    => ""
    | some pk => pk.letter.toString
```
Docstring: "Move `m` in UCI notation, such as `e2e4`, or `e7e8q` for a promotion to a queen."
Followed by `instance : Repr Move := ⟨fun m _ => Std.Format.text m.toUCI⟩` and
`instance : ToString Move := ⟨Move.toUCI⟩`, docstrings "Moves print in UCI notation." (both).

**D6.6 `CastlingRights.letters (cr : CastlingRights) : String`.**
```lean
def CastlingRights.letters (cr : CastlingRights) : String :=
  let table := [('K', Color.white, Wing.kingside), ('Q', .white, .queenside),
    ('k', .black, .kingside), ('q', .black, .queenside)]
  let held := (table.filter fun (_, c, w) => cr.get c w).map (·.1)
  if held.isEmpty then "-" else String.ofList held
```
Docstring: "The castling rights `cr` as in FEN: the letters K, Q, k, q of the rights held, in that
order, or `-` if none is held."
Written with `filter` and `map`, it mentions no `none`, so the name hazard of D4.5 does not arise.
`CastlingRights` keeps its derived
`Repr` (DESIGN §4.1); `letters` is what the diagram prints.

**D6.7 `Board.rankLine (b : Board) (r : Fin 8) : String`.**
```lean
def Board.rankLine (b : Board) (r : Fin 8) : String :=
  String.intercalate " " (toString (r.val + 1) ::
    (List.finRange 8).map fun f => ((b ⟨f, r⟩).map (·.letter.toString)).getD ".")
```
Docstring: "Rank `r` of board `b` as one line of a diagram: the rank's number, then the eight
squares from the a-file to the h-file, each shown as its piece's letter or `.` if empty, separated by
spaces."
(`r` is a rank here; this is the one place the module names a rank.)

**D6.8 `Board.diagram (b : Board) : String`.**
`String.intercalate "\n" ((List.finRange 8).reverse.map b.rankLine ++ ["  a b c d e f g h"])`.
Docstring: "Board `b` as a text diagram: one line per rank from rank 8 down to rank 1, then a line of
file letters."
Followed by `instance : Repr Board := ⟨fun b _ => Std.Format.text b.diagram⟩`, docstring "Boards
print as diagrams."

**D6.9 `Position.diagram (p : Position) : String`.**
```lean
def Position.diagram (p : Position) : String :=
  p.board.diagram ++ "\n" ++ p.turn.name ++ " to move, castling " ++ p.castling.letters ++
    ", en passant " ++ (p.epTarget.map Square.name).getD "-"
```
Docstring: "Position `p` as a text diagram: the board's diagram, then a line giving the side to move,
the castling rights and the en passant target."
Followed by `instance : Repr Position := ⟨fun p _ => Std.Format.text p.diagram⟩` and
`instance : ToString Position := ⟨Position.diagram⟩`, docstrings "Positions print as diagrams."
The `Repr` instances ignore the precedence argument, so a diagram nested in a tuple or list prints
on its own lines; display is untrusted, so this is left as is.

`Position.initial` prints as (checked with `#eval` on a scratch translation):
```
8 r n b q k b n r
7 p p p p p p p p
6 . . . . . . . .
5 . . . . . . . .
4 . . . . . . . .
3 . . . . . . . .
2 P P P P P P P P
1 R N B Q K B N R
  a b c d e f g h
White to move, castling KQkq, en passant -
```

---

## 7. Section "Tests"

As `example`s and `#guard`s at the end of the file until the test library exists (review C8). Squares
are written `⟨file, rank⟩` with the algebraic name in a comment, until the owner decides on a square
literal (Basic review C4).

- `Board.set` on a literal: `(Board.empty.set ⟨4, 3⟩ (some ⟨.white, .queen⟩)) ⟨4, 3⟩ = some
  ⟨.white, .queen⟩` by `rfl`, and the same board on e5 (`⟨4, 4⟩`) is `none` by `rfl`.
- Packing the initial board (by `decide`):
  `Board.pack Board.initial = 0xA89CB98A77777777000000000000000000000000000000001111111142365324`.
  (The last eight digits, read right to left, are a1 to h1: 4 2 3 5 6 3 2 4, that is R N B Q K B N
  R. Then, still right to left, eight white pawns `1`, 32 empty squares `0`, eight black pawns `7`,
  and the first eight digits, read right to left, are a8 to h8: A 8 9 B C 9 8 A.)
- The literal round trip, kernel-checked:
  ```lean
  example : Position.initial =
      ⟨Board.unpack 0xA89CB98A77777777000000000000000000000000000000001111111142365324,
        .white, .full, none⟩ := by
    decide +kernel
  ```
  (An anonymous constructor, not `{ board := …, turn := … }` broken over lines: a structure
  instance's fields must start in the column of the first field, and a field continued at a smaller
  indentation is a parse error. Checked.)
- A `set` chain against a literal, kernel-checked (the checkpoint pattern of DESIGN §7.4, after
  1. e4): `(Board.initial.set ⟨4, 1⟩ none).set ⟨4, 3⟩ (some ⟨.white, .pawn⟩) = Board.unpack
  0xA89CB98A77777777000000000000000000010000000000001110111142365324` by `decide +kernel`.
- `Piece.ofCode 13 = none` by `decide`.
- Positions that differ only in the side to move are different:
  `Position.initial ≠ { Position.initial with turn := .black }` by `decide`.
- Castling rights: `CastlingRights.full.revokeAll .white = ⟨false, false, true, true⟩` by `decide`;
  `#guard CastlingRights.full.letters == "KQkq"`;
  `#guard (CastlingRights.full.revoke .black .queenside).letters == "KQk"`;
  `#guard CastlingRights.none.letters == "-"`.
- Moves: `#guard (Move.mk ⟨4, 6⟩ ⟨4, 7⟩ (some .queen)).toUCI == "e7e8q"` and
  `#guard toString (Move.mk ⟨4, 1⟩ ⟨4, 3⟩ none) == "e2e4"`; `∃ m : Move, m.src = ⟨0, 0⟩ ∧ m.dst =
  ⟨0, 1⟩ ∧ m.promo = some .rook` by `decide` (through D3.2's `∃` instance).
- The diagram: `#guard Position.initial.diagram == "8 r n b q k b n r\n7 p p p p p p p p\n6 . . . . . . . .\n5 . . . . . . . .\n4 . . . . . . . .\n3 . . . . . . . .\n2 P P P P P P P P\n1 R N B Q K B N R\n  a b c d e f g h\nWhite to move, castling KQkq, en passant -"`.
- A position with Black to move, no rights and target e3 (`⟨4, 2⟩`): its diagram ends with
  `Black to move, castling -, en passant e3` (`#guard … .endsWith …`).
- Bounded quantifiers are decided by the list (D3.2, D4.7), by `rfl`:
  ```lean
  example (l : List Move) (P : Move → Prop) [DecidablePred P] :
      (inferInstance : Decidable (∀ m ∈ l, P m)) = List.decidableBAll P l := rfl
  example (l : List Move) (P : Move → Prop) [DecidablePred P] :
      (inferInstance : Decidable (∃ m ∈ l, P m)) = List.decidableBEx P l := rfl
  ```
  and the same two for `CastlingRights`.

---

## 8. Design choices, with reasons

1. **`Board` is a function, and `set` is its only writer.** The function board is faithful by
   construction (one thing per square, no padding, no sentinel), reading is application, and the
   frame lemmas of R4 are `set_ne` rewrites (*lean-eng* §5: the function board is also the fastest
   non-packed representation for chained updates). Core has no `Function.update`, so `Board.set`
   is the library's own.
2. **`set_comm` is not a simp lemma** (§1). DESIGN §4.3 lists it with the simp lemmas; this spec
   takes it out, because a permutation lemma makes `simp`'s normal form depend on term order.
3. **Equality is decided by comparing squares**, through Basic's `Square` quantifier: 64
   comparisons, no normal form needed. `Position` compares its three small fields before the board.
4. **One code table.** `Piece.code` is the table; `Piece.ofCode` searches `Piece.all` for a code, so
   the inverse is not a second copy that could disagree. Measured cost (scratch, `decide +kernel`,
   five comparisons of a 64-square literal board after two `set`s): about 55 ms per comparison with
   the search, about 35 ms with a hand-written 13-arm `match` on `Fin 16`. The search is kept:
   speed is the last priority, and a board comparison is a small part of a certificate node, which
   also generates moves. **Fallback**, if the DESIGN §7.4 benchmarks show board reads dominate: add
   the `match` as `Piece.ofCode`'s new body and prove the old one equal to it by `decide`; no other
   definition or proof changes.
5. **Codes 1–12 in `Kind.all` order** (DESIGN §4.3), so that 13–15 form one unused block and the
   white codes are python-chess's piece types. The prototype's colour-bit codes (white 1–6, black
   9–14) are not kept: nothing in this layer tests a colour bit, and the fast layer will use
   bitboards, not nibbles.
6. **Hexadecimal digits by division.** `hexDigit n i = n / 16 ^ i % 16` is "digit `i` in base 16",
   so a packed literal *is* the board read square by square from the right of the hex numeral. The
   division form is what core's `Nat` lemmas talk about (P2.6), and the kernel accelerates division
   and powers exactly as it does shifts (*lean-eng* §2). Digit `i` belongs to the square with
   `index` `i` (LERF, Basic D3.2), the same numbering the fast layer will use, so there is one
   numbering for every seam. The cost is that within a rank the literal reads from the h-file to the
   a-file; generated literals are not meant to be read (DESIGN §4.3).
7. **`pack` through a list, not by recursion on 64.** `ofHexDigits` is a `foldr` over a list, and its
   two lemmas (P2.6, P2.7) are plain inductions; `Board.pack` is `ofHexDigits` of the 64 square
   codes in index order. Proofs need only `unpack_pack`, which is all DESIGN §4.3 needs; `pack_lt`
   is there so that `pack`'s docstring states nothing unproved.
8. **Moves are UCI data and print as UCI.** `Option PromoKind` makes "promote to a king" unwritable.
   The hand-written `Repr` is a display change only (review C5 of Basic). The whole-type quantifier
   instances exist for DESIGN §5.6 and have low priority (review C1).
9. **Castling rights: four flags behind `get`.** Four `Bool`s keep equality structural and cheap;
   the `get` interface keeps statements indexed by colour and wing, so R6's swap is one lemma and
   not four. By convention rights are changed only by `revoke` and `revokeAll`, both `≤` their
   input, and there is no `grant`; this is what makes R8 provable for every move, once `play` is
   shown to use only these two (D4.1's interface rule, which Lean does not enforce). Because the type has 16 values, a whole-type quantifier
   (D4.7) turns every lemma about rights into a `decide`.
10. **`CastlingRights.full`, not `.all`**, because `T.all` is the list of a finite type's values
    (R2); **`CastlingRights.none`** as DESIGN names it.
11. **The initial board is computed, not listed.** One table of eight kinds (`backRankKind`, the
    FIDE 2.3 order a chess player recognizes) and `relRank` for colour. There are no 32 placement
    lines to proofread, and the colour symmetry is a theorem (P5.10). The packed literal of the
    initial board appears only as a test, never as the definition: a hex numeral cannot be checked
    by reading.
12. **`Position` is plain data with `@[ext]`.** No invariants, no proof fields, no clocks (DESIGN
    §4.6). Its `Inhabited` value is the initial position, so a `default` position is at least a real
    one. **The `default` values disagree on purpose**, and nobody should "fix" one to match another:
    `default : Board` is the empty board (the neutral board, as `Board.empty` is the neutral thing
    to `set` into), while `(default : Position).board` is the initial board; `default :
    CastlingRights` (derived) is `CastlingRights.none`, while the initial rights are `full`. No
    proof reads a `default`.
13. **Display is separate and untrusted; notation is trusted.** Display may use `match` with string
    literals freely; nothing in the specification reads it. The letters, `Move.toUCI` and
    `CastlingRights.letters` are notation that the FEN/UCI guards read, hence trusted (§6).

---

## 9. Not in this module, and open items

Not here, on purpose:
- **Parsers** (FEN, UCI): `Chess.ChessGame` (DESIGN §8.6). `Kind.letter` and `CastlingRights.letters`
  are the tables a parser should invert, by searching `Kind.all` the way `ofCode` searches
  `Piece.all`, so that letters too are written once.
- **Board predicates** such as "empty" or "holds a piece of colour `c`": `Chess.Rules` decides
  whether to name them. In this module `b s = none` is the idiom.
- **Counting material** (`Position.men`, `pawns`, `budget`, R7): Stage 2, `Chess/Invariants.lean`.
- **R6 flips**, deferred to Stage 2 with their home here: `Board.flip b := fun s => (b s.flip).map
  fun pc => ⟨pc.color.other, pc.kind⟩` (with Basic's planned `Square.flip`),
  `CastlingRights.swap cr` with `(cr.swap).get c w = cr.get c.other w`, `Move.flip`,
  `Position.flip`, each with a `_flip_flip` involution lemma. P5.10 becomes
  `Board.initial.flip = Board.initial`.
- **`WellFormed`, `Reachable`, `normalize`**: Stage 2 and Stage 4.

Open items for the translator, the critic and the owner:
0. ~~THEOREMS edits requested.~~ Made in Round 4 (`docs/process/Position.md`): (a) R2's English
   lists `Color`, `Kind`, `PromoKind`, `Wing`, `Square`, `Piece` as enumerated types, and says
   `Move` and `CastlingRights` have the decidable quantifiers only (header). (b) R8 is
   unconditional, `(p.play m).castling ≤ p.castling` for every `m` (D4.8). (c) R6's hazard reads
   `p.castling = CastlingRights.none`, and its "Forces" reads `get c w`. Also §0.5's sketch now
   says `CastlingRights` and `Option PromoKind`, and R4 no longer lists `set_comm` as `@[simp]`.
1. **P2.8 belongs in `Basic`** (`Square.getElem?_all_index`, next to `Square.mem_all`). Stated here
   because this spec may not edit `Basic`; move it when `Basic` is next revised.
2. **Square literals** (Basic review C4, `sq!e4`): tests here use `⟨file, rank⟩` with comments.
   An owner decision; if a literal elaborator is added, §7 is rewritten with it.
3. ~~`get_revoke_of_ne` versus one unconditional equation.~~ Settled (Round 4): both. The readable
   forms P4.4–P4.7 stay, and P4.8 adds `get_revoke` and `get_revokeAll`, not `@[simp]`, because
   R9.3's preservation needs the converse direction (D4.8 notes).
4. ~~`Board.initial` with `Option.or` or a `match`.~~ Settled (Round 2): `Option.or`, with a
   docstring that states the meaning, not the mechanism (D5.5).
5. **Whether `Move` should derive `Repr`** as DESIGN §4.1 says, with UCI printing as `ToString`
   only. The draft follows Basic's review C5 (UCI `Repr`), because `#eval` uses `Repr`.
6. **`CastlingRights.none` and the name hazard** of D4.5. Keeping DESIGN's name costs an
   `Option.none` in the few declarations inside the `CastlingRights` namespace. Renaming it (for
   example `CastlingRights.empty`, by analogy with `Board.empty`) removes the hazard but changes a
   name DESIGN and THEOREMS (R6) use. **The Round 1 critic recommends `CastlingRights.empty`**,
   parallel to `Board.empty`, with DESIGN §4.5 and THEOREMS R6 updated to match, and **the Round 4
   critic agrees**, having confirmed the hazard (D4.5). Since Round 4 `letters` no longer needs
   `Option.none`, so the only cost of keeping the name is the hazard for later modules. The
   translation keeps `none` (the name its task assigns) until the owner decides; the rename is
   mechanical.
7. **`Basic` additions that would simplify this module** (Round 4 critique; not made here, since
   this module may not edit `Basic`):
   (a) a low-priority `Option.decidableForall` and `Option.decidableExists` (with their two `rfl`
   tests), after which both `Move` instances of D3.2 become field-wise one-liners like D4.7's,
   `decidable_of_iff (∀ s t o, P ⟨s, t, o⟩) ⟨fun h m => h m.1 m.2 m.3, fun h _ _ _ => h _⟩`.
   Core 4.28 has no `Decidable (∀ o : Option α, P o)` (checked).
   (b) `Square.flip` (Basic §10 already plans it) and `Piece.flip` (colour swap), after which P5.10
   reads `Board.initial s.flip = (Board.initial s).map Piece.flip`, and R6 reuses both.

---

## 10. Checklist for the translator

- Module docstring `/-! # Position … -/` with `## Main definitions` (`Board`, `Board.set`,
  `Piece.code`/`Piece.ofCode`, `Board.pack`/`Board.unpack`, `Move`, `CastlingRights` with `get`,
  `revoke`, `revokeAll`, `none`, `full` and `≤`, `Position`, `Position.initial`), `## Main
  statements` (`set_same`, `set_ne`, `set_comm`; `unpack_pack`; `revoke_le`, `revokeAll_le` (R8);
  `get_revoke`, `get_revokeAll`; the `Board.initial` sanity theorems), and `## Implementation
  notes` summarizing §8 items 1, 4, 6 and 9, the orientation of `set_ne` (§1) and the `ext s : 1`
  advice (D1.2).
- Section order: Boards; Piece codes and packed boards; Moves; Castling rights; Positions; Notation; Display;
  Tests. Each spec section is a `/-! ## … -/` heading. Its lemmas, which need a `variable` line,
  sit in a Lean scope: `namespace Board` (§1 lemmas, after `Board.set`), `section PackedBoards`
  (§2 lemmas), `namespace CastlingRights` (all of D4.2–D4.8 and the §4 lemmas, so they are written
  `get`, `revoke_le`, …), and `section InitialPosition` (§5 lemmas). Declarations whose names start
  with another namespace (`Piece.code`, `Square.getElem?_all_index`, `Board.initial`) are written
  with the full name, not by reopening that namespace. Inside `namespace CastlingRights` the
  lemmas still write `CastlingRights.none` in full, for the reader (D4.5).
- `import Chess.Basic` only. Add `import Chess.Position` to `Chess.lean`.
- Every `def`, `instance`, structure field and `theorem` carries the docstring above. Nothing is
  `sorry`; no `native_decide`.
- `@[simp]` exactly where the tables say. Not simp: `set_apply`, `set_comm`, `unpack_apply`,
  `hexDigit_ofHexDigits`, `ofHexDigits_lt`, `hexDigit_pack`, `pack_lt`, `get_revoke_of_ne`,
  `get_revokeAll_of_ne`, `get_revoke`, `get_revokeAll`, `le_def`.
- Every whole-type quantifier instance has `priority := low` and its two `rfl` tests.
- Lines at most 100 characters. The diagram `#guard` of §7 is split with Lean string gaps (a `\`
  at the end of a line inside a string literal, which also drops the next line's leading spaces).
- No test sweeps all moves (`∀ m : Move`, about 4 s).
- Inside `namespace CastlingRights` and `CastlingRights.…` declarations, `Option.none`, never bare
  `none` (D4.5); better, write the code so that it needs neither (D6.6).
- Record in `docs/process/Position.md` every place where the Lean forced the English to change.
