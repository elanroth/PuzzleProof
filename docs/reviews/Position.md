# File-level design review: `Chess.Position`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/Position.lean` (whole file), `docs/spec/Position.md` (whole file),
`docs/process/Position.md` (Rounds 1–4), `Chess/Basic.lean` (declaration outline),
`docs/reviews/Basic.md`, `docs/DESIGN.md` (§1–§5, §7.4, §8.2, §10–§12), and `docs/THEOREMS.md`
(R4, R6, R8–R10, M7, M10, M11, C3, C5, C6, G16).

State at review time: `lake build` green; `lake env lean Chess/Position.lean` gives no warnings; no
`sorry`, no `native_decide`. 677 lines, 47 definitions and instances, 54 theorems. All 112 Lean
docstrings appear word for word in the spec (checked by script, whitespace-insensitive). The longest
line is 100 characters.

**No change was made to the Lean, the spec or the process log in this review.** The file had no
defect small enough to fix in place. Every finding below is a recommendation. The experiments behind
them were run in scratch files outside the library.

---

## 1. Verdict

**Faithful and readable. Build on it, but take two decisions before `Rules` is written (C1, C2).**

What is right and should not change:

- **One writer, `Board.set`, with the frame lemmas in the right shape.** `set_ne` takes `t ≠ s` (the
  square read first), and `simp` uses it in that orientation only, as the spec says. `set_comm` is
  deliberately not `@[simp]`. Everything R4 needs is here.
- **One code table.** `Piece.ofCode` searches `Piece.all`, so it cannot disagree with `Piece.code`.
  The fallback (swap in a `match`, proved equal by `decide`) is written down.
- **Packed literals are notation, not the representation.** `unpack_pack` is the only theorem
  proofs use, and `pack_lt` and `hexDigit_pack` back every claim in `pack`'s docstring. I checked
  the initial-board literal by hand (a1–h1 `4 2 3 5 6 3 2 4`, a8–h8 `A 8 9 B C 9 8 A`) and the
  python-chess correspondence (white codes are `piece_type`, black codes are `piece_type + 6`).
- **Castling rights behind `get`/`revoke`/`revokeAll`, with an order.** The type has 16 values, so
  each lemma about rights is a one-line `decide`. R8 is stated unconditionally. `get_revoke` and
  `get_revokeAll` give R9.3 the converse direction it needs.
- **`Position` is plain data with `@[ext]`.** `Position.decEq` compares the three small fields
  before the board, and `instDecidableAnd` short-circuits, so unequal positions are usually told
  apart without reading the board. `Position.initial` is computed from `backRankKind` and `relRank`,
  with a colour-symmetry sanity theorem, rather than being a literal.
- **Faithful chess.** I checked the en passant convention (the PGN standard records the target after
  every double push; Stockfish and python-chess's default do not), the castling-flag semantics (FIDE
  3.8.2.1 plus the FEN rook-capture convention), the queen-on-own-colour theorem, the FEN/UCI
  letters and the diagram. I found no errors.
- **Kernel behaviour is fine.** I ran chains of conditional board updates (the shape `play` will
  have) under `decide +kernel`. The cost grows linearly: 81, 172, 275 and 436 ms for 2, 3, 4 and 8
  steps. The kernel's whnf cache shares the repeated condition evaluations. DESIGN §7.4's
  checkpoint pattern works as designed (the e4 test).

---

## 2. Concerns, in priority order

### C1 (high, owner decision before `Rules`). A function board loses sharing in compiled code: conditional updates become exponential

This is the one design choice here that will be painful to change later.

**Finding (measured).** `Board` unfolds to a function type. A definition whose result is a `Board`
and whose body is an `if` or `match` is compiled with the square as an extra argument
(eta-expansion). The condition is then **re-evaluated on every square read**. If the condition
reads a board, as `play`'s steps do, each layer multiplies the cost of every later read. That
cost is exponential in the number of layers.

Reproducer (scratch file, run with `#eval`, interpreted):

```lean
def sweep (b : Board) : Nat := Square.all.foldl (fun acc s => acc + (contentsCode (b s)).val) 0
def expCond (b : Board) : Bool := sweep b != 12345          -- any condition that reads the board
def stepIf (b : Board) : Board := if expCond b then b.set ⟨0, 2⟩ none else b
-- reading the board after n steps (one sweep):
--   n = 2:  278 ms      n = 3:  ≈ 18 s      (≈ 64× per step)
-- `let c := expCond b; if c then … else b` behaves the same (≈ 18 s at n = 3), and so does
-- moving the condition into the written value,
-- `b.set ⟨0, 2⟩ (if expCond b then none else b ⟨0, 2⟩)` (n = 2: 276 ms; n = 3 did not finish
-- in 120 s): `Board.set` is inlined, and the value ends up under the same lambda.
```

The same step written so that no `Board`-valued conditional is left to the compiler stays linear:

| Shape of the step | 30 steps |
|---|---|
| `Position → Position`, with the `if` inside `{ p with board := if … }` | 16 ms |
| a one-field wrapper `structure WBoard where get : Square → Option Piece`, same `if` | 12 ms |
| a `Board`-valued helper with no conditional (`(b.set src none).set dst (b src)`) | linear (11 ms for 20 helper calls) |

A second instance of the hazard: `let b := if compact then Board.unpack b.pack else b` in an `IO`
block recomputed `pack` on every read, **6949 ms against 11 ms** for 1280 reads. Wrapping the board
in the one-field structure brought it back to 11 ms.

**Why it matters here.** DESIGN §5.5 says each step of `play` is "a named function on boards or
positions". The natural Lean for step 2 is
`def … (b : Board) : Board := if m.IsEnPassant p then b.set victim none else b`, and step 3 has the
same shape. Each conditional reads `p.board` two or three times. After `d` plies every read then
costs roughly `4^d` to `5^d` reads, so DESIGN §5.7's generator-against-`Legal` tests and THEOREMS
M7's `_native` perft at depth 4–5 would hit it, and so would any compiled search. The kernel route
(`decide +kernel`, certificates) is **not** affected (§1), so the problem would first show up as
"native perft is inexplicably slow". It would not show up in any proof.

**Options.**

1. **Make `Board` a one-field structure** (recommended if the owner accepts the change in how goals
   print):
   `structure Board where get : Square → Option Piece`, plus
   `instance : CoeFun Board (fun _ => Square → Option Piece) := ⟨Board.get⟩`. The source keeps
   writing `b s`, which elaborates to `b.get s`, and goals print `b.get s`. A `Board`-valued `if`
   is then a value, and the compiler cannot eta-expand it. The cost: `Board.ext` takes
   `∀ s, b.get s = b'.get s`, `Board.set`, `empty`, `unpack` and `initial` gain an anonymous
   constructor, and the proofs about them need a `Board.get` simp lemma or two. Generic
   `Pi` instances already cannot apply (the reason `Board` is a `def`), and `DecidableEq` stays
   hand-written. About 30 lines of `Position.lean` and spec §1, §2, §5 change. **Do it now or not
   at all.** After `Rules` and `MoveGen` exist, every statement that applies a board moves too.
2. **Keep the `def` and adopt a convention**, written into DESIGN §5.5 and the `Rules` spec:
   *no definition whose result type is `Board` computes anything from a board except through
   `set`'s fall-through.* Any conditional, and any value read off a board, is computed in a
   function that returns `Position`, and the board is built in that structure's field. (Moving the
   condition into `set`'s value does **not** help; that variant was measured in the reproducer
   above.) Add a compiled regression test that times perft depth 3 from the initial position. The
   cost: the rule is subtle (the safe and unsafe forms look almost the same), the types do not
   enforce it, and a later contributor can break it without noticing.

Both options keep `b s` in the English and in statements. My recommendation is **option 1**,
because it removes the hazard by construction rather than by a rule that the types do not enforce.
The measurements make option 2 look more fragile than it first appears. Option 2 is acceptable only
if the owner strongly prefers `b s` to `b.get s` in goals.

### C2 (high, owner decision before `Rules`). Rename `CastlingRights.none` to `CastlingRights.empty`

The spec (D4.5, §9 item 6) and both critics recommend this, and I agree. I re-confirmed the hazard
from a later module's point of view:

```lean
namespace Chess.CastlingRights
def firstHeld? (cr : CastlingRights) : Option Wing :=
  if cr.whiteKingside then some .kingside else none   -- error: `none` has type CastlingRights
end Chess.CastlingRights
```

`Rules` (rights updates), `Invariants` (R10: "rights only where the initial rights allow") and the
FEN parser (`-` means no rights) will all write code near this namespace. The rename is mechanical
today: one definition, two lemma names (`get_none`, `none_le`), two `#guard`s, DESIGN §4.5 and
THEOREMS R6. After those modules are written it touches every one of them. `empty` also matches
`Board.empty`.

### C3 (medium, before `ChessGame`). The "untrusted display" letters become trusted once the parsers use them

Spec §9 says the FEN and UCI parsers should invert `Kind.letter` and `CastlingRights.letters` by
search, so that letters are written once. That is the right design, but it moves `Kind.letter`,
`Piece.letter`, `PromoKind.letter`, `CastlingRights.letters`, `Move.toUCI` and `Square.name` into
the trusted base (DESIGN §3.1: the parsers are trusted until M11), while the file's heading still
says "Display (untrusted: nothing in the specification reads it)". When `ChessGame` is written:

- split the section into **Notation** (the letter tables and `toUCI`, trusted, with sanity
  lemmas by `decide`: `Kind.letter` injective, `Piece.letter` injective, `PromoKind.letter`
  injective, and `Kind.letter k ≠ '.'`) and **Display** (`rankLine`, `diagram`, the `Repr`
  instances, still untrusted);
- or keep the parsers' tables separate and accept the duplication. That contradicts DESIGN
  Principle 5's "one table", so I do not recommend it.

No change is needed now. The heading must not stay as it is once a parser reads a letter.

### C4 (medium, for `Game` and certificates C5/C6). A one-number key for positions is already almost free

THEOREMS C5 and C6 need finite maps from positions to entries that "the kernel can evaluate", and a
compiled search wants a hash. With a function board, every equality test reads 64 squares on each
side. But `pack` is injective, which follows in two lines from `unpack_pack` (checked):

```lean
example (b b' : Board) (h : b.pack = b'.pack) : b = b' := by
  rw [← Board.unpack_pack b, h, Board.unpack_pack]
```

So when `Game` or the C6 checker needs it, add `Board.pack_inj : b.pack = b'.pack ↔ b = b'` and a
`Position.key : Position → Nat` (the packed board shifted past one bit for the turn, four for the
rights and seven for `epTarget`), with `key_inj`. A map keyed by `key` compares one bignum per probe
instead of 64 reads, and `Hashable Position` can hash the key. This agrees with THEOREMS C5:
equality still decides membership, and the hash only indexes. One caveat: `pack` of a board that is
not a literal still costs 64 reads, once per position.

### C5 (medium). Name the normalization that `unpack_pack` already proves

`Board.unpack b.pack` is equal to `b` and is a flat board. In compiled code, reading a board after
200 `set`s cost 108 ms per 20 sweeps, against 11 ms after this compaction. A named
`Board.compact b := Board.unpack b.pack` with `@[simp] compact_eq : b.compact = b` would serve
compiled game replay (PGN, perft drivers) at zero proof cost. The kernel checkpoints of DESIGN §7.4
already compact this way, through their literals. Under option 2 of C1, `compact` must never sit
inside a `Board`-valued `if` (the 6949 ms case above). Under option 1 it may.

### C6 (low). Square literals are still `⟨4, 3⟩ -- e4`

Basic review C4 (`sq!e4`) is still open, and this file's tests and the checkpoint pattern multiply
the problem. Checkpoint generators will emit thousands of these. Decide before `Rules` adds its
test positions.

### C7 (low). Top-level helper names in `namespace Chess`

`hexDigit`, `ofHexDigits`, `contentsCode`, `backRankKind`, `startingPiece` and
`startingPiece_white_or_black` sit directly in `Chess`. The spec says `hexDigit` and `ofHexDigits`
are plumbing used only in §2. The fast layer will define its own bit and nibble helpers, and FEN
code will want its own digit readers. To keep the root namespace for chess vocabulary, put them in
namespaces: `Board.hexDigit` or a `Packed` namespace for the first three, `Board.backRankKind` and
`Board.startingPiece` for the others (they exist only to define `Board.initial`). The renames are
mechanical and can wait for the next revision of this module.

### C8 (low). Register the order with core's order classes

Core 4.28 has `Std.Refl`, `Std.Antisymm`, `Std.IsPreorder` and `Std.IsPartialOrder` (checked).
`le_refl`, `le_trans` and `le_antisymm` are already proved, so an
`instance : Std.IsPartialOrder CastlingRights` costs a few lines and lets generic order lemmas and
tactics apply to R8 chains. This is optional, because the `Trans` instance already makes `calc`
work.

### C9 (low, already recorded). Items carried from the spec

- `Square.getElem?_all_index` belongs in `Basic` next to `Square.mem_all` (spec §9 item 1).
- `Option.decidableForall`/`decidableExists` in `Basic` would turn the two `Move` instances into
  one-liners (spec §9 item 7a).
- `Square.flip` and `Piece.flip` in `Basic`, then the R6 flips with their home here (spec §9).
- Tests at the end of the module (Basic review C8): move them to a test library when it exists.

---

## 3. Checked and accepted (not concerns)

- **`Board` as a `def` rather than an `abbrev`.** Dot notation (`b.set`), application, `funext`
  and the named `DecidableEq` all work, and `#synth DecidableEq Position` returns `Position.decEq`
  and `BEq Board` comes from it. (If C1's option 1 is taken, this note is superseded.)
- **`@[ext]` on `Board.ext` and `CastlingRights.ext_get`.** Both generate `_iff` forms
  (`Board.ext_iff`, `CastlingRights.ext_get_iff`). `Position.ext_iff` and `Move.ext_iff` exist.
- **Low-priority whole-type instances for `Move` and `CastlingRights`.** Each has its two `rfl`
  tests (Basic review C1's convention is followed).
- **No root-level `le_refl` or `le_trans` in core**, so `CastlingRights.le_refl` and the others
  shadow nothing.
- **The `default` values disagree on purpose** (empty board, initial position, no rights), and spec
  §8 item 12 says no proof reads a `default`.
- **`epTarget` is unconstrained and set after every double push.** FIDE identity is handled by
  `normalize` (G16), and checkpoint generators must use python-chess `fen(en_passant="fen")`
  (DESIGN §7.4). Both are documented in the right places.
- **`R2` only in part for `Move` and `CastlingRights`** (quantifiers, no `all` list). This is
  justified and recorded in THEOREMS.
- **The `Piece.ofCode` search cost** (about 55 ms against 35 ms per kernel board comparison).
  Keep the search, and keep the `match` fallback, as the spec says.

---

## 4. Summary of recommendations

| # | Priority | Action | Who, when |
|---|---|---|---|
| C1 | high | One-field `structure Board` with `CoeFun` (or the documented convention that `Board`-valued defs compute nothing from a board, plus a compiled perft timing test) | owner, **before `Rules`** |
| C2 | high | Rename `CastlingRights.none` to `CastlingRights.empty`; update DESIGN §4.5, THEOREMS R6 | owner, **before `Rules`** |
| C3 | medium | Split Display into trusted Notation (with injectivity lemmas) and untrusted Display | `ChessGame` author |
| C4 | medium | `Board.pack_inj`, `Position.key`, `key_inj`, `Hashable Position` | `Game` / C6 author |
| C5 | medium | `Board.compact` with `compact_eq` | `MoveGen` author |
| C6 | low | `sq!e4` square literals (Basic C4) | owner |
| C7 | low | Namespace the helper names | next `Position` revision |
| C8 | low | `Std.IsPartialOrder CastlingRights` | optional |
| C9 | low | Spec §9 carry-overs (move P2.8 to `Basic`, `Option` quantifiers, flips, test library) | next `Basic` revision |
