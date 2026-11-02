# Specification of `Chess.Rules`

Role: English specification writer (Round 1); revised by the translator (Rounds 2 and 3) and the
refiner (Round 4).
Date: 2026-11-01.
Status: Round 4. The English was revised against the Round 1 critique (Round 2), against the Lean
translation in `Chess/Rules.lean` (Round 3), and against the Lean critique (Round 4);
`docs/process/Rules.md` logs all three. The Lean file follows this document definition by
definition and builds. Snippets marked *(checked)* were elaborated before the translation; every
lemma tagged [core] or [sanity] is now proved in the library, and of the [later] lemmas only L4.6
and L4.11 are not in the Lean file. IDs with a letter suffix (D2.5a, L2.6a, …) were inserted in
Round 4; no existing ID was renumbered.

File: `Chess/Rules.lean`. Depends on: `Chess.Position` (and through it `Chess.Basic`); core only.
Refines DESIGN §5 (all of it) and §8.3. Theorem targets: **R4** (frame lemmas), **R5** (square
colour), **R8** (castling rights only disappear), **R11** (terminal positions). It also lays the
foundations, with the shapes they need, of **R3** (attack symmetry; `Reaches` reads only squares
strictly between), **R7** (`Move.IsCapture`), **R9** (`Legal`'s second half), **M4**/**M5** (the
six rule predicates) and **G1** (`play_turn`).

This module is the trusted heart of the library: a chess player should be able to check every
definition in sections 2–6 against the FIDE Laws by reading its docstring, and a Lean user should be
able to check the Lean against the docstring.

## 0. How to read this document

The conventions of `docs/spec/Basic.md` §0 and `docs/spec/Position.md` §0 apply unchanged:

- Each definition has an ID (`D2.3`), its Lean name and type, its Lean body, and a **docstring** in
  quotation marks; the Lean docstring is that text, word for word.
- Each lemma has an ID (`L2.4`; `L` because `R` is taken by THEOREMS), an English statement, the
  Lean statement, and a tag: **[core]** (later modules or proofs here depend on it), **[sanity]**
  (checks that a definition says what the English says), or **[later]** (shaped now, proved when a
  Stage 2 theorem needs it; the translator may skip it). The Lean docstring of a lemma is its
  English column. Bold in the English column marks a headline lemma in this document only.
- Tables are in proof order, which is also the order in the Lean file.
- **Binding rule.** Every name a docstring mentions is bound in the signature before the colon, or
  introduced by the docstring itself ("for some `i`", "for each wing `w`").
- `autoImplicit = false`. Each section opens with the `variable` line it needs. A lemma meant to be
  *applied* to particular values (`play_turn p m`) binds them explicitly.
- `@[simp]` is written on every lemma that carries it; a lemma whose cell does not say `@[simp]`
  does not carry it.
- Everything lives in `namespace Chess`; names are given without the prefix. "Basic B6.7" and
  "Position D4.2" refer to `docs/spec/Basic.md` and `docs/spec/Position.md`.
- **Ranks.** "Rank N" (1 to 8) is the chess name. A 0-based value is written as code:
  `s.relRank c = 1` is "`c`'s second rank", `s.relRank c = 7` is "`c`'s last rank".
- **Absent squares.** `o.bind b`, for `o : Option Square`, is *what stands on the square `o`*: `none`
  if `o` is off the board or the square is empty. So `(s.shift d j).bind b = none` reads "the square
  `j` steps from `s` in direction `d` is empty (or off the board)". Every place this idiom is used,
  the square is provably on the board, and the docstring says "is empty".
- **"Of colour `c`".** `b s = some ⟨c, k⟩` reads "`s` holds a piece of colour `c` and kind `k`".
  `b.colorAt s = some c` reads "`s` holds a piece of colour `c`" (D1.1). `b.colorAt s ≠ some c`
  reads "`s` does not hold a piece of colour `c`", that is, it is empty or holds a piece of the
  other colour: FIDE 3.1 word for word.
- **The position before the move.** In every definition about a move `m` in a position `p`, every
  condition is read in `p`, the position *before* the move. `play` never inspects a half-built
  position (§5, design choice 7). The one test read after the move is `Legal`'s (D6.1), which is
  FIDE 3.9.2's own wording ("expose or leave its own king under attack").
- **Shape and rule.** A *shape* (§3) says what a move looks like and reads no more than that; a
  *rule* (§4) says whether it is allowed. A lemma whose hypothesis is a shape is stated about "a
  move with the shape of …", never about "a capture" or "castling", and needs no pseudo-legality
  hypothesis.
- **"A king of colour `c`".** Nothing in this module assumes a side has exactly one king (that is
  `WellFormed`, R9). Docstrings say "a king of colour `c`", "no king of colour `c`", never "the
  king", except in the castling rules, where the king is the one on `kingHome c`. "Colour `c` has no
  king" is `¬ b.HasKing c` (D2.5a).

Letters used in this module:

- `p q` positions; `m` a move; `c c'` colours; `w w'` wings; `k` a kind; `pc` a piece; `b` a
  board; `x` the contents of a square (`Option Piece`).
- `s t u` squares: `s` where a piece stands, `t` a target, `u` a square in between.
- `d` a direction; `i j` numbers of steps (`Nat`); `df dr` steps in files and ranks (`Int`).
- `l l'` lists of writes (`List (Square × Option Piece)`); `wr` one write.

FIDE references are to the Laws of Chess effective 1 January 2023, as in Basic §0:
3.1 (no move onto a piece of one's own colour; capture), 3.1.2–3.1.3 (attack on an opponent's
piece, including by a piece that may not move there), 3.2–3.4 (bishop, rook, queen), 3.5 (they may
not move over intervening pieces), 3.6 (knight), 3.7.1 (pawn push), 3.7.2 (double push from its original square), 3.7.3
(pawn capture), 3.7.3.1–3.7.3.2 (en passant, only on the next move), 3.7.3.3 (promotion), 3.8.1
(king step), 3.8.2 (castling), 3.8.2.1 (right lost), 3.8.2.2 (castling prevented temporarily),
3.9.1 (check, even by a pinned piece), 3.9.2 (no move may expose or leave one's king in check),
5.1.1 (checkmate), 5.2.1 (stalemate).

## Contents of the file, in order

1. Board helpers: `Board.colorAt`, `Board.kindAt`, `Board.setMany`.
2. Reaching and attacking: `Slides`, `Reaches`, `Board.AttacksFrom`, `Board.Attacked`,
   `Board.KingAttacked`, `Board.HasKing`, `InCheck`.
3. Shapes of moves: `Move.IsEnPassant`, `Move.IsCastle`, `Move.IsDoublePush`, `Move.epVictim`,
   `Move.PromotionRule`, `Move.IsCapture`.
4. Movement rules: `StepMove`, `PushMove`, `DoublePushMove`, `PawnCaptureMove`, `EnPassantMove`,
   `Position.CanCastle`, `CastleMove`, `PseudoLegal`.
5. Playing a move: the six steps and `Position.play`.
6. Legality and terminal positions: `Legal`, `Checkmate`, `Stalemate`.
7. What a move changes (R4, R8).
8. Sanity theorems (R5 and the promotion promise).
9. Terminal positions (R11).
10. Tests.

Sections 11–13 of this document are the design choices, the open items and the translator's
checklist.

---

## 1. Section "Board helpers"

**D1.1 `Board.colorAt (b : Board) (s : Square) : Option Color`.** *(checked)*
```lean
def Board.colorAt (b : Board) (s : Square) : Option Color := (b s).map (·.color)
```
Docstring: "The colour of the piece on `s`, or `none` if `s` is empty."

**D1.2 `Board.kindAt (b : Board) (s : Square) : Option Kind`.** *(checked)*
```lean
def Board.kindAt (b : Board) (s : Square) : Option Kind := (b s).map (·.kind)
```
Docstring: "The kind of the piece on `s`, or `none` if `s` is empty."

These two give the rules their two most frequent phrases: "`s` holds a piece of colour `c`"
(`b.colorAt s = some c`) and, in R5, "`s` holds a bishop" (`b.kindAt s = some .bishop`).

**D1.3 `Board.setMany (b : Board) (l : List (Square × Option Piece)) : Board`.** *(checked)*
```lean
def Board.setMany (b : Board) (l : List (Square × Option Piece)) : Board :=
  l.foldl (fun b wr => b.set wr.1 wr.2) b
```
Docstring: "The board `b` after the writes `l`, made in order: each write, a pair of a square and
its new contents, makes that square hold those contents, and a later write to a square replaces an
earlier one."

A *write* is a pair of a square and its new contents. `play` describes what a move does to the board
as a list of writes (§5); `setMany` is the only place they are carried out, through `Board.set`,
the only writer of boards (Position D1.5).

Lemmas (`variable {b : Board} {l : List (Square × Option Piece)} {s t : Square} {pc : Piece}
{x : Option Piece}`; all in `namespace Board`):

| ID | English | Lean | Tag |
|---|---|---|---|
| L1.1 | If `s` holds `pc`, the colour on `s` is `pc`'s colour. | `@[simp] theorem colorAt_of_eq_some (h : b s = some pc) : b.colorAt s = some pc.color` | core |
| L1.2 | If `s` holds `pc`, the kind on `s` is `pc`'s kind. | `@[simp] theorem kindAt_of_eq_some (h : b s = some pc) : b.kindAt s = some pc.kind` | core |
| L1.3 | No writes leave the board as it is. | `@[simp] theorem setMany_nil (b : Board) : b.setMany [] = b` | core |
| L1.4 | Writing a list that starts with `wr` is making the write `wr`, then the rest. | `@[simp] theorem setMany_cons (b : Board) (wr : Square × Option Piece) (l : List (Square × Option Piece)) : b.setMany (wr :: l) = (b.set wr.1 wr.2).setMany l` | core |
| L1.5 | Writing two lists one after the other is writing them one at a time. | `theorem setMany_append (b : Board) (l l' : List (Square × Option Piece)) : b.setMany (l ++ l') = (b.setMany l).setMany l'` | core |
| L1.6 | **A square that no write mentions keeps its contents.** | `theorem setMany_of_not_mem (h : t ∉ l.map (·.1)) : b.setMany l t = b t` | core |
| L1.6a | If the writes `l` write no square twice, a square that `l` writes holds what was written there. | `theorem setMany_of_mem (hnd : (l.map (·.1)).Nodup) (h : (t, x) ∈ l) : b.setMany l t = x` | core |
| L1.7 | After the writes `l`, a square holds what it held before or what some write in `l` put there. | `theorem setMany_eq_or_mem (b : Board) (l : List (Square × Option Piece)) (t : Square) : b.setMany l t = b t ∨ (t, b.setMany l t) ∈ l` | core |

Proofs (all checked): L1.1–L1.2 `simp [colorAt, h]`; L1.3–L1.4 `rfl`; L1.5 `List.foldl_append ..`;
L1.6 by induction on `l` generalizing `b`, with `simp only [List.map_cons, List.mem_cons, not_or]
at h` and `rw [setMany_cons, ih h.2, Board.set_ne h.1]`. L1.6 is the whole of R4's frame argument
(L7.7). L1.6a, by induction on `l` generalizing `b`: `List.nodup_cons` splits `hnd`; if `(t, x)` is
the head, L1.6 on the tail and `Board.set_same`; otherwise the induction hypothesis. With L7.7a it
says what every written square holds after a pseudo-legal move, one write at a time. `setMany_append` is not `@[simp]`: the R4 proofs split the write list at chosen points.
L1.7 by induction on `l` generalizing `b`, applying the induction hypothesis to `b.set wr.1 wr.2`
and splitting `Board.set_apply`; it is what L9.7 needs ("a move creates no piece that was not
written").

---

## 2. Section "Reaching and attacking"

**D2.1 `Slides (d : Direction) (b : Board) (s t : Square) : Prop`.** *(checked)*
```lean
def Slides (d : Direction) (b : Board) (s t : Square) : Prop :=
  ∃ i < 8, 0 < i ∧ s.shift d i = some t ∧ ∀ j < i, 0 < j → (s.shift d j).bind b = none
```
Docstring: "A piece sliding from `s` in direction `d` on board `b` reaches `t`: for some number of
steps `i` from 1 to 7, `t` is the square `i` steps from `s` in direction `d`, and for every `j` with
`0 < j < i` the square `j` steps from `s` is empty. So it reaches every square along `d` up to and
including the first occupied one. Only the squares strictly between `s` and `t` are read; `t` itself
may be empty or occupied (FIDE 3.5)."

Notes.
- *Index form* (DESIGN §5.2), not a prefix of `s.ray d`: R3's symmetry is then arithmetic through
  Basic's `shift_eq_some_iff_opposite` and `shift_eq_shift_opposite` (the square `j` steps from `s`
  is the square `i − j` steps back from `t`). The generator's ray form is linked in Stage 2 (M1).
- `i < 8` makes the quantifier bounded, hence decidable (`Nat.decidableExistsLT`); it costs nothing,
  since eight steps always leave the board (Basic `shift_eq_none_of_eight_le`; L2.1 states the
  unbounded form). `0 < i` excludes `t = s`.
- `∀ j < i, 0 < j → …` is decided by core's `Nat.decidableBallLT`. The order of the binders matters:
  `∀ j, 0 < j → j < i → …` is not matched by that instance.
- "The square `j` steps away is empty" is `(s.shift d j).bind b = none`, which eliminates the
  `Option` without a quantifier over the 64 squares (DESIGN §10, first open item, settled here).
  For `0 < j < i` that square is on the board (Basic `isSome_shift_of_le`), so "or off the board"
  never applies.

Instance *(checked)*:
```lean
instance Slides.decidable (d : Direction) (b : Board) (s t : Square) :
    Decidable (Slides d b s t) := by
  unfold Slides; infer_instance
```
Docstring: "Sliding is decided by trying each number of steps from 1 to 7 and checking the squares
in between."

**D2.2 `Reaches (k : Kind) (c : Color) (b : Board) (s t : Square) : Prop`.** *(checked)*
```lean
def Reaches (k : Kind) (c : Color) (b : Board) (s t : Square) : Prop :=
  match k with
  | .pawn   => s.offset (-1) c.forward = some t ∨ s.offset 1 c.forward = some t
  | .knight => ∃ j ∈ knightJumps, s.offset j.1 j.2 = some t
  | .king   => ∃ d : Direction, s.shift d 1 = some t
  | .bishop | .rook | .queen => ∃ d ∈ k.slideDirections, Slides d b s t
```
Docstring: "A piece of kind `k` and colour `c` would reach `t` from `s` on board `b`, whatever
actually stands on `s`: a pawn the squares diagonally forward (at most two), a knight the squares a
knight's jump away, a king the adjacent squares (up to eight), and a bishop, rook or queen every
square along one of its directions up to and including the first occupied one. En passant aside,
these are the squares the piece could capture on. What stands on `s` and on `t` is not read, and
neither are pins (FIDE 3.1.3, 3.2–3.4, 3.6, 3.7.3, 3.8.1, 3.9.1)."

Notes.
- All six kinds are listed; the three sliders share one arm through Basic's `Kind.slideDirections`,
  so a queen is visibly "rook or bishop" (Basic `mem_slideDirections_queen`). In that arm `k` is the
  matched constructor, so `simp only [Reaches]` on `Reaches .bishop …` produces
  `∃ d ∈ Kind.bishop.slideDirections, …` (checked: `Reaches .bishop c b s t ↔ ∃ d ∈
  Direction.diagonals, Slides d b s t` is `Iff.rfl`).
- Pawns, knights and kings do not read `b` at all. `c` matters only for pawns.
- *Reach is hypothetical.* `Reaches` does not look at `s`, so the same relation serves for "the
  piece on `s` attacks `t`" (D2.3) and for the super-piece method of R3.3 ("a knight placed on the
  king's square would reach `s`"). "Attacks" is kept for D2.3 and D2.4.
- *Any target.* Unlike FIDE 3.1.2, the target need not hold an opponent's piece: it may be empty or
  hold a piece of either colour. This wider relation is the one 3.9 needs (a king may not capture a
  defended piece, that is, one its own side reaches).
- Pawn pushes are not attacks; they are `PushMove` (D4.2).
- En passant captures are not attacks here, and the docstrings of D2.2 and D2.4 say so (FIDE 3.1.2
  counts them). They never matter for check, since the victim is always a pawn, never a king, and
  never for castling, since the crossed square is on the home rank, never an en passant target.
- Pawn diagonals are written `s.offset (∓1) c.forward`, with `Color.forward` an `Int`, as Basic
  has it. If the owner adopts Basic review C2 (`Color.pawnDirection : Direction`), this arm and the
  four pawn rules of §4 change locally (§12, item 3).

Instance *(checked)*: `instance Reaches.decidable (k : Kind) (c : Color) (b : Board) (s t : Square)
: Decidable (Reaches k c b s t) := by cases k <;> unfold Reaches <;> infer_instance`.
Docstring: "Reaching is decided kind by kind."

**D2.3 `Board.AttacksFrom (b : Board) (s t : Square) : Prop`.** *(checked)*
```lean
def Board.AttacksFrom (b : Board) (s t : Square) : Prop :=
  match b s with
  | none    => False
  | some pc => Reaches pc.kind pc.color b s t
```
Docstring: "The piece on `s` attacks `t`: `s` is not empty and the piece standing there reaches
`t`."
The kind is read off the board, not quantified over (DESIGN §5.3). Instance *(checked)*:
`by unfold Board.AttacksFrom; split <;> infer_instance`, docstring "Whether the piece on `s`
attacks `t` is decided by reading `s` and then deciding `Reaches`."

**D2.4 `Board.Attacked (b : Board) (c : Color) (t : Square) : Prop`.** *(checked)*
```lean
def Board.Attacked (b : Board) (c : Color) (t : Square) : Prop :=
  ∃ s, b.colorAt s = some c ∧ b.AttacksFrom s t
```
Docstring: "Square `t` is attacked by colour `c`: some square holds a piece of colour `c` that
attacks `t`. En passant captures are not counted; they never capture a king."
Decided by Basic's `∃` over squares (64 squares, never kinds or pieces). Instance *(checked)*:
`by unfold Board.Attacked; infer_instance`, docstring "Whether `t` is attacked is decided by
looking at every square."

**D2.5 `Board.KingAttacked (b : Board) (c : Color) : Prop`.** *(checked)*
```lean
def Board.KingAttacked (b : Board) (c : Color) : Prop :=
  ∃ s, b s = some ⟨c, .king⟩ ∧ b.Attacked c.other s
```
Docstring: "A king of colour `c` is attacked: some square holding a king of colour `c` is attacked
by the other colour. False on a board with no king of colour `c`."
No king finder, no sentinel (DESIGN §4.6; the prototype's `findKing` returned 64). With two kings of
colour `c` it says "one of them"; `WellFormed` (Stage 2) excludes that. Instance *(checked)*, same
shape, docstring "Whether a king of colour `c` is attacked is decided by looking at every
square."

**D2.5a `Board.HasKing (b : Board) (c : Color) : Prop`.** *(checked, Round 4)*
```lean
def Board.HasKing (b : Board) (c : Color) : Prop :=
  ∃ s, b s = some ⟨c, .king⟩
```
Docstring: "Colour `c` has a king on board `b`: some square holds a king of colour `c`."
Names the hypothesis of the kingless-side lemmas (L2.9, L9.4–L9.8), which Round 3 wrote out as
`∀ s, b s ≠ some ⟨c, .king⟩` five times; `WellFormed` (R9) will use it too. Instance
`Board.HasKing.decidable` by `unfold; infer_instance`, docstring "Whether colour `c` has a king is
decided by looking at every square."

**D2.6 `InCheck (p : Position) : Prop`.** *(checked)*
```lean
def InCheck (p : Position) : Prop := p.board.KingAttacked p.turn
```
Docstring: "The side to move is in check: a king of the side to move is attacked (FIDE 3.9.1)."
Instance *(checked)*: `by unfold InCheck; infer_instance`, docstring "Whether the side to move is in
check is decided on the board." There is no `inCheck : Position → Bool`: the executable test is
`decide (InCheck p)` (DESIGN §2).

Lemmas (`variable {k : Kind} {c : Color} {b b' : Board} {s t u : Square} {d : Direction}
{x : Option Piece} {pc : Piece}`, in a `section Reaching`):

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.1 | Sliding needs no bound on the number of steps: `t` is reached exactly when it is a positive number of steps away, with every square strictly between `s` and `t` empty. | `theorem slides_iff : Slides d b s t ↔ ∃ i, 0 < i ∧ s.shift d i = some t ∧ ∀ j < i, 0 < j → (s.shift d j).bind b = none` | core |
| L2.2 | A pawn reaches the squares diagonally forward (at most two). / A knight reaches the squares a knight's jump away. / A king reaches the adjacent squares (up to eight). / A bishop reaches what it slides to diagonally. / A rook reaches what it slides to along files and ranks. / A queen reaches what it slides to in any direction. | `theorem reaches_pawn : Reaches .pawn c b s t ↔ s.offset (-1) c.forward = some t ∨ s.offset 1 c.forward = some t` / `theorem reaches_knight : Reaches .knight c b s t ↔ ∃ j ∈ knightJumps, s.offset j.1 j.2 = some t` / `theorem reaches_king : Reaches .king c b s t ↔ ∃ d : Direction, s.shift d 1 = some t` / `theorem reaches_bishop : Reaches .bishop c b s t ↔ ∃ d ∈ Direction.diagonals, Slides d b s t` / `theorem reaches_rook : Reaches .rook c b s t ↔ ∃ d ∈ Direction.orthogonals, Slides d b s t` / `theorem reaches_queen : Reaches .queen c b s t ↔ ∃ d ∈ Direction.all, Slides d b s t` | core |
| L2.3 | **No piece reaches its own square.** | `theorem reaches_ne (h : Reaches k c b s t) : t ≠ s` | core |
| L2.4 | **Only the squares strictly between `s` and `t` are read: two boards that agree on every square other than `s` and `t` give the same answer.** / What stands on the attacker's square is not read. / What stands on the target square is not read. | `theorem reaches_congr (h : ∀ u, u ≠ s → u ≠ t → b u = b' u) : Reaches k c b s t ↔ Reaches k c b' s t` / `theorem reaches_set_src : Reaches k c (b.set s x) s t ↔ Reaches k c b s t` / `theorem reaches_set_dst : Reaches k c (b.set t x) s t ↔ Reaches k c b s t` | core |
| L2.5 | If `s` holds `pc`, the piece on `s` attacks `t` exactly when `pc` reaches `t` from `s`. | `theorem attacksFrom_of_eq_some (h : b s = some pc) : b.AttacksFrom s t ↔ Reaches pc.kind pc.color b s t` | core |
| L2.6 | An empty square attacks nothing. | `theorem not_attacksFrom_of_eq_none (h : b s = none) : ¬ b.AttacksFrom s t` | core |
| L2.6a | Square `t` is attacked by colour `c` exactly when some square holds a piece of colour `c` and some kind `k` that reaches `t`. | `theorem Board.attacked_iff : b.Attacked c t ↔ ∃ s k, b s = some ⟨c, k⟩ ∧ Reaches k c b s t` | core |
| L2.7 | On the empty board no king is attacked. | `theorem not_kingAttacked_empty (c : Color) : ¬ Board.empty.KingAttacked c` | core |
| L2.8 | One direction of `slides_symm`: a slide from `s` to `t` is a slide back from `t` to `s`. / Sliding is symmetric: a slider on `s` reaches `t` in direction `d` exactly when one on `t` reaches `s` in the opposite direction. | `theorem Slides.symm (h : Slides d b s t) : Slides d.opposite b t s` / `theorem slides_symm : Slides d b s t ↔ Slides d.opposite b t s` | later (R3), proved |
| L2.9 | A board with no king of colour `c` has no attacked king of colour `c`. | `theorem not_kingAttacked_of_not_hasKing (h : ¬ b.HasKing c) : ¬ b.KingAttacked c` | core |

Proofs.
- L2.1 *(checked)*: `→` drops the bound; `←` gets `i < 8` from `Square.shift_eq_none_of_eight_le`
  by contradiction (`Nat.lt_of_not_le fun h8 => by simp [shift_eq_none_of_eight_le h8] at h`).
- L2.2: each is `Iff.rfl` (checked for the bishop).
- L2.3 *(checked)*: `cases k`; pawn by `Square.offset_ne_self (by simp)` on each disjunct (the rank
  step `c.forward` is nonzero); knight by `mem_knightJumps_iff` and `offset_ne_self (by omega)`;
  king and sliders by `rintro rfl` and `Square.shift_ne_self` (with `Nat.one_pos`, resp. `0 < i`).
  Write the cases with `case pawn => …` etc.: after `cases k` the goals come in constructor order
  (pawn, knight, bishop, rook, queen, king), not in the order of the `match`.
- L2.4 *(checked)*: `reaches_congr` by `cases k <;> simp only [Reaches, Slides] <;> try exact
  Iff.rfl`, which closes the leapers and pawns; for sliders, congruence down to the in-between square
  (`exists_congr`, `and_congr_right`, `forall_congr'`), then `cases hu : s.shift d j`: `u ≠ s` from
  `Square.shift_ne_self`, `u ≠ t` from `Square.steps_eq_of_shift_eq` (`u` is `j < i` steps away,
  `t` is `i`), and `h`. The two `set` lemmas are one line each:
  `reaches_congr fun _ hu _ => Board.set_ne hu`, resp. `fun _ _ hu`. `reaches_congr` is the precise
  content of DESIGN §5.2's bold sentence, and the form R3, R6 and R9 will use; tagged [core] since
  Round 4 (Round 3 had the two `set` lemmas only, [sanity], with the same proof written twice).
- L2.6a *(checked)*: `→` reads the piece on `s` (`cases hs : b s`; `none` contradicts L2.6, `some pc`
  gives `pc.color = c` from `colorAt` and the reach from L2.5); `←` by L1.1 and L2.5. This is
  THEOREMS R3's definition of "attacked"; `Attacked` keeps reading the kind off the board for speed
  (design choice 3), and proofs about attacks start from this lemma instead of unfolding `colorAt`,
  `AttacksFrom` and its `match`.
- L2.5–L2.6 *(checked)*: `simp [Board.AttacksFrom, h]`.
- L2.7 *(checked)*: `simp [Board.KingAttacked]` (`Board.empty_apply`). L2.7 and L2.9 check
  nothing about attacks (there is no king to attack); they are the facts the terminal lemmas L9.4
  and L9.5 need. The positive sanity checks of `KingAttacked` are tests (§10, "Attack geometry"):
  a lone black rook on e8 attacks the white king on e1, and a piece on e4 blocks it.
- L2.8: from Basic `shift_eq_some_iff_opposite` and `shift_eq_shift_opposite`: the square `j` steps
  from `t` towards `s` is the square `i − j` steps from `s`, and `0 < i − j < i`. One direction is
  proved as `Slides.symm` (with `Nat.sub_sub_self` to turn `i − (i − j)` back into `j`); the `iff`
  is `⟨Slides.symm, fun h => by simpa using h.symm⟩`, the `simpa` removing
  `d.opposite.opposite`.
- L2.9: `fun ⟨s, hs, _⟩ => h ⟨s, hs⟩`.

---

## 3. Section "Shapes of moves"

DESIGN Principle 6: a chess concept that two definitions need is one named predicate. En passant
and castling are needed by the rules (§4) and by `play` (§5); so is the double push (for the en
passant target). Throughout, `p.turn` is "the side to move", written `c` in the English.

**D3.1 `Move.IsEnPassant (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def Move.IsEnPassant (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ p.epTarget = some m.dst ∧ p.board m.dst = none ∧
    m.src.file ≠ m.dst.file
```
Docstring: "Move `m` has the shape of an en passant capture in `p`: it moves a pawn of the side to
move to the en passant target, which is empty, changing file. Whether it is allowed is
`EnPassantMove`."
Written `m.IsEnPassant p` (dot notation fills the `Move` argument). `dst` empty is what keeps a
pawn capture onto an occupied target square (possible only in a malformed position) from being
treated as en passant, so a pseudo-legal capture removes one piece (R7). The file condition keeps a
straight push onto the target (again only in a malformed position) from removing a pawn.

**D3.2 `Move.IsCastle (p : Position) (w : Wing) (m : Move) : Prop`.** *(checked)*
```lean
def Move.IsCastle (p : Position) (w : Wing) (m : Move) : Prop :=
  m.src = kingHome p.turn ∧ p.board m.src = some ⟨p.turn, .king⟩ ∧
    m.dst = kingCastleSquare p.turn w
```
Docstring: "Move `m` has the shape of castling to wing `w` in `p`: the side to move's king goes from
its home square to its castling square on wing `w` (e1g1, e1c1, e8g8, e8c8). Whether it is allowed
is `CastleMove`."

**D3.3 `Move.IsDoublePush (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def Move.IsDoublePush (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.src.offset 0 (2 * p.turn.forward) = some m.dst
```
Docstring: "Move `m` has the shape of a pawn's two-square advance in `p`: it moves a pawn of the
side to move two squares straight forward. Whether it is allowed is `DoublePushMove`."
`2 * p.turn.forward` matches Basic B6.7a (`relRank_of_offset_forward`, with `dr := 2`). This
predicate is new relative to DESIGN §5.4; design choice 6. Among pseudo-legal moves, exactly the
double pushes have this shape (L4.7), so step 5 sets a target after a pseudo-legal move exactly
when it is a double push.

**D3.4 `Move.epVictim (m : Move) : Square`.** *(checked)*
```lean
def Move.epVictim (m : Move) : Square := ⟨m.dst.file, m.src.rank⟩
```
Docstring: "The square of the pawn an en passant capture `m` removes: on `m.dst`'s file and
`m.src`'s rank, beside the capturing pawn."

**D3.5 `Move.PromotionRule (c : Color) (m : Move) : Prop`.** *(checked)*
```lean
def Move.PromotionRule (c : Color) (m : Move) : Prop :=
  m.promo ≠ none ↔ m.dst.relRank c = 7
```
Docstring: "The promotion rule for a pawn move `m` by colour `c`: `m` names a promotion choice
exactly when it ends on `c`'s last rank. A pawn reaching the last rank must promote (FIDE
3.7.3.3)."
Used by the two pawn rules that can reach the last rank (`PushMove`, `PawnCaptureMove`). The other
four rules require no promotion choice (`m.promo = none`), so no other move names one. Together they
keep the promise of Position D3.1's `promo` field docstring, in both directions (L8.3).

**D3.6 `Move.IsCapture (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def Move.IsCapture (p : Position) (m : Move) : Prop :=
  p.board m.dst ≠ none ∨ m.IsEnPassant p
```
Docstring: "Move `m` is a capture in `p`: its destination holds a piece, or it captures en
passant."
Not used by the rules; it is DESIGN §5.5's definition, placed here for R7 (Stage 2) and for the
certificate tools.

Each of D3.1, D3.2, D3.3, D3.5, D3.6 gets an instance `X.decidable` by
`by unfold X; infer_instance` *(checked)*, with a docstring that names its predicate (hover text
has no "this"): "Whether `m` has the shape of an en passant capture is decided by reading the
position.", "Whether `m` has the shape of castling to `w` is decided by reading the position.",
"Whether `m` has the shape of a double push is decided by reading the position.", "Whether the
promotion rule holds is decided by comparing two facts.", "Whether `m` is a capture is decided by
reading the position."

Lemmas (`variable {p : Position} {m : Move} {w w' : Wing}`):

| ID | English | Lean | Tag |
|---|---|---|---|
| L3.1 | A move has the shape of castling to at most one wing. | `theorem Move.IsCastle.wing_eq (h : m.IsCastle p w) (h' : m.IsCastle p w') : w = w'` | core |
| L3.2 | A move with the shape of en passant does not have the shape of castling. | `theorem Move.IsEnPassant.not_isCastle (h : m.IsEnPassant p) (w : Wing) : ¬ m.IsCastle p w` | core |
| L3.3 | For a move with the shape of en passant, the victim square is not the source square. | `theorem Move.IsEnPassant.epVictim_ne_src (h : m.IsEnPassant p) : m.epVictim ≠ m.src` | core |

Proofs *(all checked)*: L3.1 `have := h.2.2.symm.trans h'.2.2` (equal castling squares), then
`revert this; cases p.turn <;> cases w <;> cases w' <;> decide` (Basic has no
`kingCastleSquare_inj`; §12 item 5). L3.2: `intro hc; have := h.1.symm.trans hc.2.1; simp at this`
(a pawn is not a king). L3.3: `fun e => h.2.2.2 (congrArg Square.file e).symm` (the files differ).

---

## 4. Section "Movement rules"

One named, decidable predicate per FIDE rule, joined by a disjunction (DESIGN §5.4, Stage 1
decision 5). Each reads `p` only; `c` in the English is `p.turn`, the side to move. The conjuncts
are ordered with the cheap reads first, the colour and kind of the source square leading.

**D4.1 `StepMove (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def StepMove (p : Position) (m : Move) : Prop :=
  ∃ k, k ≠ .pawn ∧ p.board m.src = some ⟨p.turn, k⟩ ∧ Reaches k p.turn p.board m.src m.dst ∧
    p.board.colorAt m.dst ≠ some p.turn ∧ m.promo = none
```
Docstring: "A step move is any non-pawn move other than castling: a knight, bishop, rook, queen or
king of the side to move goes from `m.src` to a square it reaches, which does not hold a piece of its
own colour; no promotion choice (FIDE 3.1, 3.2–3.6, 3.8.1)."
"Step" is the piece's own step, which for a slider is a slide of any length. `∃ k` ranges over the six kinds (Basic's `Kind.decidableExists`); only the kind actually on `m.src`
passes the second conjunct, so one `Reaches` is evaluated. The king's ordinary step is here;
castling is `CastleMove`.

**D4.2 `PushMove (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def PushMove (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.src.offset 0 p.turn.forward = some m.dst ∧
    p.board m.dst = none ∧ m.PromotionRule p.turn
```
Docstring: "A pawn of the side to move goes one square straight forward to an empty square, and
promotes exactly when that square is on the last rank (FIDE 3.7.1, 3.7.3.3)."

**D4.3 `DoublePushMove (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def DoublePushMove (p : Position) (m : Move) : Prop :=
  m.IsDoublePush p ∧ m.src.relRank p.turn = 1 ∧
    (m.src.offset 0 p.turn.forward).bind p.board = none ∧ p.board m.dst = none ∧ m.promo = none
```
Docstring: "A pawn of the side to move on its second rank goes two squares straight forward; the
square it passes over and the square it lands on are both empty; no promotion choice (FIDE 3.7.2)."
"On its original square" (FIDE) is read as "on the side's second rank": a pawn on that rank has
never moved, since pawns move only forward.

**D4.4 `PawnCaptureMove (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def PawnCaptureMove (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ Reaches .pawn p.turn p.board m.src m.dst ∧
    p.board.colorAt m.dst = some p.turn.other ∧ m.PromotionRule p.turn
```
Docstring: "A pawn of the side to move captures a piece of the other colour diagonally forward, and
promotes exactly when it lands on the last rank (FIDE 3.7.3, 3.7.3.3)."

**D4.5 `EnPassantMove (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def EnPassantMove (p : Position) (m : Move) : Prop :=
  m.IsEnPassant p ∧ Reaches .pawn p.turn p.board m.src m.dst ∧ m.dst.relRank p.turn = 5 ∧
    p.board m.epVictim = some ⟨p.turn.other, .pawn⟩ ∧
    (m.dst.offset 0 p.turn.forward).bind p.board = none ∧ m.promo = none
```
Docstring: "A pawn of the side to move captures en passant: it moves diagonally forward onto the en
passant target, which is empty and lies on its sixth rank; a pawn of the other colour stands on the square
beside the capturing pawn on the target's file (the victim square); the square that pawn would have
come from, one square further forward than the target from the capturer's side, is empty; no
promotion choice (FIDE 3.7.3.1–3.7.3.2)."
This encodes "the enemy pawn has just advanced two squares" as far as one position can (DESIGN
§5.4): the target is on the right rank (`relRank 5` for the capturer is the passed-over square of
the opponent's double push), the victim is a pawn of the other colour beside the capturer, and the
target and the square the victim would have come from are both empty. So a hand-written target can
only produce a capture that *some* previous double push would explain; whether that double push was
itself legal (it might have left its own king in check) is `WellFormed`'s business (R9), and
whether it was actually played is outside the position: FIDE 3.7.3.2 ("only on the move immediately after") is enforced by
`play`, which clears the target after every move that is not a double push (D5.9). The pawn's
`Reaches` makes the file condition of `IsEnPassant` redundant here; it is kept there for `play`.
"The target is empty" comes from `m.IsEnPassant p`; since Round 4 the docstring says so.

**D4.6a `Position.CanCastle (p : Position) (w : Wing) : Prop`.** *(checked, Round 4)*
```lean
def Position.CanCastle (p : Position) (w : Wing) : Prop :=
  p.castling.get p.turn w = true ∧ p.board (rookHome p.turn w) = some ⟨p.turn, .rook⟩ ∧
    (∀ s ∈ betweenKingAndRook p.turn w, p.board s = none) ∧
    ¬ InCheck p ∧ ¬ p.board.Attacked p.turn.other (rookCastleSquare p.turn w)
```
Docstring: "The side to move may castle to wing `w` now, as far as the position before the move
decides: it still holds that castling right; its rook stands on its home square on wing `w`; every
square between king and rook is empty; the side to move is not in check; and the square the king
crosses is not attacked by the other colour (FIDE 3.8.2.1, 3.8.2.2). The square the king lands on
is tested by `Legal`."
FIDE's own split: the right (3.8.2.1) and "castling is prevented temporarily" (3.8.2.2), both
independent of the move. A move generator and a FEN validator want exactly this predicate. Instance
`Position.CanCastle.decidable` by `unfold; infer_instance`, docstring "Whether the side to move may
castle to `w` is decided by reading the position."

**D4.6 `CastleMove (p : Position) (w : Wing) (m : Move) : Prop`.** *(checked)*
```lean
def CastleMove (p : Position) (w : Wing) (m : Move) : Prop :=
  m.IsCastle p w ∧ p.CanCastle w ∧ m.promo = none
```
Docstring: "The side to move castles to wing `w`: its king moves from its home square to its
castling square (`Move.IsCastle`), castling to `w` is allowed now (`Position.CanCastle`), and the
move names no promotion choice (FIDE 3.8.2)."
Notes (DESIGN §5.4).
- All preconditions are stated, including the king and rook on their home squares, so castling never
  relies on `WellFormed`.
- "The square the king is to occupy is not attacked" is not repeated: it is `Legal`'s second half.
- Emptiness uses all squares between king and rook (`betweenKingAndRook`, Basic D7.6); attack uses
  only the square crossed (`rookCastleSquare`). So on the queenside b1 must be empty but may be
  attacked, as FIDE says (test in §10).
- *When the attack tests are read.* FIDE 3.8.2.2 states all three tests (home square, crossed
  square, landing square) on the position before the move. Here the home square (`¬ InCheck p`) and
  the crossed square are tested in `p`, with the king still on its home square, and the landing
  square after the move, by `Legal`, with the king on it, the rook on the crossed square and the
  home square empty. The two readings agree. The other colour's pieces do not move, so only a
  bishop, rook or queen attack can differ, and only through a square that castling changes: the
  king's home square and the rook's home square (emptied) and the crossed square (filled). Of the
  lines through the king's home square (its rank, its file, its two diagonals) and the crossed
  square, only the home rank reaches the landing square, and an attacker on the home rank beyond
  the king's home square would attack the king there, which `¬ InCheck p` rejects; on the rook's
  side every square between king and rook is empty before the move and after it. The rook's home
  square is a corner, so no line runs through it to the landing square. (Round 3's wording, "the
  only lines … run along the home rank", overlooked the file and diagonals that emptying the king's
  home square opens; they miss the landing square.) This is the one place where the Lean does not
  say literally what FIDE says, so it is stated as L4.11 [later], to be proved before the module is
  called final.
- Since Round 4 the move-independent conditions are one predicate, `Position.CanCastle` (D4.6a), and
  `CastleMove` is "shape, permission, no promotion choice".

**Instance for `CastleMove`: hand-written, guarded by the shape** *(checked)*:
```lean
instance CastleMove.decidable (p : Position) (w : Wing) (m : Move) :
    Decidable (CastleMove p w m) :=
  if h : m.IsCastle p w then
    decidable_of_iff (p.CanCastle w ∧ m.promo = none) (and_iff_right h).symm
  else isFalse fun hc => h hc.1
```
Docstring: "Castling is decided by checking the shape of the move first, so that the attack tests
run only for the king's two castling moves."
Measured reason (design choice 9): with the derived instance (`by unfold CastleMove;
infer_instance`) the compiled decision evaluated `InCheck p` for every candidate move, not only for
`e1g1`-shaped ones: deciding `PseudoLegal` for all 20 480 candidate moves of the initial position
took **36 s** interpreted; with this instance, **0.46 s**. The kernel route (`decide`) is not
affected either way. Round 4 narrowed the cause down (it is still not explained inside the
compiler): deciding "castles to some wing" for all 20 480 candidates of the initial position takes
under 0.1 s with this instance, 0.19 s with a derived instance for `IsCastle ∧ CanCastle ∧ promo =
none`, and **35 s** with a derived instance for `IsCastle ∧ InCheck p`. So the eager evaluation
happens when an attack test is a *direct* conjunct of a derived `∧` instance; wrapped in its own
predicate it is evaluated only when needed. `Legal`'s derived instance short-circuits (the 20
legal moves of the initial position are found in 0.47 s, against 0.46 s for `PseudoLegal`; the
post-move test alone, for every candidate, takes 22 s). The guard is kept: it costs two lines and
does not depend on that compiler behaviour.

**D4.7 `PseudoLegal (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def PseudoLegal (p : Position) (m : Move) : Prop :=
  StepMove p m ∨ PushMove p m ∨ DoublePushMove p m ∨ PawnCaptureMove p m ∨ EnPassantMove p m ∨
    ∃ w, CastleMove p w m
```
Docstring: "Move `m` obeys the movement rules for the side to move in `p` (FIDE 3.1–3.8), ignoring
whether its own king is attacked afterwards: it is a step, a push, a double push, a pawn capture, an
en passant capture, or castling to some wing."
`rcases h with h | h | h | h | h | ⟨w, h⟩` gives the case split an inductive would. A capture of a
king is not excluded (DESIGN §5.4, §6.4).

Instances for D4.1–D4.5 and D4.7: `X.decidable` by `by unfold X; infer_instance` *(checked)*,
with docstrings naming the rule: "Whether `m` is a step move is decided by reading the position.",
"Whether `m` is a push is decided by reading the position.", "Whether `m` is a double push is
decided by reading the position.", "Whether `m` is a pawn capture is decided by reading the
position.", "Whether `m` is an en passant capture is decided by reading the position."; D4.7:
"Whether `m` is pseudo-legal is decided rule by rule."

Lemmas (`variable {p : Position} {m : Move} {k : Kind} {w : Wing}`, in a `section Movement`):

| ID | English | Lean | Tag |
|---|---|---|---|
| L4.1 | **A pseudo-legal move moves a piece of the side to move.** | `theorem PseudoLegal.colorAt_src (h : PseudoLegal p m) : p.board.colorAt m.src = some p.turn` | core |
| L4.2 | A pseudo-legal move does not stay on its square. | `theorem PseudoLegal.dst_ne_src (h : PseudoLegal p m) : m.dst ≠ m.src` | core |
| L4.3 | A pseudo-legal pawn move changes rank. | `theorem PseudoLegal.rank_ne_of_pawn (h : PseudoLegal p m) (hp : p.board m.src = some ⟨p.turn, .pawn⟩) : m.dst.rank ≠ m.src.rank` | core |
| L4.4 | A pseudo-legal move of a piece that is neither a pawn nor a king is a step move. | `theorem PseudoLegal.stepMove_of_kindAt (h : PseudoLegal p m) (hk : p.board.kindAt m.src = some k) (hp : k ≠ .pawn) (hking : k ≠ .king) : StepMove p m` | core |
| L4.5 | A pseudo-legal move does not land on a piece of the mover's own colour. | `theorem PseudoLegal.colorAt_dst_ne (h : PseudoLegal p m) : p.board.colorAt m.dst ≠ some p.turn` | sanity |
| L4.6 | A move obeys at most one of the six rules, and castles to at most one wing. | one lemma per pair, e.g. `theorem StepMove.not_pushMove (h : StepMove p m) : ¬ PushMove p m` | later (M5) |
| L4.7 | A pseudo-legal move has the shape of a double push exactly when it is a double push. | `theorem PseudoLegal.isDoublePush_iff (h : PseudoLegal p m) : m.IsDoublePush p ↔ DoublePushMove p m` | core |
| L4.8 | A pseudo-legal move has the shape of an en passant capture exactly when it is one. | `theorem PseudoLegal.isEnPassant_iff (h : PseudoLegal p m) : m.IsEnPassant p ↔ EnPassantMove p m` | core |
| L4.9 | A pseudo-legal move has the shape of castling to wing `w` exactly when it castles to `w`. | `theorem PseudoLegal.isCastle_iff (h : PseudoLegal p m) : m.IsCastle p w ↔ CastleMove p w m` | core |
| L4.10 | A pseudo-legal move onto a square holding a piece attacks that square. | `theorem PseudoLegal.attacksFrom_dst (h : PseudoLegal p m) (hd : p.board m.dst ≠ none) : p.board.AttacksFrom m.src m.dst` | core |
| L4.11 | A castling move is legal exactly when the square the king lands on is not attacked by the other colour in the position before the move (FIDE 3.8.2.2, read literally). | roughly `theorem CastleMove.legal_iff (h : CastleMove p w m) : Legal p m ↔ ¬ p.board.Attacked p.turn.other (kingCastleSquare p.turn w)`, with a one-king hypothesis if the proof needs one | later (fidelity) |

Proofs.
- L4.1 *(checked)*: `rcases h with ⟨k, -, h, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ |
  ⟨w, ⟨-, h, -⟩, -⟩ <;> simp [h]` (through L1.1). No `unfold` is needed: `rcases` sees through the
  definitions.
- Four `private` helpers open the section, each with a docstring: `Color.forward_ne_zero` ("A
  pawn's rank step is not zero."), `Color.two_mul_forward_ne_zero` ("A pawn's two-square rank step
  is not zero."), `Square.file_eq_of_offset_zero` ("An offset with no file step stays on the
  file.") and `shift_kingHome_one_ne` ("The king's castling square is not one king step from its
  home square.", `revert d; cases c <;> cases w <;> decide`). The first two replace four copies of
  `by cases p.turn <;> decide`; they belong in Basic (§12 item 5).
- L4.2 *(checked)*: `rcases` into the six rules; step, pawn capture and en passant by `reaches_ne`;
  push and double push by `Square.offset_ne_self (.inr (Color.forward_ne_zero _))`, resp.
  `two_mul_forward_ne_zero`; castling by `rw [hs, hd]` and `kingCastleSquare_ne_kingHome`.
- L4.3 *(checked)*: a local `have key : ∀ df dr : Int, dr ≠ 0 → m.src.offset df dr = some m.dst →
  m.dst.rank ≠ m.src.rank` (by `rw [Square.offset_eq_some_iff, e] at ho; omega`), applied in the
  four pawn rules with rank step `p.turn.forward` or `2 * p.turn.forward`; the step and castling
  cases contradict `hp` (the source holds a pawn, not a non-pawn, resp. a king).
- L4.4 *(checked)*: `rcases h with h | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨w, ⟨-, h,
  -⟩, -⟩`; the first case is the goal, the others contradict `hk` (`simp [Board.kindAt, h] at hk`
  gives `.pawn = k` or `.king = k`).
- L4.5: step by its own conjunct; push, double push, en passant because `m.dst` is empty; pawn
  capture because `c.other ≠ c` (`Color.other_ne_self`); castling because `kingCastleSquare` is
  between king and rook (Basic `kingCastleSquare_mem_between`), hence empty. This is FIDE 3.1's
  first sentence, checked against all six rules.
- L4.7: `←` is the first conjunct. `→`: in the five other rules, the shape's rank step `2 *
  p.turn.forward` (with file step 0) clashes with the rule's own step through Basic
  `steps_eq_of_offset_eq`: a push has rank step `p.turn.forward`, a pawn capture and en passant file
  step ±1; a step move and castling have no pawn on `m.src`.
- L4.8 *(checked)*: `←` is the first conjunct. `→`: a step move and castling have no pawn on
  `m.src`; a push and a double push stay on the file (`Square.file_eq_of_offset_zero`), which the
  shape forbids; a pawn capture needs a piece on `m.dst`, which the shape says is empty. R7 needs it
  to know that the en passant victim is really a pawn.
- L4.9 *(checked)*: `←` is the first conjunct. `→`: the four pawn rules need a pawn on `m.src`,
  which holds a king; a king's step is one square and castling moves it two
  (`shift_kingHome_one_ne`); a castling move to `w'` has `w' = w` (L3.1). L4.7–L4.9 are the formal
  content of "`play` and `PseudoLegal` cannot disagree" (D5.3).
- L4.10 *(checked)*: the step and pawn-capture cases by L2.5; the other four rules land on an empty
  square (castling because the castling square is between king and rook). With R9.5 it gives "no
  legal move captures a king" (R9).
- L4.11: not proved. The argument is in D4.6's note "When the attack tests are read".
- L4.6: deferred to Stage 2 with M5. The reasons it holds are recorded in DESIGN §5.4: the source
  kind separates step from pawn moves from castling (a king `StepMove` changes file by one, castling
  by two), and `dst` occupied versus empty separates pawn capture from en passant and pushes.

---

## 5. Section "Playing a move"

`Position.play` is total: it is defined for every move, and theorems say what it does on
pseudo-legal ones (DESIGN §5.5). It is written as **six named steps**. Steps 1–3 say what the move
writes on the board, as lists of writes carried out by `Board.setMany`; steps 4–6 give the other
three fields. **Every step reads only `p`, the position before the move.** So no step depends on
what an earlier step wrote, the order of steps 4–6 is immaterial, and the order of the writes
matters only on squares written twice (by two steps, or by step 1 itself when `m.src = m.dst`),
which never happens for a pseudo-legal move.

**D5.1 Step 1, `Move.pieceWrites (p : Position) (m : Move) : List (Square × Option Piece)`.**
*(checked)*
```lean
def Move.pieceWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  [(m.src, none), (m.dst, (p.board m.src).map (·.promote m.promo))]
```
Docstring: "Step 1 of a move, the piece moves: `m.src` becomes empty, and `m.dst` receives the piece
that stood on `m.src`, whatever its kind, promoted as `m.promo` says. (If `m.src` was empty, `m.dst`
becomes empty.)"
A capture needs no separate write: the captured piece is overwritten. No `movedPiece` helper and no
junk value: the arriving piece is `(p.board m.src).map (·.promote m.promo)`, total.

**D5.2 Step 2, `Move.enPassantWrites (p : Position) (m : Move) : List (Square × Option Piece)`.**
*(checked)*
```lean
def Move.enPassantWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  if m.IsEnPassant p then [(m.epVictim, none)] else []
```
Docstring: "Step 2 of a move, en passant: if `m` has the shape of an en passant capture, the victim
square becomes empty."

**D5.3 Step 3, `Move.castleWrites (p : Position) (m : Move) : List (Square × Option Piece)`.**
*(checked)*
```lean
def Move.castleWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  Wing.all.flatMap fun w =>
    if m.IsCastle p w then
      [(rookHome p.turn w, none), (rookCastleSquare p.turn w, p.board (rookHome p.turn w))]
    else []
```
Docstring: "Step 3 of a move, castling: for each wing `w`, if `m` has the shape of castling to `w`,
whatever stands on the rook's home square on `w` moves to the square the king crosses. (If that
square is empty, the crossed square becomes empty.)"
At most one wing contributes (L3.1). Steps 2 and 3 use the shape predicates of §3, so `play` and
`PseudoLegal` cannot disagree on what counts as en passant or castling (DESIGN §5.5); L4.7–L4.9 state
this formally.

**D5.4 `Move.boardWrites (p : Position) (m : Move) : List (Square × Option Piece)`.** *(checked)*
```lean
def Move.boardWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  m.pieceWrites p ++ m.enPassantWrites p ++ m.castleWrites p
```
Docstring: "Everything move `m` writes on the board, in order: steps 1, 2 and 3."
(`++` associates to the left: this is `(l₁ ++ l₂) ++ l₃`. Round 3 said "to the right", which was
wrong; proofs that split off step 1 use `List.append_assoc` first.)

**D5.5 `Move.touched (p : Position) (m : Move) : List Square`.** *(checked)*
```lean
def Move.touched (p : Position) (m : Move) : List Square := (m.boardWrites p).map (·.1)
```
Docstring: "The squares move `m` writes on: its source and destination, the victim square of an en
passant capture, and the rook's two squares when castling. No other square changes (R4)."
DESIGN §5.5's list, obtained from the writes instead of being written a second time.

**D5.6 `Move.Revokes (m : Move) (c : Color) (w : Wing) : Prop`.** *(checked)*
```lean
def Move.Revokes (m : Move) (c : Color) (w : Wing) : Prop :=
  m.src = kingHome c ∨ m.src = rookHome c w ∨ m.dst = kingHome c ∨ m.dst = rookHome c w
```
Docstring: "Move `m` costs colour `c` its castling right on wing `w`: it leaves or lands on the home
square of `c`'s king or of `c`'s rook on wing `w`. A move of the king or of that rook from home, and
a capture of that rook at home, all do this (FIDE 3.8.2.1); landing on the rook's home square also
revokes the right, so that no other rook arriving there later can be castled with."
This is a rule about squares only; it does not read the board. Design choice 8 explains why it is
faithful and why it replaces DESIGN §5.5 step 4's "if `src` holds a king". Instance
`Move.Revokes.decidable` by `unfold; infer_instance` *(checked)*, docstring "Whether `m` costs a
right is decided by comparing squares."

**D5.7 `CastlingRights.ofGet (f : Color → Wing → Bool) : CastlingRights`.** *(checked)*
```lean
def CastlingRights.ofGet (f : Color → Wing → Bool) : CastlingRights :=
  ⟨f .white .kingside, f .white .queenside, f .black .kingside, f .black .queenside⟩
```
Docstring: "The castling rights given by `f`: for every colour `c` and wing `w`, `c`'s right on `w`
is held exactly when `f c w` is true."
Written by its full name, `def CastlingRights.ofGet`, after Position's `CastlingRights` section,
without reopening the namespace; it uses no `none` (Position D4.5's hazard does not arise). It is a
general constructor and could add rights; `play` uses it only in step 4, whose `&&` can only clear
them. Position's `CastlingRights` docstring ("changed only with `revoke` and `revokeAll`") is
therefore out of date; §12 item 7 asks Position to restate it and to take `ofGet`.

| ID | English | Lean | Tag |
|---|---|---|---|
| L5.1 | The rights built from `f` hold `c`'s right on `w` exactly when `f c w` is true. | `@[simp] theorem CastlingRights.get_ofGet (f : Color → Wing → Bool) (c : Color) (w : Wing) : (CastlingRights.ofGet f).get c w = f c w` | core |

Proof *(checked)*: `cases c <;> cases w <;> rfl`. It sits right after D5.7, before step 4 uses it,
and is the one lemma in §5.

**D5.8 Step 4, `Move.castlingAfter (p : Position) (m : Move) : CastlingRights`.** *(checked)*
```lean
def Move.castlingAfter (p : Position) (m : Move) : CastlingRights :=
  CastlingRights.ofGet fun c w => p.castling.get c w && !decide (m.Revokes c w)
```
Docstring: "Step 4 of a move, castling rights: a right is held after `m` exactly when it was held
before and `m` does not cost it."
It only ever turns rights off, so R8 is two lines (L7.9).

**D5.9 Step 5, `Move.epTargetAfter (p : Position) (m : Move) : Option Square`.** *(checked)*
```lean
def Move.epTargetAfter (p : Position) (m : Move) : Option Square :=
  if m.IsDoublePush p then m.src.offset 0 p.turn.forward else none
```
Docstring: "Step 5 of a move, the en passant target: after a pawn's two-square advance, the square
it passed over; after any other move, none."
Set after **every** double push, whether or not a capture is possible (DESIGN §4.6, Position D5.4's
field docstring). The square passed over is an `Option`, but after a double push it is on the board;
no `get!`.

**D5.10 `Position.play (p : Position) (m : Move) : Position`.** *(checked)*
```lean
def Position.play (p : Position) (m : Move) : Position where
  board    := p.board.setMany (m.boardWrites p)
  turn     := p.turn.other
  castling := m.castlingAfter p
  epTarget := m.epTargetAfter p
```
Docstring: "The position after move `m` in `p`: the board after steps 1–3, the turn passed to the
other side (step 6), the castling rights after step 4, and the en passant target of step 5. Defined
for every move; the theorems say what it does to pseudo-legal ones."
Step 6 is `p.turn.other` itself: unconditional, which is G1's alternation law (L7.1).

---

## 6. Section "Legality and terminal positions"

**D6.1 `Legal (p : Position) (m : Move) : Prop`.** *(checked)*
```lean
def Legal (p : Position) (m : Move) : Prop :=
  PseudoLegal p m ∧ ¬ (p.play m).board.KingAttacked p.turn
```
Docstring: "Move `m` is legal in `p`: it obeys the movement rules, and after it no king of the
mover's colour is attacked (FIDE 3.9.2)."
FIDE 3.9.2 read literally: it covers moving into check, staying in check, and moving a pinned
piece, in one clause. The second half is, for the new position, the "side not to move is not in
check" component of `WellFormed` (R9), and the generator's filter (M4). No `WellFormed` hypothesis
anywhere. Instance `Legal.decidable` by `unfold; infer_instance` *(checked)*, docstring "Whether `m`
is legal is decided by deciding the rules and then playing the move."

**D6.2 `Checkmate (p : Position) : Prop`.** *(checked)*
```lean
def Checkmate (p : Position) : Prop := InCheck p ∧ ∀ m, ¬ Legal p m
```
Docstring: "The side to move is checkmated: it is in check and has no legal move (FIDE 5.1.1)."

**D6.3 `Stalemate (p : Position) : Prop`.** *(checked)*
```lean
def Stalemate (p : Position) : Prop := ¬ InCheck p ∧ ∀ m, ¬ Legal p m
```
Docstring: "The side to move is stalemated: it is not in check and has no legal move (FIDE 5.2.1)."

*Positions without a king.* Since `KingAttacked` asks for *some* attacked king, a side with no king
is never in check (L9.4); for that side every pseudo-legal move is legal (L9.8); it can be
stalemated but never checkmated (L9.5); and the empty board, with either side to move, is
stalemate (L9.6). These are the facts the game layer meets after a king capture (design choice 11).

Both are over `Legal`, not over the generator (DESIGN §5.6). Instances `Checkmate.decidable` and
`Stalemate.decidable` by `unfold; infer_instance` *(checked)*, through Position's
`Move.decidableForall` (64 × 64 × 5 candidates); docstrings "Checkmate is decided by checking every
candidate move." and "Stalemate is decided by checking every candidate move." Measured: deciding
`Checkmate` for Fool's mate by `#guard` takes **1.4 s** interpreted (with D4.6's instance; 78 s
without it). Never by `decide` in the library: the cheap decision is the generator's (M6, Stage 2).

---

## 7. Section "What a move changes (R4, R8)"

Lemmas (`variable {p : Position} {m : Move} {c : Color} {w : Wing} {t : Square}`, in a `section
Play`). The helper lemmas L7.3–L7.6 come first, then R4, then R8.

| ID | English | Lean | Tag |
|---|---|---|---|
| L7.1 | **Playing a move passes the turn, whatever the move.** | `@[simp] theorem play_turn (p : Position) (m : Move) : (p.play m).turn = p.turn.other` | core |
| L7.2 | The board after `m` is the board with `m`'s writes made. / The rights after `m` are those of step 4. / The en passant target after `m` is that of step 5. | `theorem play_board (p : Position) (m : Move) : (p.play m).board = p.board.setMany (m.boardWrites p)` / `theorem play_castling (p : Position) (m : Move) : (p.play m).castling = m.castlingAfter p` / `theorem play_epTarget (p : Position) (m : Move) : (p.play m).epTarget = m.epTargetAfter p` | core |
| L7.3 | For a move without the shape of en passant, step 2 writes nothing. / For a move with the shape of en passant, step 2 clears the victim square. | `theorem Move.enPassantWrites_of_not_isEnPassant (h : ¬ m.IsEnPassant p) : m.enPassantWrites p = []` / `theorem Move.enPassantWrites_of_isEnPassant (h : m.IsEnPassant p) : m.enPassantWrites p = [(m.epVictim, none)]` | core |
| L7.4 | For a move with the shape of castling to no wing, step 3 writes nothing. / For a move with the shape of castling to wing `w`, step 3 moves what stands on that wing's rook home square to the square the king crosses. | `theorem Move.castleWrites_of_forall_not_isCastle (h : ∀ w, ¬ m.IsCastle p w) : m.castleWrites p = []` / `theorem Move.castleWrites_of_isCastle (h : m.IsCastle p w) : m.castleWrites p = [(rookHome p.turn w, none), (rookCastleSquare p.turn w, p.board (rookHome p.turn w))]` | core |
| L7.5 | `t` is touched by `m` exactly when it is the source, the destination, the victim square of a move with the shape of en passant, or one of the rook's two squares of a move with the shape of castling. | `theorem Move.mem_touched : t ∈ m.touched p ↔ t = m.src ∨ t = m.dst ∨ (m.IsEnPassant p ∧ t = m.epVictim) ∨ ∃ w, m.IsCastle p w ∧ (t = rookHome p.turn w ∨ t = rookCastleSquare p.turn w)` | core |
| L7.6 | The square a castling rook lands on is not a king's home square. | `theorem rookCastleSquare_ne_kingHome (c c' : Color) (w : Wing) : rookCastleSquare c w ≠ kingHome c'` | core |
| L7.7 | **(R4) A square that the move does not touch keeps its contents, whatever the move.** | `theorem play_board_of_not_mem (h : t ∉ m.touched p) : (p.play m).board t = p.board t` | core |
| L7.7a | A pseudo-legal move writes no square twice. | `theorem PseudoLegal.touched_nodup (h : PseudoLegal p m) : (m.touched p).Nodup` | core |
| L7.8 | **(R4) After a pseudo-legal move its source square is empty.** / **(R4) After a pseudo-legal move its destination holds the piece from the source, promoted as the move says.** / (R4) After a move with the shape of en passant the victim square is empty. / (R4) After a move with the shape of castling to wing `w` the rook's home square on `w` is empty. / (R4) After a move with the shape of castling to wing `w` the square the king crossed holds what stood on the rook's home square. | `theorem play_board_src (h : PseudoLegal p m) : (p.play m).board m.src = none` / `theorem play_board_dst (h : PseudoLegal p m) : (p.play m).board m.dst = (p.board m.src).map (·.promote m.promo)` / `theorem play_board_epVictim (h : m.IsEnPassant p) : (p.play m).board m.epVictim = none` / `theorem play_board_rookHome (h : m.IsCastle p w) : (p.play m).board (rookHome p.turn w) = none` / `theorem play_board_rookCastleSquare (h : m.IsCastle p w) : (p.play m).board (rookCastleSquare p.turn w) = p.board (rookHome p.turn w)` | core |
| L7.9 | **(R8) After `m`, colour `c` holds its right on wing `w` exactly when it held it before and `m` does not cost it.** / **(R8) Playing any move adds no castling right.** | `theorem get_play_castling : (p.play m).castling.get c w = true ↔ p.castling.get c w = true ∧ ¬ m.Revokes c w` / `theorem castling_play_le (p : Position) (m : Move) : (p.play m).castling ≤ p.castling` | core |

Proofs.
- L7.1 *(checked)*, L7.2: `rfl`. All three L7.2 rows use the folded form (`m.castlingAfter p`,
  `m.epTargetAfter p`), matching "that of step 4/5". `play_board`, `play_castling`, `play_epTarget`
  are not `@[simp]`:
  they are rewritten with on purpose, so that goals keep `p.play m` until a proof chooses to look
  inside.
- L7.3 *(checked)*: `simp [Move.enPassantWrites, h]`.
- L7.4 *(checked)*: `simp [Move.castleWrites, Wing.all, h]` for the first; for the second,
  `have hne : ∀ w', w' ≠ w → ¬ m.IsCastle p w' := fun w' hw h' => hw (h'.wing_eq h)`, then
  `cases w` and in each case `simp [Move.castleWrites, Wing.all, h, hne _ (by decide)]`.
- L7.5 *(checked)*: two local `iff`s, one per optional step, each proved by `by_cases` on the shape
  and L7.3 / L7.4 (with L3.1 to identify the wing):
  `(m.IsEnPassant p ∧ t = m.epVictim) ↔ t ∈ (m.enPassantWrites p).map (·.1)` and
  `(∃ w, m.IsCastle p w ∧ (t = rookHome p.turn w ∨ t = rookCastleSquare p.turn w)) ↔
  t ∈ (m.castleWrites p).map (·.1)`; rewrite with both, then
  `simp [Move.touched, Move.boardWrites, Move.pieceWrites]`.
- L7.6: `cases c <;> cases c' <;> cases w <;> decide` *(checked)*. It belongs in Basic beside
  `kingCastleSquare_ne_kingHome`; stated here because this module may not edit Basic (§12 item 5).
- L7.7 *(checked)*: `Board.setMany_of_not_mem h` (the touched list is the write list's squares by
  definition). This is THEOREMS R4's frame lemma, unconditional.
- L7.7a *(checked)*: after `List.append_assoc`, `List.nodup_append` splits the write squares into
  step 1's and the rest. Step 1's two squares differ (L4.2). The rest is one square (en passant;
  step 3 then writes nothing, L3.2), the rook's two squares (`rookCastleSquare_ne_rookHome`), or
  nothing. Step 1's squares are not among the rest by the `private` helper
  `PseudoLegal.not_mem_rest` ("Steps 2 and 3 of a pseudo-legal move write neither its source nor its
  destination.", hypothesis `t = m.src ∨ t = m.dst`): the victim is on the source's rank but another
  file (L3.3, L4.3), and the king's two squares are neither rook square (Basic
  `kingHome_ne_rookHome`, `kingCastleSquare_ne_rookHome`, `rookCastleSquare_ne_kingCastleSquare`,
  L7.6). In the castling case keep the whole `IsCastle` hypothesis (`obtain ⟨w, hw⟩`, then `hw.1`,
  `hw.2.2`): destructuring it with `-` drops the king-on-source fact that `castleWrites_of_isCastle`
  needs. R7's counting argument needs L7.7a too.
- L7.8 `play_board_src` and `play_board_dst` *(checked)*: one line each,
  `Board.setMany_of_mem h.touched_nodup (by simp [Move.boardWrites, Move.pieceWrites])` (L1.6a with
  L7.7a; the membership is step 1's write). Round 3 proved them through a second helper
  (`play_board_of_not_mem_rest`), now gone.
  - `play_board_epVictim` *(checked)*: step 3 writes nothing (L3.2, L7.4), and the victim is
    step 2's write: `rw [play_board, Move.boardWrites, Move.castleWrites_of_forall_not_isCastle
    (h.not_isCastle ·), Move.enPassantWrites_of_isEnPassant h]`, then
    `simp [Board.setMany_append]`. No `PseudoLegal` hypothesis is needed.
  - `play_board_rookHome` and `play_board_rookCastleSquare`: step 2 writes nothing (L3.2), step 3 is
    L7.4's two writes, and `rookCastleSquare_ne_rookHome`. No `PseudoLegal` hypothesis is needed.
- L7.9 *(checked)*: `get_play_castling` by `simp [Position.play, Move.castlingAfter]` (through
  `CastlingRights.get_ofGet`, a `@[simp]` lemma proved by `cases c <;> cases w <;> rfl` right after
  D5.7); `castling_play_le` is `fun _ _ h => (get_play_castling.mp h).1`.

L7.8 replaces THEOREMS R4's `play_board_dst … = some (movedPiece p m)` by the total form DESIGN §12
asks for. Together L7.7 and L7.8 say what every square holds after a pseudo-legal move. The last
three rows need only the shape, so no pseudo-legality hypothesis is needed for them.

---

## 8. Section "Sanity theorems (R5 and the promotion promise)"

These exist to catch a specification that says the wrong thing (THEOREMS R5, *prior-work* L8).
Lemmas (`variable {p : Position} {m : Move}`):

| ID | English | Lean | Tag |
|---|---|---|---|
| L8.1 | **(R5) A pseudo-legal bishop move lands on a square of the same shade (light or dark) as the one it left.** | `theorem PseudoLegal.isLight_dst_iff_of_bishop (h : PseudoLegal p m) (hb : p.board.kindAt m.src = some .bishop) : m.dst.IsLight ↔ m.src.IsLight` | sanity |
| L8.2 | **(R5) A pseudo-legal knight move lands on a square of the other shade.** | `theorem PseudoLegal.isLight_dst_iff_of_knight (h : PseudoLegal p m) (hn : p.board.kindAt m.src = some .knight) : m.dst.IsLight ↔ ¬ m.src.IsLight` | sanity |
| L8.3 | **A pseudo-legal move names a promotion choice exactly when a pawn reaches the last rank.** | `theorem PseudoLegal.promo_ne_none_iff (h : PseudoLegal p m) : m.promo ≠ none ↔ p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.dst.relRank p.turn = 7` | sanity |

Proofs.
- L8.1 *(checked)*: `obtain ⟨k, -, hsrc, hr, -⟩ := h.stepMove_of_kindAt hb (by decide) (by
  decide)`, `obtain rfl : k = .bishop := by simpa [Board.kindAt, hsrc] using hb`, then
  `obtain ⟨d, hd, i, -, -, hi, -⟩ := hr` and Basic's `Square.isLight_shift_of_mem_diagonals hd hi`.
- L8.2 *(checked)*: the same, ending with `obtain ⟨j, hj, hjt⟩ := hr` and Basic's
  `Square.isLight_iff_of_mem_knightJumps hj hjt`.
- L8.3: the six cases. Step and castling: `promo = none` and the source does not hold a pawn (step:
  `simp [hpr, hs, hk]`).
  Push and pawn capture: `PromotionRule` (`simpa [hs] using hpr`). Double push: `promo = none`, and
  `dst` is on relative rank 3 (Basic B6.7a, `relRank_of_offset_forward (dr := 2) ho`: `dr` must be
  given, since `2 * c.forward` is not syntactically `dr * c.forward` until it is). The leftover
  `((7 : Fin 8) : Int) = 3` is closed by `revert h3; decide`; `simp` and `omega` do not see through
  the `Fin` literal. En passant: `promo = none` and `relRank 5 ≠ 7`. This discharges
  Position D3.1's forward promise about the `promo` field "in both directions".

The hypotheses use `kindAt` and do not name the colour: "a bishop move" is any move from a square
holding a bishop. (A bishop of the side not to move makes `PseudoLegal` false.) THEOREMS proposed
the names `bishop_keeps_colour` and `knight_flips_colour`; the names here follow the library's
convention (conclusion first, `_of_` hypothesis, dot notation on the main hypothesis). The hazard of
THEOREMS R5 stands: "bishops stay on their colour" is per move, never per position.

---

## 9. Section "Terminal positions (R11)"

| ID | English | Lean | Tag |
|---|---|---|---|
| L9.1 | **(R11) A side to move with no legal move is checkmated or stalemated.** | `theorem checkmate_or_stalemate (h : ∀ m, ¬ Legal p m) : Checkmate p ∨ Stalemate p` | core |
| L9.2 | **(R11) No position is both checkmate and stalemate.** | `theorem not_checkmate_and_stalemate : ¬ (Checkmate p ∧ Stalemate p)` | core |
| L9.3 | A legal move is pseudo-legal. / After a legal move no king of the mover's colour is attacked. | `theorem Legal.pseudoLegal (h : Legal p m) : PseudoLegal p m` / `theorem Legal.not_kingAttacked (h : Legal p m) : ¬ (p.play m).board.KingAttacked p.turn` | core |
| L9.4 | A side to move with no king is not in check. | `theorem not_inCheck_of_not_hasKing (h : ¬ p.board.HasKing p.turn) : ¬ InCheck p` | core |
| L9.5 | A side to move with no king is not checkmated. | `theorem not_checkmate_of_not_hasKing (h : ¬ p.board.HasKing p.turn) : ¬ Checkmate p` | core |
| L9.6 | On the empty board the side to move is stalemated. | `theorem stalemate_of_board_eq_empty (h : p.board = Board.empty) : Stalemate p` | sanity |
| L9.7 | A side to move with no king has none after any move: promotion never makes a king, and the castling writes need a king on the source square. | `theorem not_hasKing_play (h : ¬ p.board.HasKing p.turn) : ¬ (p.play m).board.HasKing p.turn` | core |
| L9.8 | For a side to move with no king, every pseudo-legal move is legal. | `theorem legal_iff_pseudoLegal_of_not_hasKing (h : ¬ p.board.HasKing p.turn) : Legal p m ↔ PseudoLegal p m` | core |

Proofs *(L9.1, L9.2 checked)*: L9.1 is `if hc : InCheck p then .inl ⟨hc, h⟩ else .inr ⟨hc, h⟩`
(the decidable instance of D2.6; no classical reasoning); L9.2 is `fun ⟨h, h'⟩ => h'.1 h.1`; L9.3
are `h.1` and `h.2`. L9.4 is L2.9; L9.5 is `fun hc => not_inCheck_of_not_hasKing h hc.1`; L9.6: not
in check by L2.7, and no move is pseudo-legal, since `PseudoLegal.colorAt_src` (L4.1) needs a piece
on `m.src`. L9.7 needs no pseudo-legality: by L1.7 a square after the move holds what it held or a
value written by the move; step 3 writes nothing (`castleWrites_of_forall_not_isCastle`, since
`IsCastle` needs a king on `m.src`); step 2 writes `none`; so (one `simpa`) the king is step 1's
value, `(p.board m.src).map (·.promote m.promo)`, and `Option.map_eq_some_iff` names the source's
piece. That is a king only if it was one (`promo = none`) and never otherwise
(`PromoKind.toKind_ne_king`). L9.8 is
`⟨Legal.pseudoLegal, fun hm => ⟨hm, not_kingAttacked_of_not_hasKing (not_hasKing_play h)⟩⟩`.
`variable {p : Position} {m : Move}`, in a `section Terminal`.

---

## 10. Section "Tests"

As `example`s and `#guard`s at the end of the file, until the test library exists. Squares are
written `⟨file, rank⟩` with the algebraic name in a comment (Basic review C4 is still open). Each
named test position is a `def` with a docstring that lists its pieces, the side to move and the
rights, in the words used below (for example "White king e1 and pawn e5; Black king e8 and pawn d7;
Black to move, no rights; then d7d5."). Every
test below was run *(checked)*; the whole scratch file, definitions, the checked lemmas and these
tests, elaborates in about 6 s, of which 1.4 s is the `#guard` on Fool's mate.

- The initial position: `¬ InCheck Position.initial` by `decide`; e2e4 (`⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩`)
  is legal, by `decide` (about 0.25 s) and by `decide +kernel`; e2e5 is not; e2e4 with promotion
  choice queen is not; Ng1f3 (`⟨⟨6, 0⟩, ⟨5, 2⟩, none⟩`) is legal; Bf1c4 (`⟨⟨5, 0⟩, ⟨2, 3⟩, none⟩`)
  is not (blocked by e2); after e2e4 the en passant target is e3 (`some ⟨4, 2⟩`), by `decide`.
- Fool's mate, `foolsMate := (((Position.initial.play f2f3).play e7e5).play g2g4).play d8h4`, with
  the moves written as structure literals: `InCheck foolsMate` by `decide`, and
  `#guard decide (Checkmate foolsMate)`.
Every test position grants only rights that FIDE could grant (R9.3: a right is held only with the
king and that rook on their home squares), so a test about a kept right tests a real right.

- The initial position, further: Ng1f3 with a promotion choice (`some .queen`) is not legal (a
  knight move may not name one). It has exactly 20 legal moves (`#guard`, about 1 s, counting over
  `Square.all` and `PromoKind.all`). With a white knight on e3, e2e4 is not legal (the square passed
  over must be empty).
- Rights by squares: on `castlePos`, Rh1h2 leaves rights `⟨false, true, false, false⟩` (only `K`
  is lost).
- Black castling, on `blackCastlePos`: black king e8 and rook h8, white king e1, Black to move,
  rights `⟨false, false, true, false⟩`: e8g8 is legal, and after it f8 holds the black rook.
- Black promotion, on `blackPromoPos`: black king e8 and pawn a2, white king h8, Black to move, no
  rights: a2a1=N is legal, a2a1 without a choice is not.
- A pin, on `pinPos`: white king e1 and bishop e2, black king a8 and rook e8, White to move, no
  rights: Be2d3 is pseudo-legal but not legal.
- Castling, on `castlePos`: white king e1, white rooks a1 and h1, black king e8, black rooks f8 and
  b8, White to move, rights `⟨true, true, false, false⟩` (White's only: Black's rooks are not at
  home), no target. Built as
  `⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set … , .white, ⟨true, true, false, false⟩,
  none⟩`.
  - e1g1 is not legal (f1, the square crossed, is attacked by the f8 rook);
  - e1c1 is legal (b1 must be empty but may be attacked: the b8 rook attacks it);
  - after e1c1 the rook stands on d1, and the rights are `CastlingRights.none`.
- Castling out of check and through an attacked d1, on `castleRookPos f`: white king e1, white
  rooks a1 and h1, black king b8, a black rook on the seventh rank on file `f`, rights
  `⟨true, true, false, false⟩`. With the rook on e7 (`f = 4`) neither e1g1 nor e1c1 is legal (the
  king is in check); with the rook on d7 (`f = 3`) e1c1 is not legal (d1 is attacked) and e1g1 is.
- En passant, on `epPos`: white king e1, black king e8, white pawn e5, black pawn d7, Black to move,
  no rights (`.none`), after `d7d5`: the target is d6; e5d6 is legal; after it d5 is empty.
  - A stale target: after White's e1d1 the target is `none`; after Black's e8d8 as well, e5d6 is
    not legal.
- En passant that exposes the king along the rank, on `epPinPos`: white king a5, white pawn b5,
  black pawn c7, black rook h5, black king h8, Black to move, no rights, after `c7c5`: b5c6 is
  pseudo-legal but not legal (with b5 and c5 both emptied, the rook attacks a5).
- Kings may not stand adjacent, on `kingsPos`: white king e1, black king e3, White to move, no
  rights: e1e2 is not legal, e1d1 is.
- Promotion and rights, on `promoPos`: white king e1, black king e8, white pawn b7, black rooks a8
  and h8, White to move, rights `⟨false, false, true, true⟩` (Black's only: White has no rooks):
  - b7a8 without a promotion choice is not legal; b7a8=Q is legal; b7b8=N is legal;
  - after b7a8=Q, a8 holds a white queen and the rights are `⟨false, false, true, false⟩`: Black's
    queenside right is gone and Black's kingside right is kept (the capture-on-the-rook's-home bug
    class of *representation* §2.5, DESIGN §8.4).
- Attack geometry: a rook on a1 reaches a8 on the empty board; not with a pawn on a4; a knight on
  b1 does not reach b3. A lone black rook on e8 attacks the white king on e1
  (`KingAttacked .white`); with a white pawn on e4 it does not.

- Added by the file-level review (`docs/reviews/Rules.md` §2), each run *(checked)*:
  - Black en passant, on `blackEpPos`: white king e1 and pawn e2, black king e8 and pawn d4, White
    to move, no rights, after `e2e4`: the target is e3; d4e3 is legal and empties e4; with e4
    emptied by hand, d4e3 is not legal (a target alone permits no capture).
  - The rook may be attacked, on `rookAttackedPos`: white king e1 and rook h1, black king a8 and
    rook h8, White to move, rights `⟨true, false, false, false⟩`: e1g1 is legal although h1 is
    attacked; with a white knight on g1, or a black rook on g8 (g1 attacked), it is not.
  - A king may not capture a defended piece, on `defendedPos`: white king e1, black king e8, black
    rook e2 and bishop h5, White to move, no rights: e1e2 is not legal; with the bishop removed it
    is.

No test sweeps all moves by `decide` (`Checkmate` by `decide` would check 20 480 candidates in the
kernel; measured in the file-level review: `Checkmate foolsMate` by `decide +kernel` does not finish
in 500 s). No `native_decide` (DESIGN §7.3).

---

## 11. Design choices, with reasons

1. **`Slides` in index form, with `(s.shift d j).bind b = none` for "empty".** It is DESIGN §5.2's
   form, settles its open item (no quantifier over squares for the in-between test), is decidable by
   core's bounded `Nat` quantifiers, and makes R3 arithmetic. A named slider predicate keeps
   `Reaches` one line per kind.
2. **`Reaches` matches on the kind, sliders sharing one arm** through `Kind.slideDirections`, so the
   queen is visibly rook-or-bishop and a reader sees all six kinds.
3. **`AttacksFrom` reads the kind off the board** (a `match`), and `Attacked` quantifies over squares
   only: 64 reads per attacked-square test, never 64 × 12.
4. **`Board.colorAt` and `Board.kindAt`.** "Does not hold a piece of its own colour" is
   `colorAt dst ≠ some c`, FIDE 3.1's sentence, with no case split on "empty or enemy".
5. **`StepMove` quantifies over the kind** (`∃ k`), unlike `Attacked`. A move is tested once, not
   64 times, so six cheap reads are affordable, and `obtain ⟨k, hk, hsrc, hr, hdst, hpromo⟩` is the
   most readable way to take a step move apart. Measured: deciding `StepMove` for all 20 480
   candidates of the initial position takes 0.29 s interpreted.
6. **`Move.IsDoublePush`**, a third shape predicate beside DESIGN's two, because `DoublePushMove`
   and step 5 both need "a pawn of the side to move goes two squares straight forward"
   (Principle 6).
7. **`play` as writes, every step reading the position before the move.** Steps 1–3 produce lists
   of writes and `Board.setMany` performs them. Reasons:
   - *Faithful and readable.* "The move writes: source empty; destination the arriving piece; if en
     passant, victim empty; if castling, the rook from its home to the square crossed" is exactly
     how a player would say it, and each condition is read in the position before the move, so no
     step can see a half-made move.
   - *Provable.* R4's frame lemma is one list lemma (L1.6); `touched` is the write list's squares by
     definition, not a second list that could disagree.
   - *Safe under the Position review's C1 hazard.* No definition here has result type `Board` and an
     `if` that reads a board: conditions are decided where the write lists are built, in a function
     that returns a `Position`. Measured (interpreted, function boards as they are now): 32 chained
     plies with a legality test each, 0.19 s; all 20 480 candidates tested for legality on the
     position after four plies (Fool's mate), 1.4 s. No exponential growth. So this module does not
     force the owner's C1 decision, and its statements do not change under either option.
8. **Castling rights are revoked by squares (D5.6), not by reading the board.** DESIGN §5.5 step 4
   says "if `src` holds a king of colour `c`, revoke both of `c`'s rights; revoke `(c', w)` if `src`
   or `dst` is `rookHome c' w`". This spec says "revoke `(c, w)` if `src` or `dst` is `kingHome c` or
   `rookHome c w`", the rule Stockfish uses (`castlingRightsMask[from] | castlingRightsMask[to]`,
   a mask indexed by square only; python-chess, by contrast, also clears all of the mover's rights
   on any king move, which reads the piece). Why it is faithful: a right can be
   used only with the king on `kingHome c` and the rook on `rookHome c w` (`CastleMove` checks both),
   and any king or rook that leaves or arrives on those squares revokes it. So castling is possible
   only if the king and that rook have stood on their home squares since the position was set up,
   which is FIDE 3.8.2.1 read from the given position. The two rules differ only when a right is held
   while its king or rook is away from home, which `WellFormed` (R9.3) excludes, or when a king is
   captured on its home square (possible only from a position where the side not to move is in
   check, design choice 11): the square rule revokes that colour's rights, DESIGN's does not. In
   neither case does either rule allow a castling FIDE forbids. Why better: it reads no board, so step 4 is a function of the
   rights and two squares, R8 is two lines, and R9.3's preservation is a statement about squares.
   **This departed from DESIGN §5.5 step 4.** The Round 3 Lean critic agreed it is faithful and
   recommended accepting it; Round 4 updated DESIGN §5.5 step 4 to match. The owner can still revert
   it (§12 item 1).
9. **`CastleMove`'s `Decidable` instance is hand-written**, guarded by the shape (D4.6), for the
   measured 80× speedup of compiled decisions. Since Round 4 the guarded part is the named
   predicate `Position.CanCastle`, so the instance restates no condition, and the measurements
   under D4.6 locate the slowdown (an attack test as a direct conjunct of a derived instance). All other instances are `by unfold X;
   infer_instance`, which is the shortest form and is kernel-friendly (all checked under `decide`
   and `decide +kernel`).
10. **`CastlingRights.ofGet`** builds rights from their `get` function. Position's convention says
    rights are changed only by `revoke` and `revokeAll`; that convention was a means to R8, and with
    `ofGet` R8 is immediate from the definition of step 4 (`&&` can only turn a right off). The true
    convention is now "`play` changes rights only through `Move.castlingAfter`, which can only clear
    them"; Position's docstring should say that (§12 item 7).
13. **Named hypotheses over spelled-out ones** (Round 4): `Board.HasKing` for "has a king",
    `Position.CanCastle` for "may castle now", `reaches_congr` for "only the squares between are
    read". Each replaces a formula that appeared several times, and each is a phrase a player would
    use.
14. **Rules stay conjunctions, not structures** (Round 4, considered and deferred). Proofs take the
    rules apart by position (`⟨-, -, h5, -, -, hpr⟩`), so reordering a conjunct breaks them at build
    time. Prop-valued structures with documented fields would read better (`h.promo`) and cost one
    `decidable_of_iff` instance each. Deferred to the M2/M5 work, where the generator's completeness
    proof will show which rules need it; `CanCastle` already cut `CastleMove` from seven conjuncts to
    three.
11. **A king capture is not excluded** (DESIGN §5.4); `parseFEN` rejects the positions where it
    could happen (DESIGN §6.4).
12. **No executable `inCheck`**, no `movedPiece`, no `findKing`, no `get!`, no `default`.

---

## 12. Not in this module, and open items

Open items:
1. **Step 4 by squares** (design choice 8): accepted by the critic and written into DESIGN §5.5 in
   Round 4; the owner has the last word. If rejected, D5.6 becomes
   `m.dst = rookHome c w ∨ m.src = rookHome c w ∨ (p.board m.src = some ⟨c, .king⟩)` (taking `p`),
   and L7.9 changes accordingly; nothing else moves.
2. **Position review C1 (`Board` as a one-field structure).** Not forced by this module (design
   choice 7). If adopted, goals print `b.get s`, and `Board.setMany` and `colorAt` are unchanged in
   the source.
3. **Basic review C2 (pawn direction as a `Direction`).** If adopted, `Reaches`' pawn arm, D3.3,
   D4.2, D4.3, D4.5 and D5.9 change from `offset 0 (dr * c.forward)` to `shift c.pawnDirection dr`
   (and the capture diagonals to two directions). Decide before the translation.
4. **Position review C2 (`CastlingRights.none` → `empty`).** This module writes `.none` only in one
   test (`epPos`); the rename touches one line.
5. **Basic additions this module would use** (proved locally here, to move when Basic is next
   revised): `rookCastleSquare_ne_kingHome` (L7.6), `kingCastleSquare` injective in the wing (used in
   L3.1), and the `private` helpers of §4 (`Color.forward_ne_zero`, `Color.two_mul_forward_ne_zero`,
   `Square.file_eq_of_offset_zero`, `shift_kingHome_one_ne`). Possibly also
   `Piece.kind_promote_eq_king : (pc.promote o).kind = .king ↔ pc.kind = .king ∧ o = none`; L9.7 no
   longer needs it.
6. **THEOREMS edits**: applied in Round 4 (R3, R4, R5, R8, R9, R11, M2 now name this module's
   statements). DESIGN §5.5 step 4 updated (item 1); DESIGN §5.4 does not yet mention
   `IsDoublePush` or `CanCastle`.
7. **Position, next revision**: restate `CastlingRights`' convention as "`play` changes rights only
   through `Move.castlingAfter`, which can only clear them", and move `CastlingRights.ofGet` and
   `get_ofGet` (D5.7, L5.1) into Position. Not edited here: it is Position's file.
8. **L4.11, the castling-landing fidelity lemma** ([later]): the one place where the Lean's reading
   of FIDE is an argument, not a definition (D4.6 note). Prove before calling the module final.

Not here, on purpose:
- R3 symmetry and the super-piece test (Stage 2; L2.4 and L2.8 shape them).
- R6 colour flip, R7 material, R9 `WellFormed`, R10 `Reachable`: `Chess/Invariants.lean`, Stage 2.
- M5 exclusivity of the rules (L4.6) and the generator: `Chess.MoveGen`.
- Draw rules, clocks and repetition: not part of the move layer (DESIGN §6.5).

---

## 13. Checklist for the translator

- `import Chess.Position` only; add `import Chess.Rules` to `Chess.lean`.
- Module docstring `/-! # Rules … -/` with `## Main definitions` (`Reaches` and `Slides`,
  `Board.Attacked`, `Board.KingAttacked`, `InCheck`; the shape predicates; the six rules and
  `PseudoLegal`; `Position.play` and its steps; `Legal`, `Checkmate`, `Stalemate`), `## Main
  statements` (`play_board_of_not_mem`, `play_board_src`, `play_board_dst` (R4); `play_turn`;
  `castling_play_le` (R8); the R5 pair; `checkmate_or_stalemate`, `not_checkmate_and_stalemate`
  (R11); `reaches_set_src`/`reaches_set_dst`), and `## Implementation notes` summarizing design
  choices 1, 7, 8 and 9 and the `o.bind b` idiom.
- Section order as in "Contents" above; each a `/-! ## … -/` heading. Lemmas needing a `variable`
  line go in a `section` or the namespace they live in (`namespace Board` for §1's lemmas).
- Every `def`, `instance` and `theorem` carries the docstring given here. Nothing is `sorry`; no
  `native_decide`. [later] lemmas may be left out (L4.6 is).
- Scopes: §1's lemmas in `namespace Board`; then `section Reaching`, `section Shapes`, `section
  Movement`, `section Play`, `section Sanity`, `section Terminal`, each opening with its table's
  `variable` line. Proof helpers that no other module needs are `private`, with a docstring, next
  to the lemmas they serve (the four §4 helpers, and `PseudoLegal.not_mem_rest` for L7.7a).
- `@[simp]` exactly on: `Board.colorAt_of_eq_some`, `Board.kindAt_of_eq_some`, `Board.setMany_nil`,
  `Board.setMany_cons`, `CastlingRights.get_ofGet`, `play_turn`. Nothing else.
- Instances: `by unfold X; infer_instance` (D2.3: `split <;> infer_instance`; D2.2: `cases k <;>
  unfold Reaches <;> infer_instance`), except `CastleMove.decidable`, written as in D4.6. Never put
  an attack test directly as a conjunct of a derived instance of a predicate that is decided for
  every candidate move (D4.6's measurements): name the conditions, as `CanCastle` does.
- In `Slides`, keep the binder order `∀ j < i, 0 < j → …` (core's bounded instance).
- After `cases k`, name the cases (`case pawn => …`): goals come in constructor order.
- Lines at most 100 characters. Test positions use `|>.set` chains (checked to parse).
- Record in `docs/process/Rules.md` every place where the Lean forced the English to change.
