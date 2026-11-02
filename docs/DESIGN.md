# Design of the `Chess` library

Author role: architect. Date: 2026-11-01. Status: second draft, revised after the design critique
(findings A1–G, answered in Section 11).

Inputs: `docs/research/*.md` (cited as *representation*, *lean-eng*, *game-theory*, *prior-work*,
*landscape*), `docs/THEOREMS.md` (theorem IDs such as R4, G2, C1 refer to it), and the prototype in
`../chess-lean`.

This document fixes the architecture in English. Lean names appear so that the English and the code
can be matched, but the only Lean here is short signatures. The per-module details belong in
`docs/spec/<Module>.md`, which refines Section 8 of this file.

**The names in Section 2 are authoritative.** Where `docs/THEOREMS.md` uses a different name, this
file wins; Section 12 lists the edits THEOREMS needs to catch up.

---

## 1. Principles

1. **The English is the specification; the Lean is its translation.** Every definition in the
   trusted layer has a one-sentence English docstring that matches `docs/spec/<Module>.md` word for
   word where possible. A chess player should be able to check each rule against the FIDE Laws by
   reading the English, and a Lean user should be able to check the Lean against the English.
2. **What is legal is a relation; what a move does is a total function.** Legality, attack, check,
   checkmate and forcing are `Prop`s. The effect of a move is the total function `play`, trusted by
   reading it. Listing the legal moves is a separate function joined to the relation by a theorem.
   Until that theorem (M4, Stage 2) is proved, the generator is also trusted; after it, only the
   relations and `play` are.
3. **One data model, two kinds of definitions.** The specification and the executable generator
   share the same `Square`, `Board`, `Move` and `Position`. What separates the layers is relation
   versus function, not two copies of the data. A third, faster data model (bitboards) is a later
   addition behind a refinement theorem (Section 3.3).
4. **Game theory is stated once, for an abstract game.** Forced wins, certificates and their
   soundness never mention a knight. Chess is one instance (*prior-work* L1).
5. **Small, named, total.** Every function is total. Partial behaviour is expressed by a
   hypothesis on the theorem, never by a sentinel value (the prototype's square 64 and piece code 0
   are the cautionary examples). No magic numbers: castling squares, promotion ranks and pawn
   directions are derived from colour. The one exception is the table of nibble codes for packed
   board literals, which lives in exactly one place (Section 4.3).
6. **One predicate per rule, shared by every user.** A chess concept that two definitions need (an
   en passant capture, a castling) is a single named predicate, used by the legality rule, by `play`
   and by the theorems. Two slightly different copies of a rule are the commonest source of false
   lemmas.
7. **Kernel-reducible by construction.** Structural recursion only, `List` and `Nat` rather than
   `Array`, and no user-defined proof fields inside data; the only proofs carried by data are the
   `Fin` bounds. This keeps every computation available to `decide +kernel`, so that kernel-only
   proofs remain possible (*lean-eng* §10).

---

## 2. Vocabulary fixed by this design

| English | Lean | Meaning |
|---|---|---|
| colour | `Color` (`white`, `black`), `c.other` | a player |
| kind | `Kind` (`pawn`, `knight`, `bishop`, `rook`, `queen`, `king`) | what a piece is, without colour |
| piece | `Piece` = colour + kind | what can stand on a square |
| square | `Square` = file + rank, each `Fin 8` | a1 is file 0, rank 0 |
| board | `Board` = `Square → Option Piece` (a `def`) | what stands on each square |
| wing | `Wing` (`kingside`, `queenside`) | the side of the board a castling goes to |
| castling rights | `CastlingRights`, read by `rights.get c w` | which castling rights are still held (not whether castling is possible now) |
| promotion choice | `PromoKind` (`knight`, `bishop`, `rook`, `queen`) | what a pawn may become |
| move | `Move` = `src`, `dst`, `promo : Option PromoKind` | a move as data (UCI) |
| position | `Position` = `board`, `turn`, `castling`, `epTarget` | the move layer's state |
| en passant shape | `Move.IsEnPassant p m` | `m` has the shape of an en passant capture in `p` |
| castling shape | `Move.IsCastle p w m` | `m` is the king's castling move to wing `w` in `p` |
| pseudo-legal | `PseudoLegal p m` = `StepMove ∨ PushMove ∨ DoublePushMove ∨ PawnCaptureMove ∨ EnPassantMove ∨ ∃ w, CastleMove w` | movement rules, ignoring own-king safety |
| legal | `Legal p m` | pseudo-legal and the mover's king is not attacked afterwards |
| check | `InCheck p` (a `Prop`, decided by `decide`) | the side to move's king is attacked |
| abstract game | `Game` (structure), with game `G` | states, moves, turn, play, mated |
| chess as a game | `Game.chess` | the instance whose moves are `legalMoves` |
| forcing | `G.Forces a T n x` | attacker `a` forces the target set `T` within `n` attacker moves |
| winning | `G.WinsIn a n x`, `G.Wins a x`, `G.MateIn a n x` | forcing the defender to be mated |
| holding | `G.Holds d x := ¬ G.Wins d.other x` | defender `d` holds at `x` (Stage 3) |
| only winning move | `G.OnlyWinningMove x m` | the mover wins after `m` and after no other move |
| chess-specialised names | `Chess.WinsIn`, `Chess.MateIn`, `Chess.Wins`, `Chess.OnlyWinningMove` | the above with `G := Game.chess`; headline theorems use these |
| attacker | `a : Color` in `WinsIn a n x` | the side trying to mate; the defender is `a.other` |
| budget | `n` in `WinsIn a n x` | attacker moves allowed, the mating move included |
| certificate | `Cert M` with `goal`, `move`, `replies` | a finite strategy tree, untrusted data |

There is no executable `inCheck : Position → Bool` in Stage 1. The executable check test is
`decide (InCheck p)`. A faster test (the super-piece method, R3.3) may be added later, under its own
name, with a theorem equating it to `InCheck`.

---

## 3. Layers

```
                ┌─────────────────────────── trusted: read the English ───────────────────────────┐
 Specification  │ Basic (colours, squares, pieces, geometry)  Position (board, moves, positions)   │
                │ Rules (Reaches, Attacked, PseudoLegal, play, Legal, Checkmate, Stalemate)        │
                │ Game, definitions only (Game, Forces, WinsIn, MateIn, OnlyWinningMove)          │
                │ ChessGame (Game.chess, Chess.WinsIn …, fen/uci parsers)                          │
                │ ┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄ │
                │ MoveGen (pseudoMoves, legalMoves): trusted UNTIL STAGE 2 (M4 removes it)         │
                └───────────────────────────────────────────────────────────────────────────────┘
 Proved, not      Game, the rest: searchForces (searchForces_iff), Cert and checkers (checkWin_sound)
 trusted          MoveGen/Correct (Stage 2): mem_legalMoves
                        ▲ refinement + game morphism (Stage 5)
 Fast           Fast.* (bitboards over BitVec 64)                       — not in this draft
                        ▲ certificates (data)
 Untrusted      scripts/ (Stockfish, python-chess, tablebases): proposes, never decides
```

### 3.1 Specification layer

The specification consists of the data types, the `Prop`-valued rules and the total function
`play`: what a square, piece, board, move and position are; when a piece attacks a square; when a
move is legal; what a move does; what checkmate and stalemate are; and, in the abstract game, what
it means to force a win. These are the definitions a reader must trust. They are written to be
read, not run, although all of them are decidable and therefore also runnable.

`ChessGame` is in the trusted box because headline theorems are stated in its vocabulary: the chess
instance, the specialised names, and the FEN and UCI parsers. The parsers are trusted until M11.

### 3.2 Executable layer

The executable layer computes what the specification describes:

- `legalMoves : Position → List Move`, the generator, and `perft`.
- `searchForces`, a bounded minimax that decides `Forces` (and so `WinsIn`).
- `checkWin` and `checkOnlyMove`, Boolean certificate checkers.

Each executable function has, or will have, a theorem stating what it computes in specification
terms. The checkers and the search are proved in Stage 1 (C1, C2, G5). For the generator this
theorem is M4 (Stage 2): in Stage 1 the generator is *tested*, by perft (M7) and by checking it
against the decidable `Legal` on test positions (Section 5.7), and it is part of the trusted base.
Until M4 is proved, chess theorems are honestly about "the game whose moves are `legalMoves`", and
G8 later turns them into theorems about FIDE chess without changing a single statement.

The executable layer works on the *same* `Position` as the specification. This is deliberate. The
Stage 2 link is then a membership `↔`, the simplest possible refinement statement, and no
abstraction map is needed until the fast layer exists.

### 3.3 Fast layer (Stage 5, not in this draft)

Bitboards: two colour sets and six kind sets, each a `BitVec 64` read as a set of squares, with
leapers computed by masked shifts and sliders by the classical ray method (first blocker). They are
linked to the specification by an abstraction map `abs : Fast.Position → Position` and the theorems
of *representation* §4.1. Their payoff is a game morphism (G7) from the fast game to `Game.chess`, so
every certificate checked fast transfers to the specification by one rewrite. Magic and PEXT
bitboards are excluded: their constants come from search, and a reader cannot see why they are right
(*representation* §4). The bitboard ideas the owner has seen (whole-board shifts, attack sets as
words) belong here; the specification must not depend on them.

---

## 4. Representation, and why

### 4.1 Colours, kinds, pieces

`Color` and `Kind` are enumerations. `Piece` is a structure of a colour and a kind, not twelve
constructors, because almost every rule is "a piece of kind `k` and colour `c`" and needs to
take the two apart. Colour-dependent geometry is a function of colour, never a duplicated rule:

- `Color.forward : Color → Int` is `+1` for White and `-1` for Black (the pawn direction).
- `Square.relRank (s : Square) (c : Color) : Fin 8`, written `s.relRank c`, is the rank of `s`
  counted from `c`'s side: rank for White, `7 − rank` (`s.rank.rev`) for Black. A pawn starts on relative rank 1, double-pushes from it, promotes on
  relative rank 7, and captures en passant onto relative rank 5. The en passant target of a double
  push by `c` lies on `c`'s relative rank 2.
- `Color.homeRank c : Fin 8` is the absolute rank whose `relRank c` is 0 (rank 0 for White, rank 7
  for Black), where `c`'s king and rooks start.
- `Piece.promote : Piece → Option PromoKind → Piece` keeps the piece for `none` and, for `some k`,
  gives a piece of the same colour and kind `k.toKind`.

This makes the colour-flip symmetry (R6) a lemma about `forward` and `relRank`, not a case split.

Every finite type (`Color`, `Kind`, `PromoKind`, `Wing`, `Square`) gets `all`, `mem_all`,
`all_nodup` and a `Decidable ∀` instance (R2). For `Square` the instance goes through the core
`Fin 8` quantifiers, which plain `decide` handles; a list-based instance hits `maxRecDepth`
(*lean-eng* §4, §6). `Square` also gets `Decidable ∃` by the same route. The enumerations and
`Square`, `Piece`, `Move`, `CastlingRights` derive `DecidableEq, Repr, Inhabited` and never `BEq`
separately (*lean-eng* §6). `Board` is a function type and cannot derive them: it gets a
hand-written `DecidableEq` (Section 4.3), and `Position` gets hand-written `DecidableEq` and `Repr`
(the `Repr` prints an 8×8 diagram; Section 4.6).

### 4.2 Squares

`structure Square where file : Fin 8; rank : Fin 8`. A square *is* a file and a rank, and the rules
are stated in file and rank differences. `Fin 8` makes "on the board" a type, so no rule carries a
`< 64` side condition. The cost under `decide +kernel` is the same as `Fin 64` (*lean-eng* §4).

- `Square.index : Square → Fin 64` is `8 · rank + file` (a1 = 0, h8 = 63; the LERF numbering of
  every chess-programming source), with inverse `Square.ofIndex` and both round trips (R1). It is the
  only bridge to packed literals and, later, to bitboards.
- `Square.offset (s : Square) (df dr : Int) : Option Square`, written `s.offset df dr`, is the
  single geometric primitive: shift by `df` files and `dr` ranks, or `none` if that leaves the board. Every leaper, every slider and
  every pawn step is defined from it (*representation* §4).
- `Direction` is an enumeration of the eight compass directions, each with its `(df, dr)` and its
  `opposite`. Rook directions, bishop directions and queen directions are named lists of directions.
  The knight's eight jumps are a named list of offsets.
- `s.shift d i := s.offset (i · d.df) (i · d.dr)`: the square `i` steps from `s` in
  direction `d`, if it is on the board. This is the form the *specification* of sliders uses
  (Section 5.2).
- `s.ray d : List Square` is the list `[s.shift d 1, s.shift d 2, …]` of on-board squares,
  nearest first, excluding `s`, by structural recursion with fuel 7. It is the form the *generator*
  uses. `mem_ray_iff` (M1) links the two.
- `Square.IsLight s` is "file + rank is odd" (a1 is dark).

There are no 64 named square constants. Fixed squares are computed from colour and wing:
`kingHome c`, `rookHome c w`, `kingCastleSquare c w` (where the king lands), `rookCastleSquare c w`
(the square the king crosses, where the rook lands).

### 4.3 Boards

`def Board := Square → Option Piece`. The mailbox board in its purest form. It is a `def`, not an
`abbrev`, so that the generic `Pi` instances for `DecidableEq` and `Inhabited` cannot compete with
the library's own.

- **Faithful by construction.** Each square holds at most one piece. There is no "two pieces on one
  square" invariant, no padding, no sentinel.
- **Reading is application.** "What stands on e4" is `b e4`.
- **Writing is one combinator.** `Board.set b s x` is `b` with square `s` replaced by `x`. Core has
  no `Function.update`, so `Board.set` is the library's own, with `@[simp]` lemmas `set_same` and
  `set_ne`, and `set_comm` (not simp: a permutation lemma) for `rw`. Every change a move makes is a
  composition of `set`s, and every frame lemma (R4) is `simp [set_ne]`, provided disequalities are
  stated read-square first, `t ≠ s` (with `h : s ≠ t`, `simp [h]` makes no progress).
- **Equality** is extensional (`funext`) and decidable through the `Square` quantifier, 64
  comparisons.

**Packed literals.** The prototype's insight was that one `Nat` of 64 four-bit nibbles is very fast
in the kernel, because shifts and masks on `Nat` are GMP-accelerated (*lean-eng* §2, §5). This design
keeps that insight as a *notation*, not as the representation.

- The code table is `Piece.code : Piece → Fin 16` (codes 1–12) and `Piece.ofCode : Fin 16 → Option
  Piece`, which returns `none` for 0 and for the unused codes 13–15, with the round trip
  `ofCode_code`. This is the only place piece codes appear.
- `Board.unpack : Nat → Board` reads square `s` as `Piece.ofCode` of nibble number `s.index`.
  `Board.pack : Board → Nat` is its inverse on boards, and `unpack_pack b : unpack (pack b) = b` is
  the only theorem it needs.

A board literal `Board.unpack 0x…` costs two bignum operations per square read, and a few `set`s on
top of it cost a few comparisons more. Generated per-node lemmas in certificates state positions this
way (Section 7.4), which keeps every chain of `set`s short. **No headline statement mentions
`Board.unpack`.** Headline positions are written with `fen "…"`; `unpack` appears only in generated
files the reader never has to read.

Rejected alternatives, with the reason:

| Representation | Why not in the specification |
|---|---|
| `Nat` of nibbles as *the* board | Every rule becomes arithmetic on codes; the type admits invalid codes; this is the prototype's main readability problem. Kept as the literal notation above. |
| `List`/`Array`/`Vector` of 64 | Indexed access walks a list in the kernel; `Array` and `Vector` equality is about 40× slower than `List` (*lean-eng* §5). Adds a length invariant. |
| Twelve bitboards | 66 disjointness invariants. Bitboards belong to the fast layer, as two colour sets and six kind sets. |
| Piece list | Not canonical (order), duplicates information. |

### 4.4 Moves

`structure Move where src : Square; dst : Square; promo : Option PromoKind`.

- **Moves are data.** A move says which square a piece leaves, which square it goes to, and what a
  pawn becomes if it promotes. It does not say what kind of move it is; `play` and `PseudoLegal`
  work that out from the position, through the shared predicates of Section 5.4. This is exactly
  UCI, so certificates from Stockfish need no translation.
- **Castling** is the king's two-square move (`e1g1`, `e1c1`, `e8g8`, `e8c8`). It is not a separate
  constructor, so it can never be generated twice (M5).
- **En passant** is a pawn's diagonal move onto the en passant target.
- **Promotion** uses `PromoKind`, a four-value enumeration with `PromoKind.toKind`, so that
  "promote to a king" or "promote to a pawn" cannot be written. FIDE 3.7.5 lists exactly queen,
  rook, bishop or knight.
- **Notation is a parser.** UCI strings parse to `Move`. SAN is not used for identity (the
  dwrensha pitfall, *prior-work* §5).

### 4.5 Castling rights

`inductive Wing | kingside | queenside` and `structure CastlingRights` with four `Bool` fields,
always read through `CastlingRights.get : CastlingRights → Color → Wing → Bool` and changed through
`CastlingRights.revoke c w` and `revokeAll c`. `CastlingRights.none` has all four rights false. The
four fields keep equality structural and cheap; the `get` interface keeps theorems indexed by colour
and wing, so colour flip is a swap, not four special cases (R6). Castling rights are ordered
pointwise, and `play` never grants a right: `(p.play m).castling ≤ p.castling` for **every** move
`m` (R8, unconditional).

### 4.6 Positions

`structure Position where board : Board; turn : Color; castling : CastlingRights;
epTarget : Option Square`.

This is the **move layer**: exactly the information that determines which moves are legal and what
they do. It deliberately has:

- **No halfmove clock and no fullmove number.** Perft is defined on this layer and must not read a
  clock to match the published numbers (M7). The clock belongs to the clocked games of Stage 4
  (G12), which are separate `Game` instances whose states pair a position with a clock.
- **No history.** Repetition is a property of a game record, not of a position (G15).
- **No stored king squares.** Storing them would make "one king per side" true by construction, but
  it adds a consistency invariant between the fields and the board, and `play` would have to update
  it. Instead "the king of colour `c` is attacked" is the total statement "some square holds a king
  of colour `c` and is attacked" (Section 5.3), which needs no king finder. The prototype's
  `findKing` returned 64 on a kingless board and made such boards silently stalemated (*landscape*
  §2); the existential cannot fail that way.
- **No proof fields.** `WellFormed p` (R9) is a separate, decidable predicate on plain data, defined
  in Stage 2: one king of each colour; no pawn on either back rank; each castling right backed by
  the king and that rook on their home squares; if `epTarget = some t`, then `t` is empty, the
  square behind it (towards `p.turn.other`'s home rank) is empty, and a pawn of colour
  `p.turn.other` stands one square beyond it (away from `p.turn.other`'s home rank); and the side
  not to move is not in check. Literal positions stay `decide`-friendly.

`Position` has a hand-written `DecidableEq` (via the board's) and a hand-written `Repr` that prints
an 8×8 diagram with the other three fields. `Position.initial` is the standard starting position.

**En passant target.** `epTarget` is the square a pawn has just passed over by a double push, as in
FEN. `play` sets it after **every** double push and clears it after every other move. This is the
simplest rule to state and to check. It means two positions can differ only in an en passant target
from which no capture is possible; FIDE 9.2.3 treats those as the same position. That identity is
handled by `Position.normalize` in Stage 4 (G16), not by complicating `play` now. (Setting the
target only when an enemy pawn stands beside the pushed pawn would not remove the need: a pinned
capturer still makes the capture illegal.) This convention has a consequence for certificate
generation; see Section 7.4.

---

## 5. Moves and legality

### 5.1 Two relations and one function

- `PseudoLegal p m : Prop`: `m` obeys the movement rules of FIDE Articles 3.1–3.8 for the side to
  move, including all of castling's preconditions, but ignoring whether the mover's own king is
  attacked afterwards.
- `Position.play : Position → Move → Position`: what the move does. **Total.** Theorems about
  `play` assume `PseudoLegal p m`, except `play_turn`, `play_board_of_not_mem` and
  `castling_play_le`, which hold for every move.
- `Legal p m : Prop := PseudoLegal p m ∧ ¬ (p.play m).board.KingAttacked p.turn`.

The definition of `Legal` is FIDE 3.9.2 read literally: no move may expose the mover's own king to
check or leave it in check. Making it the conjunction of two named facts means:

- the second half of `Legal` *is* the "side not to move is not in check" component of `WellFormed`
  for the new position (R9);
- the generator is `pseudoMoves` filtered by the second half, the same sentence read as a program
  (M4);
- no theorem about `Legal` needs a `WellFormed` hypothesis (M4 is unconditional).

`PseudoLegal` and `Legal` are **decidable from day one** (Section 5.4), so the generator can be
tested against them in Stage 1.

### 5.2 Geometry: `Reaches`

`Reaches k c b s t : Prop`: a piece of kind `k` and colour `c` standing on `s` attacks `t` on board
`b`. It ignores what stands on `t` and ignores pins (FIDE 3.9.1: a pinned piece still gives check).

**`Reaches k c b s t` reads `b` only on squares strictly between `s` and `t`; it does not inspect
`b s` or `b t`.** Leapers and pawns do not read `b` at all. The super-piece theorem (R3.3) and attack
symmetry depend on this.

- knight: `t` is one of the eight knight jumps from `s`;
- king: `t = s.shift d 1` for one of the eight directions `d`;
- bishop, rook, queen: for some direction `d` of the kind and some `i` with `1 ≤ i ≤ 7`,
  `s.shift d i = some t`, and for every `j` with `1 ≤ j < i` the square `s.shift d j` is empty
  (it is on the board, since it lies between two on-board squares);
- pawn: `t = s.offset df c.forward` with `df = ±1` (the capture diagonals; pawn pushes are not
  attacks).

The slider clause is in *index form*, not "a prefix of `s.ray d`". Symmetry (R3) is then plain
arithmetic: `s.shift d i = some t` iff `t.shift d.opposite i = some s`, and the in-between square
`j` from `s` is the in-between square `i − j` from `t`. `Reaches` is decidable by bounded
quantifiers over `i, j < 8`; the Lean form of "the square `s.shift d j` is empty" eliminates the
`Option` directly (no quantifier over all 64 squares), and `docs/spec/Rules.md` fixes it.

### 5.3 Attacks and check

- `Board.AttacksFrom b s t : Prop`: a piece stands on `s` and it reaches `t`
  (`Reaches q.kind q.color b s t` for the piece `q` on `s`; false if `s` is empty).
- `Board.Attacked b c t : Prop`: some square `s` holds a piece of colour `c` and that piece attacks
  `t` from `s`. The kind is read off the board, not quantified over.
- `Board.KingAttacked b c : Prop`: some square holding a king of colour `c` is attacked by
  `c.other`. With no king on the board this is false; with two kings it says "one of them".
- `InCheck p : Prop := p.board.KingAttacked p.turn`.

All are decidable by their own `Decidable` instances (quantifiers over `Square`). The executable
check test is `decide (InCheck p)`. The super-piece method (put each kind on the king's square and
look back, R3.3) is a later optimization proved equal.

### 5.4 `PseudoLegal`: one named predicate per rule

Writing `c := p.turn` and `b := p.board`, two **shape predicates** are defined first, because both
the legality rules and `play` need them (Principle 6):

- `Move.IsEnPassant p m`: `src` holds a pawn of colour `c`, `p.epTarget = some dst`, `dst` is empty,
  and `src.file ≠ dst.file`.
- `Move.IsCastle p w m`: `src` is `kingHome c` and holds `c`'s king, and `dst` is
  `kingCastleSquare c w`.

Then six named, decidable predicates, one per rule:

| Predicate | English (FIDE) |
|---|---|
| `StepMove p m` | `src` holds a non-pawn piece of colour `c`, it `Reaches` `dst`, `dst` is empty or holds a piece of colour `c.other`, and `promo = none`. (3.2–3.6, 3.8.1) |
| `PushMove p m` | `src` holds a pawn of colour `c`, `dst` is one square `c.forward` from `src` on the same file, `dst` is empty, and the promotion rule holds. (3.7.1) |
| `DoublePushMove p m` | `src` holds a pawn of colour `c` on relative rank 1, `dst` is two squares `c.forward` from `src` on the same file, the square between them and `dst` are both empty, and `promo = none`. (3.7.2) |
| `PawnCaptureMove p m` | `src` holds a pawn of colour `c`, it `Reaches` `dst`, `dst` holds a piece of colour `c.other`, and the promotion rule holds. (3.7.3) |
| `EnPassantMove p m` | `m.IsEnPassant p`; the pawn `Reaches` `dst`; `dst.relRank c = 5`; a pawn of colour `c.other` stands on the *victim square* (`dst`'s file, `src`'s rank); the victim's origin square (one square `c.forward` beyond `dst`) is empty; and `promo = none`. (3.7.3.1) |
| `CastleMove p w m` | `m.IsCastle p w`; `p.castling.get c w`; `rookHome c w` holds `c`'s rook; every square strictly between `kingHome c` and `rookHome c w` is empty; `c` is not in check; `rookCastleSquare c w` (the square the king crosses) is not attacked by `c.other`; and `promo = none`. (3.8.2) |

`PseudoLegal p m := StepMove p m ∨ PushMove p m ∨ DoublePushMove p m ∨ PawnCaptureMove p m ∨
EnPassantMove p m ∨ ∃ w, CastleMove p w m`.

**The promotion rule**: `promo` is `some _` exactly when `dst` is on relative rank 7. A pawn
reaching the last rank must promote, and nothing else may (3.7.5).

Design notes:

- A chess player reviews one row per article, exactly as with an inductive; `rcases h with h | h |
  h | h | h | ⟨w, h⟩` gives the same case split an inductive would. Unlike an inductive, the
  disjunction is decidable by instances, so `Legal` is decidable in Stage 1, without waiting for M4
  (see Section 5.7 for what that buys).
- Castling states *all* its preconditions, including that the king and rook are on their home
  squares, so that castling legality never relies on `WellFormed`. That the king does not *land* on
  an attacked square is not repeated here: it is the second half of `Legal`. On the queenside the
  b-file square must be empty but may be attacked; "strictly between king and rook" for emptiness
  versus "the square the king crosses" for attack says exactly this.
- `EnPassantMove` encodes "the enemy pawn has just advanced two squares" as far as a single position
  can: the target is on the right rank, the victim is a pawn beside the capturer, and the square it
  came from is empty. A hand-written FEN with a nonsensical target cannot produce a capture FIDE
  forbids. None of this relies on `WellFormed`.
- `PawnCaptureMove` and `EnPassantMove` are disjoint (`dst` occupied versus empty), and a king
  `StepMove` moves one file while `CastleMove` moves two. So a move satisfies at most one of the six
  predicates, which is what M5 (no duplicates) needs.
- Capturing a king is not excluded by `PseudoLegal`. In a well-formed position it cannot happen,
  because the side not to move is not in check (R9 corollary). Keeping it out of the rule avoids a
  condition FIDE does not state. The consequence for the game layer, and how `fen` avoids it, is in
  Section 6.4.

### 5.5 `play`: a short composition of named updates

`p.play m` is, in order, with `c := p.turn`:

1. **Move the piece.** Clear `src`, and put on `dst` the arriving piece
   `(p.board m.src).map (·.promote m.promo)`: the piece from `src`, promoted if `m.promo = some k`.
   (If `src` is empty, `dst` becomes empty; no theorem cares.)
2. **En passant.** If `m.IsEnPassant p`, clear the victim square (`dst`'s file, `src`'s rank).
3. **Castling.** If `m.IsCastle p w` for a wing `w`, move whatever stands on `rookHome c w` to
   `rookCastleSquare c w`.
4. **Rights.** For each colour `c'` and wing `w`, revoke `(c', w)` if `src` or `dst` equals
   `kingHome c'` or `rookHome c' w` (`Move.Revokes`; revocation by squares, Stockfish's
   `castlingRightsMask[from] | castlingRightsMask[to]`). This covers a king or rook moving from
   home and a rook being captured at home, including by a promoting pawn (*representation* §2.5).
   It reads no board. *Changed in `Chess.Rules` Round 4* from "if `src` holds a king of colour `c`,
   revoke both of `c`'s rights; revoke `(c', w)` if `src` or `dst` is `rookHome c' w`": the two
   rules differ only for rights held while the king or rook is away from home, or after a king is
   captured on its home square, and in neither case does either allow a castling FIDE forbids
   (spec/Rules design choice 8). The owner may revert it; spec/Rules §12 item 1 gives the
   alternative.
5. **En passant target.** If `src` holds a pawn and `dst` is two squares `c.forward` from `src` on the
   same file, set the target to the square between them; otherwise clear it.
6. **Turn.** Pass the turn: `(p.play m).turn = c.other`, unconditionally.

Steps 2 and 3 use the very predicates the legality rules use (Section 5.4), so `play` and
`PseudoLegal` cannot disagree on what counts as en passant or castling. In particular a pawn capture
onto an occupied en passant target square (possible only in a malformed position) is never treated
as en passant, and a pseudo-legal capture removes exactly one man (R7 holds without `WellFormed`).

Each step is a named function on boards or positions, so each frame lemma (R4) talks about one step.
`Move.touched p m` lists the squares steps 1–3 may change (source, destination, the victim square if
`m.IsEnPassant p`, the rook's two squares if `m.IsCastle p w`), and `play_board_of_not_mem` says every
other square is unchanged, for every move. `play_turn` is unconditional because the game layer's
alternation law (G1) needs it for all moves. The destination lemma needs no `movedPiece` helper
and no junk value: `(p.play m).board m.dst = (p.board m.src).map (·.promote m.promo)` for every
pseudo-legal `m` (steps 2 and 3 never write to `dst` then: the castling rook squares differ from the
king's landing square, and an en passant capture changes rank, so the victim square is not `dst`).

`Move.IsCapture p m := (p.board m.dst).isSome ∨ m.IsEnPassant p`.

### 5.6 Terminal positions

Word for word from FIDE 5.1.1 and 5.2.1, over `Legal`, not over the generator:

- `Checkmate p := InCheck p ∧ ∀ m, ¬ Legal p m`
- `Stalemate p := ¬ InCheck p ∧ ∀ m, ¬ Legal p m`

with `checkmate_or_stalemate` and their exclusivity (R11). Both are decidable already in Stage 1,
by enumerating all 64 × 64 × 5 candidate moves, which is fine for tests under `native_decide` but too
slow for certificates. The cheap decision goes through the generator in Stage 2 (M6).

### 5.7 The generator

`pseudoMoves p` enumerates, for each square holding a piece of the side to move, its targets by
kind: leapers from the jump lists, sliders by walking each `ray` until the first occupied square
(including it if it is an enemy), pawn pushes, double pushes, captures, en passant, the four
promotion choices on the last rank, and castling by checking `CastleMove` for each wing.

`legalMoves p := (pseudoMoves p).filter fun m => ¬ (p.play m).board.KingAttacked p.turn`.

This is the FIDE definition read as a program. Check masks and pin rays are later optimizations
proved equal to this filter. `perft` counts leaves of the tree of `legalMoves` (M7). The Stage 2
theorems are `mem_legalMoves` (`↔`, not list equality, so move order stays free) and
`legalMoves_nodup`.

**Stage 1 testing against the specification.** Because `Legal` is decidable, the test suite checks,
on every perft test position, both `∀ m ∈ legalMoves p, Legal p m` (soundness) and, by enumerating
all 64 × 64 × 5 candidate moves, `∀ m, Legal p m → m ∈ legalMoves p` (completeness). This is far
stronger evidence than perft counts alone, and it tests the generator against the very definition
M4 will relate it to.

---

## 6. Game semantics

### 6.1 The abstract game

`structure Game` (a structure, not a class, so that a morphism between two games on the same state
type is easy to name, G7) has: `State`, `Move`, `turn : State → Color`, `moves : State → List Move`,
`play : State → Move → State`, `Mated : State → Prop`, `decMated : DecidablePred Mated`,
`decEqMove : DecidableEq Move`, and two laws:

- **alternation**: a move in `moves x` passes the turn: `turn (play x m) = (turn x).other`;
- **a mated side has no moves**: `Mated x → moves x = []`.

Structure fields are not instances on projection, so the module registers
`attribute [instance] Game.decMated Game.decEqMove`. Without this every theorem would quietly need
`classical` or explicit arguments.

Every definition about games takes the game `G` as its **first explicit argument**, so that dot
notation reads naturally (`G.WinsIn a n x`) and `G` never has to be inferred from a state.

The interface is finite-branching by construction (`moves` is a `List`). Toy games (a subtraction
game, tic-tac-toe) instantiate it in tests, where everything is instant under `decide`.

*Stage 1 option, not a requirement:* a field `isLegal : State → Move → Bool` with the law
`isLegal x m = true ↔ m ∈ moves x`. Attacker nodes of a certificate could then check one move
instead of generating all of them (about 35 king-safety scans saved per attacker node). For chess it
would be `decide (Legal p m)`, which needs M4 for the law, so it waits for Stage 2 unless the kernel
cost of Section 7.4 forces it earlier.

### 6.2 Forcing a target, and winning

The basic notion is goal-directed (THEOREMS O8, Stage 1 decision 2):

`G.Forces a T n x`: the attacker `a` can force play into the target set `T` using at most `n`
attacker moves, whatever the defender does. Inductively:

1. **goal**: if `x` is in `T`, then `x` is forced within any budget `n`;
2. **move**: if `a` is to move at `x` and some move in `moves x` leads to a state forced within `n`,
   then `x` is forced within `n + 1`;
3. **replies**: if `a.other` is to move at `x`, **has at least one move**, and every one of its moves
   leads to a state forced within `n`, then `x` is forced within `n`.

`G.WinsIn a n x := G.Forces a (G.DefenderMated a) n x`, where `G.DefenderMated a x` says `a.other`
is to move and is mated. `G.Wins a x := ∃ n, G.WinsIn a n x`.

Why this shape:

- **The "at least one move" guard** is what makes a stalemated defender not lost. Without it the
  universal over an empty move list is vacuously true; dwrensha's `ForcedWin` has exactly this bug
  (*prior-work* §5). Stalemate is encoded nowhere: it is a state with no moves that is not mated,
  and the semantics simply cannot win there.
- **The index is a budget of attacker moves, and the goal holds at any budget.** So `WinsIn a n`
  means "within `n`", monotonicity (G3) is provable, and "exactly `n`" is the separate
  `G.MateIn a n x := G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x` (G6). An engine's "M3" means exactly
  3; a problem's "#3" means at most 3 with no shorter solution. Statements use `MateIn` for the first
  and `WinsIn` plus a lower bound for the second.
- **Forces is general for free.** Monotonicity, the search, the certificate checkers and their
  soundness and completeness are proved once for any decidable target. "Wins material by force",
  "promotes by force" and "reaches a position already certified won" reuse them, and
  `Forces.trans` composes a forced reach with a forced win (O8). Only `not_both` (G4) is
  mate-specific; the trap duality of Section 6.6 is stated for a general `T`.
- **The attacker is an explicit colour.** Claims are usually "White wins", and the prototype's
  proofs read well this way. The game value of Stage 3 (G10) is side-relative where that halves
  the work.

### 6.3 What the semantics proves in Stage 1

`Forces.mono` (G3), `WinsIn.not_both` (G4: no state is a forced win for both sides; the bridge from
"this wins" to "the alternatives are worse"), `winsIn_zero_iff` and `not_wins_of_stalemate` (G2),
and `MateIn.unique` (G6), all by induction on derivations.

**Decidability (G5).** Bounded minimax needs two functions, because a defender node does not
consume budget:

- `attackerForces : Nat → State → Bool`, by structural recursion on the budget:
  `attackerForces 0 x = T x`, and
  `attackerForces (n + 1) x = T x || (moves x).any (fun m => defenderForced n (play x m))`;
- `defenderForced n x := T x || (!(moves x).isEmpty && (moves x).all (fun m => attackerForces n (play x m)))`,
  which is not recursive itself (it calls `attackerForces` at the same `n`, and is unfolded inline
  in the recursive case above);
- `G.searchForces a T n x := if turn x = a then attackerForces n x else defenderForced n x`.

(`T x` here is `decide (T x)`; `T` must be a decidable predicate.) No fuel and no well-founded
recursion, so `decide` can run it (*lean-eng* §7). The alternation law is what makes "the children
of an attacker node are defender nodes" true. `searchForces_iff` gives `Decidable (G.Forces a T n x)`,
and with it every negative fact "there is no forced win within `k`" **for small `k`**.

*Feasibility.* A negative fact `¬ WinsIn a k x` must branch over every attacker move at each of `k`
attacker plies: about 35^k leaves. This is feasible for `k ≤ 2` or `3`, and nowhere near feasible for
`k = 10` (about 10^15 leaves, beyond both the kernel and `native_decide`). Exact `MateIn` is therefore
provable by search only for short mates. An exact `MateIn` for a long mate needs a mathematical
lower-bound argument and is out of scope for Stage 1.

**Only winning move (O2).** `G.OnlyWinningMove x m`: `m` is in `moves x`, the mover wins after `m`,
and after every other move in `moves x` the mover does not win. `OnlyWinningMove.wins_iff` is the
Stage 1 statement. Its optimality reading (`optimal_iff`) needs the value of Stage 3.

### 6.4 Chess as a game

`Game.chess : Game` (defined in `Chess.ChessGame`) has `State := Position`, `Move := Move`,
`turn := Position.turn`, `moves := legalMoves`, `play := Position.play`, and
`Mated p := InCheck p ∧ legalMoves p = []`. The alternation law is `play_turn`; the second law is
immediate from the definition of `Mated`.

The same module defines the names headline theorems use, each an `abbrev`:

- `Chess.WinsIn a n p := Game.chess.WinsIn a n p`, and likewise `Chess.MateIn`, `Chess.Wins` and
  `Chess.OnlyWinningMove` (and `Chess.Holds` in Stage 3).

So a headline reads `Chess.OnlyWinningMove (fen "…") (uci "…") ∧ Chess.WinsIn .black 11 (fen "…")`,
with no `(G := …)` annotations.

The instance uses the generator, not `Legal`, so that Stage 1 is not blocked on M4. Stage 2 proves
`m ∈ Game.chess.moves p ↔ Legal p m` and `Game.chess.Mated p ↔ Checkmate p` (G8), after which every
`Chess.WinsIn` theorem is a theorem about FIDE chess.

**Malformed positions.** `PseudoLegal` allows capturing a king (Section 5.4). If the side *not* to
move is in check, the side to move can capture that king; the kingless side is then never `InCheck`,
so never mated, and the semantics can never award a win against it. That is harmless (no false win
can be derived), but such a position is not chess. So `parseFEN` rejects it: besides syntax errors,
it rejects positions where a side does not have exactly one king, and positions where the side not
to move is in check. `fen "…"` positions in headlines therefore never hit this case. This is a
sanity filter in the parser, not `WellFormed`.

### 6.5 Which FIDE rules are in, which are out, and why

The primary game is **G∞** ("pure chess", *game-theory* §1.2): no clock, no repetition, and
infinite play is not a win for anyone.

| FIDE rule | In this draft? | Reason |
|---|---|---|
| Movement, incl. castling, en passant, promotion (Art. 3.1–3.8) | **In** | The rules of the move layer. |
| Check, and no move may leave one's own king attacked (3.9) | **In** | The second half of `Legal`. |
| Checkmate wins (5.1.1) | **In** | `Mated`, the only losing condition. |
| Stalemate draws (5.2.1) | **In** | Implicit: a stalemated defender is never lost (the guard in `replies`). |
| Dead position draws (5.2.2) | Out, Stage 4 | Deciding deadness is expensive. G11 shows a forced win never passes through a dead position, so excluding the rule does not change any `WinsIn` claim. |
| Threefold and fivefold repetition (9.2, 9.6.1) | Out, Stage 4 | In G∞ a forced win can always avoid repeating a position. G15 proves that under the actual rules, given a stated history hypothesis. Claim timing has an off-by-one hazard: FIDE 9.2.1.1 lets a player claim with a move that *would* produce the third occurrence, so the claim model must fix `R = 2` versus `3`, just as the 50-move rule must fix `L = 99` versus `100`. |
| 50- and 75-move rules (9.3, 9.6.2) | Out, Stage 4 | They *do* change some values (Syzygy's "cursed wins"). They enter as the clocked games `Clocked L`, separate `Game` instances whose states pair a position with a clock, and G12/G15 transfer wins with explicit clock headroom. |
| Illegal positions (3.10.3) | Partly | `WellFormed` (Stage 2) and `Reachable` (R10) are predicates; nothing assumes a position is reachable. `parseFEN` rejects the two cases of Section 6.4. |
| Resignation, agreement, time, arbiter rules (Art. 5.1.2, 5.2.3, 6–12) | Out, permanently | Not part of the game tree. |
| Chess960 castling | Out | Different castling geometry; not needed. |

The policy is: rules that cannot change who wins a forced line are proved irrelevant rather than
modelled; the one rule that can (the move counter) becomes a parameter of a separate game. Every
headline theorem says which game it is about.

### 6.6 Draws and optimality (later stages, shaped now)

Draws are certified by **traps** (G9), stated for a general target: `G.Trap a T S` says that no
state of `S` is in `T`, every attacker move from a state of `S` stays in `S`, and at every defender
state of `S` the defender either has some move that stays in `S` or has no moves at all. A defender
with no moves outside `T` is safe because `Forces`'s `replies` rule needs a move. The duality is
`holds_iff_not_forces`: no budget forces `T` from `x` exactly when `x` lies in some trap, a greatest
fixed point given by an invariant, with no `coinductive`. For `T := DefenderMated a` this is the
draw half; for other targets it says "cannot force material gain", and so on.

"Holding" is indexed by the defender: `G.Holds d x := ¬ G.Wins d.other x`, read "`d` holds at `x`".
The game value (G10), `Optimal` (O0) and the ladder of approximations (O3–O7) are defined from
`Wins` and `Holds`. Nothing in Stage 1 needs to change for them, because `Forces` already uses the
"at least one move" guard that the trap duality requires.

---

## 7. Certificates and the trust boundary

### 7.1 The pipeline

```
 Stockfish / python-chess / tablebase      (untrusted, outside Lean, in scripts/)
        │  proposes moves, orders replies, finds refutations
        ▼
 certificate as Lean data (a generated .lean file)
        │
        ▼
 checkWin a n x c = true          ← evaluated by the kernel (decide +kernel or rfl)
        │  checkWin_sound
        ▼
 G.WinsIn a n x                   ← a theorem about the specification
```

Lean never sees an engine score. A certificate is a strategy; the checker replays it against the
rules; the soundness theorem turns acceptance into the semantic claim. A wrong certificate fails to
check; it cannot produce a false theorem.

### 7.2 The certificate type and the checkers

`inductive Cert (M : Type)` has three constructors mirroring `Forces`: `goal`; `move m next` (the
attacker plays `m`); `replies rs` with `rs : List (M × Cert M)` (one subtree per defender reply).

`G.checkForces a T n x c : Bool` mirrors the three rules of `Forces`:

- `goal`: decide `T x`;
- `move m next`: `a` is to move, the budget has the form `k + 1`, `m ∈ moves x`, and `next` checks
  at `play x m` with budget `k`;
- `replies rs`: `a.other` is to move, `moves x` is non-empty, every move in `moves x` appears in
  `rs`, and every pair `(m, c)` in `rs` has `m ∈ moves x` and `c` checking at `play x m` with the same
  budget `n`.

**Recursion (Stage 1 decision 7).** `checkForces` and a helper over the reply list are defined by
mutual structural recursion on the certificate, which Lean 4.28 supports for this nested inductive.
A quick experiment for this design confirmed that such a checker evaluates under `decide`,
`decide +kernel` and `rfl`. The prototype's fuel parameter is gone: it was a number with no meaning
in the claim. Iterating over the reply list, rather than looking each defender move up in it, keeps
every recursive call structural; coverage ("every defender move appears") is a separate Boolean
conjunct.

`G.checkWin a := G.checkForces a (G.DefenderMated a)`. Theorems:

- `checkWin_sound : G.checkWin a n x c = true → G.WinsIn a n x` (C1);
- `checkWin_complete : G.WinsIn a n x → ∃ c, G.checkWin a n x c = true` (C2: the format is not lossy);
- `checkOnlyMove_sound` (C7). **Budget convention: the budget is counted at `x`, the position before
  the best move**, like every other budget in the library. `G.checkOnlyMove n k x best c refs` takes a
  win certificate `c` *at `x`* whose root is `move best _`, and for every other move in `moves x` a
  certificate in `refs` that the opponent wins within `k` after it. Acceptance gives
  `G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x`. The "does not win" half comes from
  `not_both`. So the headline `Chess.WinsIn .black 11 gotham` uses `n = 11` directly, with no
  subtraction anywhere. Refutations by traps (alternatives that only draw) are added in Stage 3 as a
  second kind of refutation.

### 7.3 Trust labels

Every headline theorem's docstring carries one label (THEOREMS §0.4):

- **[kernel]**: `#print axioms` shows at most `propext`, `Classical.choice`, `Quot.sound`.
- **[native]**: also `Lean.ofReduceBool` / `Lean.trustCompiler`, from `native_decide`. Such
  theorems have names ending in `_native` and live only in test or demonstration files, never in the
  six library modules.
- **[hyp: H]**: conditional on an explicit hypothesis in the statement, such as a tablebase
  soundness assumption. Never an `axiom`.

A test file records `#print axioms` for every headline theorem, so the labels are checked, not
claimed.

What a reader trusts for a Stage 1 chess theorem: the Lean kernel; the English and Lean of `Basic`,
`Position`, `Rules`, the definitions section of `Game`, and `ChessGame` (including the FEN and UCI
parsers until M11); and, until M4, `MoveGen` as the meaning of "legal". After Stage 2 the last item
disappears.

### 7.4 Keeping kernel checks affordable

The kernel reduces lazily, and long chains of unnormalized board updates are superlinear
(*lean-eng* §5). Two rules:

1. **Literal checkpoints.** A large certificate is compiled into one small theorem per node, each
   stating the position after a move as a literal: `p.play m = q` with `q` written as
   `⟨Board.unpack 0x…, turn, rights, ep⟩`, proved by `decide`. Glue lemmas (C3) chain them. The
   prototype's kernel-only mate in 11 used this pattern (320 theorems, about 80 s, about 6 GB).
2. **Short `set` chains.** Because each checkpoint restarts from an `unpack` literal, a board read
   costs at most a handful of comparisons plus two bignum operations.

**Checkpoint literals must follow this library's en passant convention** (Section 4.6: the target
is set after every double push). They are produced by Lean itself (`#eval` of `play`, then `pack`), or
by python-chess with `board.fen(en_passant="fen")`, **never** with python-chess's default
`en_passant="legal"`, which drops unusable targets and would make `p.play m = q` fail after a double
push. The `scripts/` README states this.

*Risk.* The function board is slower in the kernel than raw nibbles (about 1.4 s against 0.75 s for
20 chained moves, *lean-eng* §5), and the generator itself is not optimized. If the Stage 1
kernel-only demonstration proves too slow, the remedies in order are: a faster `Attacked` (super-piece
method, proved equal); the `isLegal` option of Section 6.1; then the fast layer of Section 3.3 with a
game morphism. The specification does not change in any case.

---

## 8. Modules of the first draft

Six modules in `Chess/`, built in this order. Each is one file, each has `docs/spec/<Module>.md` as
its English specification, `docs/process/<Module>.md` as the log of the English↔Lean back-and-forth,
and `docs/reviews/<Module>.md` as its file-level review. `Chess.lean` imports all six.

```
Basic ──► Position ──► Rules ──► MoveGen ──┐
  │                                         ├──► ChessGame
  └──► Game ────────────────────────────────┘
```

- `Game` imports `Basic` only for `Color`, which is the first section of `Basic` and changes rarely.
- `MoveGen` does **not** import `Game`: perft tests and the Stage 2 generator proofs never rebuild
  because game theory changed.
- `Rules` does **not** see the FEN/UCI parsers; they live in `ChessGame`, isolated and auditable.

Planned later files, given homes now so that the reviews have fixed targets (not part of the six):

| File | Stage | Contents |
|---|---|---|
| `Chess/MoveGen/Correct.lean` | 2 | M1–M6: `mem_ray_iff`, `mem_pseudoMoves`, `mem_legalMoves`, `legalMoves_nodup`, the cheap decision of `Checkmate`. Imports `MoveGen`. |
| `Chess/Invariants.lean` | 2 | `WellFormed`, `Reachable`, R6–R10. Imports `Rules`. |
| `Chess/ChessGame.lean` (extended) | 2 | G8: `Game.chess` means FIDE chess. Then imports `MoveGen.Correct`. |
| `Chess/Fast/*.lean` | 5 | Bitboards, refinement, game morphism. |

### 8.1 `Chess.Basic`: colours, kinds, pieces, squares, geometry

Depends on: nothing (core only).

A colour is White or Black, and `c.other` is the opponent (first section, so that `Game` can import
it cheaply). A kind is one of pawn, knight, bishop, rook, queen, king; a promotion choice is one of
knight, bishop, rook, queen, with its kind. A piece is a colour and a kind, and promoting a piece
keeps its colour and changes its kind. A square is a file and a rank, each from 0 to 7, a1 being
file 0 and rank 0. Each square has an index `8 · rank + file` in `Fin 64`, and this is a bijection
(R1). Every finite type has the list of all its values, without repeats, and quantifiers over it are
decidable (R2). A square can be shifted by a number of files and ranks; the result is a square or
"off the board". The eight compass directions each have a file step, a rank step and an opposite;
shifting `i` steps in a direction is the basic slider motion, and the ray from a square in a
direction is the list of squares met by repeatedly stepping that way, nearest first, until the edge.
A pawn of colour `c` moves in direction `c.forward` (+1 rank for White, −1 for Black); the relative
rank of a square for `c` is its rank counted from `c`'s side of the board; `c`'s home rank is the
absolute rank whose relative rank is 0. The king's and rooks' home squares and the castling squares
are computed from colour and wing. A square is light when file plus rank is odd. *Targets: R1, R2.*

### 8.2 `Chess.Position`: boards, moves, castling rights, positions

Depends on: `Basic`.

A board says, for each square, which piece stands there, if any. Setting a square replaces what is
on it and changes nothing else (`set_same`, `set_ne`, `set_comm`). Board equality is decidable by
comparing the 64 squares. A board can be written compactly as a number whose `i`-th group of four
bits is the code of the piece on the square with index `i`; the code table is defined once, unused
codes read as empty, and unpacking the packing of a board gives the board back. A move is a source
square, a destination square and an optional promotion choice; castling is written as the king's
two-square move. The castling rights record, for each colour and wing, whether that right is still
held; they are read by colour and wing and, by convention, only revoked. A position is a board, the
side to move, the castling rights and an optional en passant target. The initial position is the
standard one. Two positions are equal when they agree on all four fields, and this is decidable.
A position prints as a diagram.

### 8.3 `Chess.Rules`: attacks, legality, the effect of a move, terminal positions

Depends on: `Position`.

A piece of a given kind and colour on one square reaches another if the rule for its kind allows
it, reading only the squares strictly between: knights jump, kings step, sliders move along one of
their directions over empty squares, and pawns reach the two squares diagonally forward
(Section 5.2). A piece attacks from its square what it reaches. A square is attacked by a colour if
some piece of that colour attacks it; a colour's king is attacked if some square holding a king of
that colour is attacked by the other colour; the side to move is in check if its king is attacked.
A move has the shape of an en passant capture, or of a castling, by the shared predicates of
Section 5.4. A move is pseudo-legal if it satisfies one of the six rule predicates of Section 5.4.
Playing a move does the six steps of Section 5.5. A move is legal if it is pseudo-legal and, after
it, the mover's king is not attacked. A position is checkmate if the side to move is in check and
has no legal move, and stalemate if it is not in check and has no legal move. All of these are
decidable. The module ends with the frame lemmas for `play` (R4), the unconditional facts
`play_turn` and `castling_play_le` (R8), the square-colour sanity theorems for bishops and knights
(R5), and the terminal-position facts (R11). *Targets: R4, R5, R8, R11.*

### 8.4 `Chess.MoveGen`: the generator and perft

Depends on: `Rules`.

The pseudo-legal moves of a position are listed square by square: for each piece of the side to
move, its leaper jumps, its slider rays up to and including the first occupied square if that holds
an enemy, its pawn pushes, double pushes, captures and en passant capture, every promotion choice
when a pawn reaches the last rank, and each castling whose rule predicate holds. The legal moves are
the pseudo-legal moves after which the mover's king is not attacked. Perft of depth `n` counts the
sequences of `n` legal moves from a position. The perft regression facts and the generator-versus-
`Legal` checks (M7 and Section 5.7) live in a test file that imports this module and `ChessGame` (for
FEN), with kernel versions at small depths and `_native` versions deeper. The test positions are the
six standard perft positions plus five named bug-class positions: the three of THEOREMS M7, a
promotion capture onto a rook home square (b7xa8=Q must revoke Black's queenside right through
step 4's `dst` clause), and an en passant capture that is legal only because it removes the pawn
that, having just double-pushed, gives check. *Targets: M7 (in tests).*

### 8.5 `Chess.Game`: the abstract game, forced wins, search and certificates

Depends on: `Basic` (for `Color`).

The file has four sections; only the first is part of the trusted reading.

1. **Definitions.** A game has states, moves, a side to move, a finite list of moves in each state,
   a way to play a move, and a decidable notion of the side to move being mated, such that playing a
   listed move passes the turn and a mated side has no moves. The attacker forces a target set
   within a budget of attacker moves if the state is in the target; or if it is the attacker's turn
   and some listed move leads to a state forced within budget `n`, in which case the state is forced
   within `n + 1`; or if it is the defender's turn, the defender has a move, and every defender move
   leads to a state forced within the same budget. Winning within `n` is forcing the defender to be
   mated; mating in exactly `n` is winning within `n` and not within less; a side wins if it wins
   within some budget. A move is the only winning move if it is a listed move, the mover wins after
   it, and after no other listed move does the mover win.
2. **Laws.** More budget never hurts; no state is a win for both sides; a stalemated defender is
   never lost; exact distance to mate is unique.
3. **Search.** A bounded search, by an attacker function recursive on the budget and a defender
   function that is not, decides forcing.
4. **Certificates.** A certificate is a finite strategy tree: a goal leaf, an attacker move with a
   subtree, or a list of defender replies each with a subtree. The checker accepts a certificate at
   a state for an attacker, a target and a budget exactly when it follows the three rules of
   forcing: at a goal leaf the state is in the target; at a move node it is the attacker's turn, the
   budget is `k + 1`, the move is listed, and the subtree checks after it with budget `k`; at a
   replies node it is the defender's turn, the defender has a move, every listed defender move has a
   subtree, every subtree belongs to a listed move, and every subtree checks with the same budget.
   Acceptance implies the forcing claim (soundness), and every true forcing claim has an accepted
   certificate (completeness). The only-move checker accepts, with the budget counted before the
   best move, a win certificate whose root is the best move and, for every other listed move, an
   opponent's win certificate; acceptance implies that the best move is the only winning move and
   that the mover wins within the budget. Glue lemmas let a large certificate be checked as many
   small per-node theorems.

*Targets: G1 (interface), G2, G3, G4, G5, G6, O2 (`wins_iff`), C1, C2, C3, C7.*

### 8.6 `Chess.ChessGame`: chess as a game, and the notation of claims

Depends on: `MoveGen`, `Game`.

The chess game has positions as states, the legal-move list as its moves, `play` as its play, and
"in check with no legal moves" as mated; its two laws hold because `play` always passes the turn and
a mated side has an empty move list by definition. Chess-specialised names (`Chess.WinsIn`,
`Chess.MateIn`, `Chess.Wins`, `Chess.OnlyWinningMove`) abbreviate the game-generic ones at the chess
game. Positions are read from FEN and moves from UCI by parsers over `List Char`, so that `fen "…"`
reduces in the kernel. `parseFEN : String → Option Position` reads the four move-layer fields,
reads and ignores the two clock fields, and rejects a string that is not valid FEN, a position where
a side does not have exactly one king, and a position where the side not to move is in check.
`fen s` takes, as an automatically discharged argument, the proof that `parseFEN s` succeeded, so a
bad string is a compile-time error, never a silent default position. `uci` is analogous. `toFEN`
writes a position back. *Targets: G1 (chess instance); M11 later.*

### 8.7 Outside the six modules

- `test/` (or a `ChessTest` library): perft regressions, generator-versus-`Legal` checks, toy games
  for `Game`, sanity checks, and the `#print axioms` ledger.
- `scripts/`: the untrusted certificate generator (Python, Stockfish, python-chess), ported from the
  prototype's `gen_cert.py` to emit `Cert` values and literal checkpoints for this library, with the
  en passant rule of Section 7.4.
- **The Stage 1 closing demonstration** is a file built on top of the six modules once they compile.
  It proves, for the prototype's GothamChess position (Black to move), `Chess.WinsIn .black 11 gotham`
  and `Chess.OnlyWinningMove gotham (uci "b7b2")`, each **[kernel]**. Exact `MateIn` is demonstrated
  only for short mates (budget at most 3), where `searchForces` is feasible; its label, [kernel] or
  [native], is whatever the measurement allows. An exact `MateIn 11` for Gotham would need a
  mathematical lower-bound argument and is out of scope for Stage 1 (Section 6.3).

---

## 9. How the definitions make the first milestone provable

| Theorem | Definition shape that makes it go through |
|---|---|
| R1 `ofIndex_index`, `index_ofIndex` | `Square` as two `Fin 8`; `grind` or `simp [Fin.ext_iff]; omega` (*lean-eng* §4). |
| R2 `mem_all`, `all_nodup`, `Decidable ∀` | Enumerations listed once; `Square` quantifiers through core `Fin` quantifiers. |
| R3 attack symmetry (later) | Slider `Reaches` in index form via `Square.shift`; `Reaches` never reads `b s` or `b t`. |
| R4 frame lemmas, `play_turn`, destination lemma | `play` as a composition of `Board.set` steps; `set_ne` as `@[simp]`; turn update unconditional; arriving piece `(b src).map (·.promote promo)`, total. |
| R5 bishops keep, knights flip square colour | Bishop directions with `|df| = |dr|`; knight jumps a named list of eight offsets; `StepMove` carries `Reaches`. |
| R7 material (later) | `IsEnPassant` requires `dst` empty and is shared by `EnPassantMove` and `play`. |
| R8 `castling_play_le` | Step 4 only clears rights (`p.castling.get c w && !decide (m.Revokes c w)`); stated for every move. |
| R11 checkmate or stalemate, not both | Definitions phrased over `InCheck` and `∀ m, ¬ Legal p m`. |
| M7 perft facts, generator-versus-spec tests | `Position` has no clock; `legalMoves` is a plain filter; `Legal` decidable from day one; FEN parser for the test positions. |
| G1 `Game`, `Game.chess` | Game laws provided by `play_turn` and the definition of `Mated`; decidability fields registered as instances. |
| G2–G4, G6 | `Forces` with the "has a move" guard, goal at any budget, budget decremented only by attacker moves. |
| G5 `searchForces_iff` | `attackerForces` structural on the budget, `defenderForced` non-recursive; alternation law. |
| C1, C2 | Checker mirrors `Forces` rule by rule; mutual structural recursion; `DecidableEq Move`. |
| C3 | Literal checkpoints via `Board.unpack`; `DecidableEq Position`; checkpoints follow the en passant convention. |
| C7, O2 `wins_iff` | Budget counted at `x`; best move's certificate is a certificate at `x`; `not_both` plus `checkWin_sound`. |
| Headline elaboration | `G` an explicit first argument; `Chess.*` abbreviations at `Game.chess`. |

---

## 10. Decisions taken, and questions left open

Stage 1 decisions from THEOREMS §7, as decided here:

1. `Position` has no clock and no history. **Yes.**
2. `WinsIn` is an instance of a goal-directed relation. **Yes**, named `Forces` (THEOREMS calls it
   `Reach`; "White forces …" reads better).
3. `play` sets the en passant target after every double push. **Yes**; FIDE identity via
   `normalize` in Stage 4; certificate checkpoints follow the convention (Section 7.4).
4. `Legal` is "pseudo-legal and own king not attacked", with `KingAttacked` a total existential.
   **Yes.**
5. `PseudoLegal` has one named piece per rule. **Yes, revised:** six named decidable predicates
   joined by `∨`, not an inductive, so that `Legal` is decidable in Stage 1 (Section 5.4).
6. `WellFormed` is a predicate on plain data; no king-square fields. **Yes.**
7. Certificate checking recurses structurally on the certificate, without fuel. **Yes** (tested in
   Lean 4.28).

Also decided: `Game` is a structure, with the game an explicit first argument of every definition;
the chess instance is `Game.chess` and headlines use the `Chess.*` abbreviations; the attacker is an
explicit colour; `Game.chess.Mated` is executable (`InCheck p ∧ legalMoves p = []`) and bridged to
`Checkmate` in Stage 2; there is no `inCheck : Position → Bool` in Stage 1; promotion choices have
their own type; castling rights are four `Bool`s behind a `get` interface; `Board` is a `def`; en
passant and castling are each one shared shape predicate; the only-move budget is counted before
the best move; exact `MateIn` is claimed only for short mates.

Open, for the owner or for the spec phase:

- The exact Lean form of "the square `s.shift d j` is empty" and of `Attacked`'s "some square holds
  a piece of colour `c` that attacks `t`", chosen in `docs/spec/Rules.md` for readable proofs and a
  decision procedure that enumerates squares only, never kinds or pieces.
- Whether the FEN parser builds the board through `Board.unpack` of a computed number or through
  `set`s; benchmark under `decide +kernel` in the Stage 1 demonstration.
- Whether the only-move checker takes one refutation budget `k` for all alternatives or one per
  alternative (`docs/spec/Game.md`).
- Claim timing for the Stage 4 draw rules: `L = 99` or `100` for the 50-move rule, `R = 2` or `3`
  for threefold repetition (THEOREMS G15). Not needed now.

---

## 11. Decisions and rejected alternatives (response to the design critique)

Adopted as proposed, or with the small changes noted in the text: A1 (Sections 6.3, 8.7), A2
(Sections 2, 6.4; the field `Game.Move` keeps its name, see below), A3 and A4 (Sections 5.4, 5.5),
B1–B8 (Sections 1, 3, 4.1, 5.1, 5.4, 5.5, 6.2, 7.2, 8.5), B9 and B10 (Sections 4.5, 4.6; THEOREMS
edits in Section 12), B11 (THEOREMS edit), B12 (Section 6.6), B13 (Section 2 and the header; the
decision is: no executable `inCheck` in Stage 1), C1–C8 (Sections 5.2–5.7, 6.1, 6.3, 6.6), D1–D3
(Sections 4.3, 7.4), E3 (Section 8), F1–F4 (Sections 6.2, 6.4, 6.5, 8.4), and the smaller points G
(Sections 3.2, 4.1, 4.3, 6.1).

Rejected or adopted only in part, with the reason:

| Point | Decision | Reason |
|---|---|---|
| E1: a separate `Chess.Color` module | **Rejected**; `Color` is the first section of `Basic`, and `Game` imports `Basic`. | The first draft has a budget of six modules. `Basic` is small and becomes stable first, so the rebuild cost of the `Basic → Game` edge is negligible. The part of E1 that matters is adopted: `MoveGen` no longer imports `Game`, and the chess instance moved to `ChessGame`. |
| E2: split `Position` into `Board`, `Position` and `Notation` | **In part.** The parsers leave `Position` and go to `ChessGame`; `Board` stays in `Position`. | Isolating the trusted, unverified parser from `Rules` is the substance of E2, and it is done. A seventh module would exceed the budget; `Board` and its packing are about 100 lines and read naturally beside `Position`. The parser also needs `Rules` now (F3: it rejects positions where the side not to move is in check), so it could not sit under `Rules` anyway. Cost accepted: perft tests import `ChessGame` for FEN and so rebuild when `Game` changes. |
| (consequence of the module budget) `Game` and `Certificate` merged | **Merged** into `Chess.Game`, in four sections. | With `ChessGame` added, six modules forced one merge. `Game` already contained an executable decision procedure (`searchForces`), and certificates are a second one for the same semantics, so the merge follows the existing seam. The trusted reading is section 1 of the file only. If the file exceeds about 600 lines, certificates split off as `Chess.Game.Certificate` after the first draft. |
| A2: `Game.Move` "collides visually" with `Chess.Move` | **Kept.** | The field is always written qualified (`G.Move`, `Game.chess.Move`), and `Game.chess.Move` *is* `Chess.Move`, so the collision is a coincidence of meaning, not a confusion. Renaming it (`Action`) would make the abstract game read less like a game. The `Chess.Game` / `Chess.game` case collision is removed by `Game.chess`. |
| C1: certificate attacker nodes check `Legal` instead of generating | **Deferred** to the `isLegal` option of Section 6.1. | The law `isLegal x m = true ↔ m ∈ moves x` is M4 for chess, a Stage 2 theorem. Generating moves at attacker nodes is correct now and its cost is measured first. |
| C4: `AttacksFrom` as the exact Lean form | **Adopted in English; Lean form open** (Section 10). | The spec phase should compare a `match` on `b s`, an `Option` membership and a helper predicate for proof ergonomics; the English is fixed. |

---

## 12. Edits `docs/THEOREMS.md` needs to follow this design

Not made here (the theorem architect owns that file); listed so the two documents converge.
Made since by the `Chess.Position` refiner (Round 4, `docs/process/Position.md`): the §0.5
`CastlingRights` and `Option PromoKind` renames, R2's list of enumerated types, R4's simp list, the
R6 hazard and `get c w` wording, and the unconditional R8.

- §0.5: add "The names in DESIGN §2 are authoritative; this file follows them." Rename `Castling`
  to `CastlingRights` (fields read by `get c w`), `promo : Option Kind` to `Option PromoKind`,
  `Reach` to `Forces`, `searchWin` to `searchForces`, `Cert.mate` to `Cert.goal`, `pawnCapture` to
  `PawnCaptureMove`, `Castling.get c side` to `get c w`, and the inductive `PseudoLegal` to the
  disjunction of Section 5.4.
- §1 and §7: the headline is `Chess.OnlyWinningMove gotham (uci "b7b2") ∧ Chess.WinsIn .black 11
  gotham` (Gotham is Black to move). Exact `MateIn` only for short mates; delete "exactly 11, using
  G5 or C4 for the lower bound", and change G5's and C4's "Why it matters" to say the same.
- §1: replace "Every other legal move allows the opponent at least a draw. Therefore `m` is the
  unique optimal move." with "After every other legal move, the mover has no forced win. (That this
  makes `m` the unique optimal move is O2, Stage 3.)"
- R4: `play_board_dst` becomes `(p.play m).board m.dst = (p.board m.src).map (·.promote m.promo)`
  under `PseudoLegal p m`; no `movedPiece`.
- R6 hazard: `p.castling = CastlingRights.none` (all four rights false).
- R7: holds as stated under `PseudoLegal`, because `IsEnPassant` requires `dst` empty; cite it.
- R8: unconditional, `(p.play m).castling ≤ p.castling` for every `m`.
- R9.4: "a pawn of colour `p.turn.other` stands one square beyond the target, away from
  `p.turn.other`'s home rank, and both the target and the square behind it are empty."
- M3: delete `inCheck_eq_true_iff` (there is no executable `inCheck`); the super-piece test, when
  added, gets its own equation with `InCheck`. G1 and M4: `InCheck p`, not `inCheck p = true`.
- C7 and O2: the budget is counted at `x`; the conclusion is `OnlyWinningMove x best ∧
  WinsIn (turn x) n x`.
- G9 and O6: traps are `Trap a T S` for a general target; `Holds d x := ¬ Wins d.other x`, indexed by
  the defender (drop the reminder comment in O6).
- G15: flag `R = 2` versus `3` for the repetition claim alongside `L = 99` versus `100`.
- G-tier statements: `G` is an explicit first argument (`G.WinsIn a n x`); chess statements use
  `Chess.WinsIn` and friends; `Chess.game` is `Game.chess`.
- M7: add the two bug-class positions of Section 8.4, and the generator-versus-`Legal` checks.
