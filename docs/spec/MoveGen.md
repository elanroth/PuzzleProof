# Specification of `Chess.MoveGen`

Role: English specification writer (Round 1); translator (Round 2, answering the Round 1 English
critique); refiner (Round 4, answering the Lean critique F1–F6, R1–R6, P1–P6).
Date: 2026-11-01.
Status: Round 4, matched to the refined `Chess/MoveGen.lean` (built; no `sorry`); Round 2
answered the English critique (A1–A8, B1–B14, C1–C4, D), Round 4 the Lean critique. Every definition,
every lemma tagged [core] and every test below was elaborated in a scratch file importing the built
`Chess.Rules` (scratchpad only; nothing in the library was written), and is marked *(checked)*.
Timings are from that scratch file, on this machine, one process at a time.

File: `Chess/MoveGen.lean`. Depends on: `Chess.Rules` (and through it `Chess.Position`,
`Chess.Basic`); core only. Does **not** import `Chess.Game`. Refines DESIGN §5.7 and §8.4. Theorem
targets here: **M1** (target lists mean `Reaches`), **M4** in both halves (`legalMoves_sound`,
`legalMoves_complete`, `mem_legalMoves`), **M2** and **M6** through one cover lemma (§7), and the
perft definitions and equations that **M7**'s tests use. Planned in `Chess/MoveGen/Correct.lean`:
**M5**.

What a reader must trust from this module: nothing. That every move it lists is legal is L3.5, by
the shape of the definitions (design choice 1); that it misses none is the cover L7.1.

## 0. How to read this document

The conventions of `docs/spec/Basic.md` §0, `docs/spec/Position.md` §0 and `docs/spec/Rules.md` §0
apply unchanged:

- Each definition has an ID (`D2.4`), its Lean name and type, its Lean body, and a **docstring** in
  quotation marks; the Lean docstring is that text, word for word.
- Each lemma has an ID (`L1.2`), an English statement, the Lean statement, and a tag: **[core]**
  (proved in this file; later modules or the Stage 2 proofs depend on it), **[sanity]** (checks a
  definition says what its docstring says), or **[later]** (shaped now, proved in
  `Chess/MoveGen/Correct.lean`; the translator does not write it here). The Lean docstring of a
  lemma is its English column.
- **Binding rule.** Every name a docstring mentions is bound in the signature or introduced by the
  docstring itself.
- `autoImplicit = false`. Each section opens with the `variable` line given for it.
- `@[simp]` is written on every lemma that carries it; a lemma whose cell does not say `@[simp]`
  does not carry it.
- Everything lives in `namespace Chess`; names are given without the prefix. "Rules D4.6",
  "Basic B5.18" refer to the other specs.
- Squares in examples are written by their algebraic names; the Lean writes `⟨file, rank⟩` with
  the name in a comment, as in Rules §10.
- "**Generator**" means `legalMoves` and everything it is built from. "**Specification**" means
  `Chess.Rules` (`Reaches`, `PseudoLegal`, `Legal`, `play`).

Letters used in this module: `p` a position; `m` a move; `c` a colour; `w` a wing; `k` a kind; `pc`
a piece; `pk` a promotion kind; `o` a promotion choice (`Option PromoKind`); `b` a board; `s` the
source square, `t` a target square; `d` a direction; `l` a list of squares, `ts` the rest of a
list after its first square; `i j` list indices or numbers of steps (`Nat`), except in D1.3, where,
as in `Reaches`, `j` is a knight jump (`Int × Int`); `n` a perft depth.

### The idea of the module, in one paragraph

The generator **proposes and the rules dispose**. For each piece of the side to move, geometry
alone proposes a short list of *candidate moves*: where a knight could jump, how far a rook could
slide before it meets a piece, the four squares a pawn might go to, and the king's castling moves
if the rights are still held and the king stands on its home square. Then the specification
decides: `pseudoMoves` keeps the candidates that `PseudoLegal` allows, and `legalMoves` keeps those
after which no king of the mover's colour is attacked. The generator never decides a rule itself.
Every other test it makes (the colour and kind of the piece on a square, empty squares and blockers,
the edge of the board, the two guards of `castleCandidates`) only removes candidates, so none can
add an illegal move: everything it lists is legal by a one-line theorem (L3.5, Stage 1), because
the last filter is `Legal`'s own second conjunct. Completeness needs only that no such test removes
a pseudo-legal move, so the whole of M4's difficulty collapses into one geometric fact, "every
pseudo-legal move is a candidate" (L7.1), which needs no reasoning about checks, pins, en passant
victims or castling attacks. L7.1 is proved (§7), so nothing here is trusted.

## Contents of the file, in order

1. Targets: `Board.upToBlocker`, `slideTargets`, `reachTargets` (the list form of `Reaches`, M1).
2. Candidates: `pawnTargets`, `pawnMovesTo`, `Move.castle`, `candidatesFrom`, `castleCandidates`,
   `candidates`.
3. The generator: `pseudoMoves`, `legalMoves`.
4. Perft: `perft`, `perftDivide`.
5. Testing against the specification: `legalMovesBySpec`, `agreesWithLegal` (and the lemmas
   `mem_legalMovesBySpec`, `mem_legalMoves_of_agreesWithLegal`, `nodup_legalMoves_of_agreesWithLegal`).
6. Tests.

Sections 7–10 of this document are the Stage 2 plan (`Chess/MoveGen/Correct.lean`), the design
choices, the open items and the translator's checklist.

---

## 1. Section "Targets"

The list forms of `Slides` and `Reaches` (Rules D2.1, D2.2). Like `Reaches`, whether a square `t`
is listed does not depend on what stands on the source or on `t` itself (L1.3 with Rules'
`reaches_set_src`/`reaches_set_dst`); the list as a whole does read the board, since an occupied
square ends a ray. Whether a target may be *moved to* is the rules' business (`StepMove`'s "does
not hold a piece of its own colour").

`variable {b : Board} {l : List Square} {s t : Square} {d : Direction} {k : Kind} {c : Color}`

### D1.1 `Board.upToBlocker (b : Board) : List Square → List Square`

```lean
def Board.upToBlocker (b : Board) : List Square → List Square
  | [] => []
  | t :: ts =>
    match b t with
    | none   => t :: b.upToBlocker ts
    | some _ => [t]
```

Docstring: "The squares of the list, in order, up to and including the first one that is occupied
on `b`; the whole list if every square of it is empty on `b`."

Notes. Structural recursion on the list, so it reduces under `decide +kernel` (*lean-eng* §7). It
is a general list operation, not a ray operation, so its one lemma (L1.1) is about lists; rays enter
only in L1.2. The `match` on `b t` (not `if b t = none`) needs no `Decidable` instance and is what
the proof of L1.1 splits on *(checked)*.

### D1.2 `slideTargets (d : Direction) (b : Board) (s : Square) : List Square`

```lean
def slideTargets (d : Direction) (b : Board) (s : Square) : List Square :=
  b.upToBlocker (s.ray d)
```

Docstring: "The squares a piece sliding from `s` in direction `d` reaches on `b`, nearest first:
the squares 1, 2, … steps from `s` in direction `d` as far as the edge of the board (`s` itself
excluded), up to and including the first occupied one, or all of them if none is occupied. Empty
if the step from `s` leaves the board."

Notes. Argument order `d b s` is `Slides d b s t` without the `t`, so that L1.2 reads
`t ∈ slideTargets d b s ↔ Slides d b s t`. This is the "ray walk" of DESIGN §5.7 and of the Rules
review C3.1: each square of the ray is read once, nearest first, and the walk stops at the first
blocker.

### D1.3 `reachTargets (k : Kind) (c : Color) (b : Board) (s : Square) : List Square`

```lean
def reachTargets (k : Kind) (c : Color) (b : Board) (s : Square) : List Square :=
  match k with
  | .pawn   => [s.offset (-1) c.forward, s.offset 1 c.forward].filterMap id
  | .knight => knightJumps.filterMap fun j => s.offset j.1 j.2
  | .king   => Direction.all.filterMap fun d => s.shift d 1
  | .bishop | .rook | .queen => k.slideDirections.flatMap fun d => slideTargets d b s
```

Docstring: "The squares a piece of kind `k` and colour `c` would reach from `s` on `b`, whatever
stands on `s`, as a list (the list form of `Reaches`): for a pawn the squares diagonally forward,
for a knight the squares a knight's jump away, for a king the adjacent squares, and for a bishop,
rook or queen the squares along each of its directions up to and including the first occupied one.
Jumps and steps that would leave the board give no square."

Notes.
- The `match` has exactly the arms of `Reaches` (Rules D2.2), in the same order, each built from the
  same expression the `Reaches` arm compares with `some t`: `s.offset (-1) c.forward` and
  `s.offset 1 c.forward`; `s.offset j.1 j.2` for `j ∈ knightJumps`; `s.shift d 1`; `Slides d b s`
  for `d ∈ k.slideDirections`. A reader checks D1.3 against D2.2 line by line, and L1.3 is the proof
  that they agree.
- The king's arm enumerates `Direction.all` where `Reaches` says `∃ d : Direction`; `Direction.mem_all`
  bridges them.
- The pawn arm is the capture diagonals only (`Reaches` does not include pushes). Pushes are
  `pawnTargets`' business (D2.1).
- Order: knight jumps in `knightJumps` order, king steps in `Direction.all` order (N, E, S, W, NE,
  SE, SW, NW), slider directions in `k.slideDirections` order (a bishop's list is
  `Direction.diagonals`), each ray nearest first. Not part of any contract.

### Lemmas of §1

| ID | English (= Lean docstring) | Lean statement | Tag |
|---|---|---|---|
| L1.1 | `t` is listed by `b.upToBlocker l` exactly when, for some `i`, `t` is entry `i` of `l` and every entry before `i` is empty on `b`. | `theorem Board.mem_upToBlocker : t ∈ b.upToBlocker l ↔ ∃ i : Nat, l[i]? = some t ∧ ∀ j < i, l[j]?.bind b = none` | [core] *(checked)* |
| L1.2 | **The squares listed by `slideTargets d b s` are exactly those a piece sliding from `s` in direction `d` reaches on `b`.** | `theorem mem_slideTargets : t ∈ slideTargets d b s ↔ Slides d b s t` | [core, M1] *(checked)* |
| L1.3 | **The squares listed by `reachTargets k c b s` are exactly those a piece of kind `k` and colour `c` reaches from `s` on `b`.** | `theorem mem_reachTargets : t ∈ reachTargets k c b s ↔ Reaches k c b s t` | [core, M1] *(checked)* |
| L1.4 | The squares up to the first blocker are a sublist of the list. | `theorem Board.upToBlocker_sublist (b : Board) (l : List Square) : (b.upToBlocker l).Sublist l` | [later, M5] |
| L1.5 | A target list names each square once. | `theorem reachTargets_nodup (k : Kind) (c : Color) (b : Board) (s : Square) : (reachTargets k c b s).Nodup` | [later, M5] |

Proof notes *(checked)*.
- L1.1: induction on `l`; in the `cons` case `unfold Board.upToBlocker; split`. The `none` branch is
  `List.mem_cons` plus the induction hypothesis with indices shifted by one (`cases i`, `cases j`,
  `simpa`, `omega`); the `some` branch is `List.mem_singleton`, and index `i + 1` is impossible
  because entry 0 is not empty. About 25 lines.
- L1.2: `rw [slideTargets, Board.mem_upToBlocker, slides_iff]; simp only [Square.getElem?_ray]`
  turns entry `i` of the ray into `s.shift d (i + 1)` (Basic B5.18); then shift the index by one
  each way, with `omega`. Rules' `slides_iff` (sliding with no bound on the number of steps) removes
  the bound `i < 8` from the goal, so no edge-of-board argument is needed. About 10 lines.
- L1.3: `cases k`; pawn by `List.mem_filterMap` (6 lines), knight by
  `simp [reachTargets, Reaches]`, king by `simp [reachTargets, Reaches, Direction.mem_all]`, the
  three sliders by `simp [reachTargets, Reaches, mem_slideTargets]`.
- L1.5 needs `knightJumps_nodup`, `Direction.all_nodup`, `Square.steps_eq_of_offset_eq`,
  `Square.dir_eq_of_shift_eq` (two directions never reach the same square at a positive distance),
  `Square.ray_nodup` and L1.4.

M1 sits here, not in `Correct.lean` as DESIGN §8's table says, because D1.2 and D1.3 make promises
in their docstrings ("exactly the squares it reaches"), the proofs are short and already checked,
and a promise in a docstring should be a theorem in the same file (design choice 8).

---

## 2. Section "Candidates"

`variable {c : Color} {s t : Square} {m : Move} {p : Position} {w : Wing}`

### D2.1 `pawnTargets (c : Color) (s : Square) : List Square`

```lean
def pawnTargets (c : Color) (s : Square) : List Square :=
  [s.offset 0 c.forward, s.offset 0 (2 * c.forward), s.offset (-1) c.forward,
    s.offset 1 c.forward].filterMap id
```

Docstring: "The squares a pawn of colour `c` on `s` might move to, in this order: one square
straight forward, two squares straight forward, and the two squares diagonally forward, towards the
a-file first. Squares that would be off the board are left out. Which of them it may move to now is
for the pawn rules to say."

Notes.
- With `c := p.turn` and `s := m.src` (as D2.4 calls it), each entry is, character for character,
  the expression the corresponding rule compares with `some m.dst`: `PushMove`
  (`m.src.offset 0 p.turn.forward`), `Move.IsDoublePush` (`m.src.offset 0 (2 * p.turn.forward)`),
  and `Reaches .pawn` (the two diagonals, which `PawnCaptureMove` and `EnPassantMove` use). So the
  cover lemma's pawn cases are `simp [pawnTargets, h]` with the rule's own hypothesis `h`.
- The list does not depend on the board or on the pawn's rank. A pawn not on its second rank still
  proposes its double push, and `DoublePushMove` rejects it. A pawn on its own back rank (relative
  rank 0, which no game reaches) proposes a one-square push to relative rank 1, and `PushMove`
  accepts it, since `PushMove` reads no rank: here the specification, not the generator, differs
  from FIDE, and the generator follows the specification. A pawn on its last rank proposes nothing
  (every forward square is off the board).

### D2.2 `pawnMovesTo (c : Color) (s t : Square) : List Move`

```lean
def pawnMovesTo (c : Color) (s t : Square) : List Move :=
  if t.relRank c = 7 then PromoKind.all.map fun pk => ⟨s, t, some pk⟩ else [⟨s, t, none⟩]
```

Docstring: "The moves of a pawn of colour `c` from `s` to `t`: one for each promotion choice
(knight, bishop, rook, queen) if `t` is on `c`'s last rank, otherwise the one move with no promotion
choice."

Notes.
- This is `Move.PromotionRule` (Rules D3.5) read as a list; L2.1 says so. It is the only place the
  generator produces promotion choices, so the Lean-Hackathon bug (a position whose only moves are
  promotions reported as having none, *prior-work* §6) cannot arise once L7.1 is proved: every pawn
  candidate onto the last rank comes with all four choices, and `PawnCaptureMove`/`PushMove` accept
  exactly those. Until then it is what `agreesWithLegal` tests.
- The choice depends only on `t`, whatever the rule. Double-push and en passant destinations are on
  relative ranks 3 and 5, so they always get `none`, which is what `DoublePushMove` and
  `EnPassantMove` require.

### D2.3 `Move.castle (c : Color) (w : Wing) : Move`

```lean
def Move.castle (c : Color) (w : Wing) : Move := ⟨kingHome c, kingCastleSquare c w, none⟩
```

Docstring: "The castling move of colour `c` to wing `w`, as data: the king from its home square to
its castling square on wing `w`, with no promotion choice (e1g1, e1c1, e8g8, e8c8)."

Notes. Tests and certificates name castling moves with it (`Move.castle .white .kingside`), so no
test writes `⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩` by hand. It may move to `Chess.Rules` later (open item 3).

### D2.4 `candidatesFrom (p : Position) (s : Square) : List Move`

```lean
def candidatesFrom (p : Position) (s : Square) : List Move :=
  match p.board s with
  | some ⟨c, k⟩ =>
    if c = p.turn then
      if k = .pawn then (pawnTargets p.turn s).flatMap (pawnMovesTo p.turn s)
      else (reachTargets k p.turn p.board s).map fun t => ⟨s, t, none⟩
    else []
  | none => []
```

Docstring: "The candidate moves from `s` in `p`, proposed by geometry alone. For a pawn of the side
to move on `s`: a move to each of its pawn targets, with every promotion choice when the target is
on the last rank. For any other piece of the side to move on `s`: a move with no promotion choice to
each square it reaches. None if `s` is empty or holds a piece of the side not to move. Castling
moves are not proposed here (`castleCandidates`)."

Notes.
- The piece is read once, by the `match`, and its colour `c` and kind `k` are tested in the order a
  player would say them, the side to move first. Both branches then use `p.turn`, not `c`, so the
  target lists are built from the very expressions the rules use (`Reaches k p.turn …`,
  `m.src.offset 0 p.turn.forward`), and the cover lemma needs no rewrite `c = p.turn`. For a king
  this proposes its steps only; castling is D2.5.
- The arms come in the docstring's order (an occupied square first, the empty square last), so the
  docstring and the body can be read side by side.
- "Proposed by geometry alone": a candidate may land on a piece of its own colour, push into a
  piece, double-push from the wrong rank, capture diagonally onto an empty square that is not the en
  passant target, and so on. The filter in D3.1 removes all of these.

### D2.5 `castleCandidates (p : Position) : List Move`

```lean
def castleCandidates (p : Position) : List Move :=
  if p.board (kingHome p.turn) = some ⟨p.turn, .king⟩ then
    (Wing.all.filter (p.castling.get p.turn)).map (Move.castle p.turn)
  else []
```

Docstring: "The candidate castling moves of `p`. If a king of the side to move stands on that
colour's king home square (e1 or e8): the move `Move.castle p.turn w` for each wing `w` on which the
side to move still holds the castling right, kingside first. Otherwise none."

Notes on the shape. The king clause does not depend on the wing, so it is tested once, outside;
the rights clause is a filter on `Wing.all` by the Boolean flag itself (no `= true`). Body and
docstring read in the same order. (Round 4; the Round 3 body, a `filterMap` over an `if` on both
clauses, was proved equal in scratch.)

Notes.
- **Why the king clause.** Without it, a position holding a castling right with a *queen* on e1
  (excluded by `WellFormed`, but `legalMoves` is stated for every position) would propose e1g1
  twice: once from the queen (a slide) and once as castling. Both copies are `PseudoLegal` (the
  first is a `StepMove`), so `legalMoves` would list e1g1 twice and M5 (`legalMoves_nodup`, stated
  without `WellFormed`) would be false. With the clause, a castling candidate's source holds a king,
  whose own candidates are one-square steps, never the two-square castling move.
- **Why the rights clause.** It is implied by `CastleMove` (through `Position.CanCastle`). It
  changes `candidates`, but not `pseudoMoves` or `legalMoves`: without the right, the castling
  candidate is not `CastleMove`, and with a king on its home square it is not a `StepMove` either
  (a king does not reach its castling square). It is kept because it makes `candidates` tighter at
  the cost of one flag read, not for speed: `CastleMove.decidable` tests `IsCastle` first,
  `CanCastle`'s first conjunct is the right itself, and core's `And` instance stops at the first
  false conjunct, so without the clause a missing right also costs about one flag read. (Round 3
  claimed it saved two attack scans per wing; that claim was wrong and is withdrawn. No compiled
  benchmark was run.)

### D2.6 `candidates (p : Position) : List Move`

```lean
def candidates (p : Position) : List Move :=
  Square.all.flatMap (candidatesFrom p) ++ castleCandidates p
```

Docstring: "The candidate moves of `p`: the candidate moves from every square, in square order (a1,
b1, …, h8), then the candidate castling moves. Every pseudo-legal move of `p` is a candidate (the
cover, `PseudoLegal.mem_candidates`); in general some candidates are not pseudo-legal."

Notes. The second sentence of the docstring is L7.1, proved in §7 of this module. On the empty board there are no candidates
(no piece, and castling needs the king), so `legalMoves` is empty and `perft (n + 1)` is 0 there. In the initial position there
are 56 candidates (30 pawn, 6 knight, 4 bishop, 4 rook, 5 queen, 5 king, 2 castling) and 20
pseudo-legal moves *(checked)*.

### Lemmas of §2

| ID | English (= Lean docstring) | Lean statement | Tag |
|---|---|---|---|
| L2.1 | **A pawn move list holds exactly the moves from `s` to `t` that obey the promotion rule for colour `c`.** | `theorem mem_pawnMovesTo : m ∈ pawnMovesTo c s t ↔ m.src = s ∧ m.dst = t ∧ m.PromotionRule c` | [core] *(checked)* |
| L2.2 | A castling to wing `w` is the castling move of the side to move to `w`. | `theorem CastleMove.eq_castle (h : CastleMove p w m) : m = Move.castle p.turn w` | [core] *(checked)* |
| L2.3 | A candidate from `s` moves from `s`. | `theorem src_of_mem_candidatesFrom (h : m ∈ candidatesFrom p s) : m.src = s` | [later, M5] |
| L2.4 | The candidates name each move once. | `theorem candidates_nodup (p : Position) : (candidates p).Nodup` | [later, M5] |
| L2.5 | The candidates do not read the en passant target: changing it leaves them unchanged. | `theorem candidates_ignores_epTarget (e : Option Square) : candidates { p with epTarget := e } = candidates p` | [core] *(checked, `rfl`)* |

Proof notes *(checked)*. L2.1: `rcases m with ⟨s', t', o⟩; unfold pawnMovesTo Move.PromotionRule;
by_cases h : t.relRank c = 7 <;> cases o <;> simp [h, PromoKind.mem_all, eq_comm] <;> rintro rfl
rfl <;> omega`: after `simp` each of the four cases is "same source and target imply the rank
fact", closed by substituting and `omega` (Round 4; the Round 3 proof ended in `simp_all … <;>
grind`, which hid which step did the work). L2.2: `obtain ⟨⟨hs, -, hd⟩, -, hp⟩ :=
h; cases m; simp_all [Move.castle]`. L2.4 needs `Square.all_nodup`, L2.3, `PromoKind.all_nodup`,
L1.5, `Square.steps_eq_of_offset_eq` with `c.forward ≠ 0` (the four pawn targets differ), and for
the castling candidates: the king's steps from `kingHome c` never reach `kingCastleSquare c w`
(Rules' private `shift_kingHome_one_ne`, which the Rules review C5 asks to move to Basic). L2.5:
`rfl`, because `candidatesFrom` reads only `p.board` and `p.turn`, and `castleCandidates` also
`p.castling` (design choice 13). It is the reason G16 (`legalMoves_normalize`) can be stated as list
equality: it then reduces to `List.filter_congr` pointwise.

---

## 3. Section "The generator"

`variable {p : Position} {m : Move}`

### D3.1 `pseudoMoves (p : Position) : List Move`

```lean
def pseudoMoves (p : Position) : List Move :=
  (candidates p).filter fun m => decide (PseudoLegal p m)
```

Docstring: "The pseudo-legal moves of `p`: the candidate moves that obey the movement rules
(`PseudoLegal`)."

Notes. "The pseudo-legal moves of `p`" is the completeness claim M2 (L7.2), proved in §7 of this
module (design choice 8: a promise is proved in the file that makes it).

### D3.2 `legalMoves (p : Position) : List Move`

```lean
def legalMoves (p : Position) : List Move :=
  (pseudoMoves p).filter fun m => decide (¬ (p.play m).board.KingAttacked p.turn)
```

Docstring: "The legal moves of `p`: the entries of `pseudoMoves p` after which no king of the
mover's colour is attacked (FIDE 3.9.2)."

Notes. As for D3.1: "the legal moves of `p`" is M4 (L7.4), proved in §7 of this module. The filter's condition is, word for word,
the second conjunct of `Legal` (Rules D6.1), so D3.1 and D3.2 together are "the candidates that are legal" (L3.3), DESIGN §5.7's sentence read as a
program. Both use the `Decidable` instances fixed in `Chess.Rules`; see design choice 10 for what
that means for speed-ups.

`legalMoves` is total and faithful to `Legal` on every position. On positions no game reaches, `Legal`
itself admits unusual moves, and so does the generator: if the side to move has no king,
`KingAttacked` is false, so `legalMoves p = pseudoMoves p`; if the side not to move is in check,
`legalMoves` includes captures of that king, because `StepMove` and `PawnCaptureMove` allow
capturing any piece of the other colour.

### Lemmas of §3

| ID | English (= Lean docstring) | Lean statement | Tag |
|---|---|---|---|
| L3.1 | `m` is in `pseudoMoves p` exactly when it is a candidate of `p` and pseudo-legal in `p`. | `theorem mem_pseudoMoves_iff_candidate : m ∈ pseudoMoves p ↔ m ∈ candidates p ∧ PseudoLegal p m` | [core] *(checked)* |
| L3.2 | Every entry of `pseudoMoves p` is pseudo-legal in `p`. | `theorem pseudoMoves_sound (h : m ∈ pseudoMoves p) : PseudoLegal p m` | [core] *(checked)* |
| L3.3 | **`legalMoves p` is `candidates p` filtered by `Legal`, in the same order.** | `theorem legalMoves_eq_filter (p : Position) : legalMoves p = (candidates p).filter fun m => decide (Legal p m)` | [core] *(checked)* |
| L3.4 | `m` is in `legalMoves p` exactly when it is a candidate of `p` and legal in `p`. | `theorem mem_legalMoves_iff_candidate : m ∈ legalMoves p ↔ m ∈ candidates p ∧ Legal p m` | [core] *(checked)* |
| L3.5 | **Every entry of `legalMoves p` is legal in `p` (M4, soundness).** | `theorem legalMoves_sound (h : m ∈ legalMoves p) : Legal p m` | [core, M4] *(checked)* |

Proof notes *(checked)*. L3.1: `simp [pseudoMoves]`. L3.2: `(mem_pseudoMoves_iff_candidate.mp
h).2`. L3.3: `rw [legalMoves, pseudoMoves, List.filter_filter]; congr 1; funext m; simp [Legal,
Bool.and_comm]`, with a comment giving the reason for `Bool.and_comm`: `List.filter_filter` puts the
outer test (king safety) first, and `Legal` puts it second. (Round 4; the Round 3 one-line `simp`
left the reordering to simp's AC normalization.) L3.4: `simp
[legalMoves_eq_filter]`. L3.5: `(mem_legalMoves_iff_candidate.mp h).2`.

**What L3.4 gives `Chess.Game` now.** DESIGN §6.1's optional `isLegal` field, with law `isLegal x m =
true ↔ m ∈ moves x`, is available in Stage 1, not Stage 2: take `isLegal p m := decide (m ∈
candidates p ∧ Legal p m)`; its law is L3.4. At an attacker node of a certificate this builds the
candidate list (cheap, about 0.3 ms) and decides legality for one move only, instead of filtering
all candidates.

---

## 4. Section "Perft"

No `variable` line: the lemmas below bind `n` and `p` explicitly, being meant to be applied
(`perft_one p`).

### D4.1 `perft : Nat → Position → Nat`

```lean
def perft : Nat → Position → Nat
  | 0, _ => 1
  | n + 1, p => ((legalMoves p).map fun m => perft n (p.play m)).sum
```

Docstring: "The number of ways to choose `n` moves one after another from `p`, each an entry of
`legalMoves` of the position reached so far; a move counts as often as `legalMoves` lists it (perft
of depth `n`). Depth 0 counts the empty choice, so it is 1 for every position. A line that reaches a
position where `legalMoves` is empty before its `n`-th move adds nothing. No move clock and no
history are read, so the counts can be compared with the published ones (chessprogramming.org,
*Perft Results*)."

Notes. Structural recursion on the depth, `List.sum` from core (`Init.Data.List.Basic`). It counts
leaves without building the lines. That it is the number of *sequences of legal moves* (M8) needs M4
(the entries are exactly the legal moves) and M5 (no entry is repeated), and is Stage 2; until
then the docstring speaks only of entries of `legalMoves`.

### D4.2 `perftDivide (n : Nat) (p : Position) : List (Move × Nat)`

```lean
def perftDivide (n : Nat) (p : Position) : List (Move × Nat) :=
  (legalMoves p).map fun m => (m, perft n (p.play m))
```

Docstring: "For each entry of `legalMoves p`, in order, the move and the perft of depth `n` after
it: the 'divide' that localizes a disagreement with another program's perft."

Notes. Stockfish's `go perft k` prints this list for `n = k − 1`; python-chess can produce the same.
`#eval perftDivide 2 p` prints UCI moves (Position's `Repr Move`), so a mismatching move is found by
comparing two columns (*representation* §2.7).

### Lemmas of §4

| ID | English (= Lean docstring) | Lean statement | Tag |
|---|---|---|---|
| L4.1 | Perft of depth 0 is 1: the empty choice. | `@[simp] theorem perft_zero (p : Position) : perft 0 p = 1` | [core] *(checked, `rfl`)* |
| L4.2 | Perft of depth `n + 1` adds up, over the entries of `legalMoves p`, perft of depth `n` after each. | `theorem perft_succ (n : Nat) (p : Position) : perft (n + 1) p = ((legalMoves p).map fun m => perft n (p.play m)).sum` | [core] *(checked, `rfl`)* |
| L4.3 | Perft of depth 1 is the number of entries of `legalMoves p`. | `theorem perft_one (p : Position) : perft 1 p = (legalMoves p).length` | [core] *(checked)* |
| L4.4 | The divide's counts add up to perft of one more ply. | `theorem sum_perftDivide (n : Nat) (p : Position) : ((perftDivide n p).map (·.2)).sum = perft (n + 1) p` | [core] *(checked)* |

Proof notes *(checked)*. L4.3: `simp [perft, List.map_const']` (`List.sum_replicate_nat` then
fires). L4.4: `simp [perftDivide, perft_succ, Function.comp_def]`. `perft_succ` is not `@[simp]`:
unfolding a perft by `simp` is never wanted.

---

## 5. Section "Testing against the specification"

Two executable definitions used by the tests here and by the test library (DESIGN §8.7), and one
[sanity] lemma saying what the first computes. They are part of no theorem used elsewhere and of no
trusted reading.

`variable {p : Position} {m : Move}`

### D5.1 `legalMovesBySpec (p : Position) : List Move`

```lean
def legalMovesBySpec (p : Position) : List Move :=
  let sources := Square.all.filter fun s => p.board.colorAt s = some p.turn
  let moves := sources.flatMap fun s =>
    Square.all.flatMap fun t => (none :: PromoKind.all.map some).map fun o => ⟨s, t, o⟩
  moves.filter fun m => decide (Legal p m)
```

Docstring: "The legal moves of `p` found from the specification alone, for tests: every move from a
square holding a piece of the side to move, to any square, with no promotion choice or with each of
the four in turn, that `Legal` allows. Slow: 320 moves are tested per piece of the side to move."

Notes. It uses no part of the generator: not its target lists, not its candidates. Restricting
sources to squares holding a piece of the side to move loses no legal move, by
`PseudoLegal.colorAt_src` (Rules, proved); it cuts DESIGN §5.7's 20 480 candidates to 320 per piece
(5 120 in the initial position). Its shape is the docstring's: the sources, every move from them,
then the filter by `Legal` (Round 4; the Round 3 body hid the filter in a `filterMap` over an `if`,
and L5.1's proof had to destructure `m` and `split` on it).

### D5.2 `agreesWithLegal (p : Position) : Bool`

```lean
def agreesWithLegal (p : Position) : Bool :=
  (legalMovesBySpec p).all (· ∈ legalMoves p) && decide (legalMoves p).Nodup
```

Docstring: "The generator agrees with the specification on `p`: every move `legalMovesBySpec` finds
is listed by `legalMoves`, and `legalMoves` lists no move twice. (That every listed move is legal is
a theorem, `legalMoves_sound`.)"

Notes. A `true` here gives M4 and M5 at `p` as theorems: L5.2 and L5.3 below, through L3.5 and
L5.1. So a test position can carry a kernel-checked "the generator lists exactly the legal moves
here" by `decide +kernel` on `agreesWithLegal p = true` (about 5 s for a small position), not only
a `#guard`, which trusts the interpreter. Soundness is not tested, because it is proved; a test of
a proved fact would only add time.

### Lemmas of §5

| ID | English (= Lean docstring) | Lean statement | Tag |
|---|---|---|---|
| L5.1 | `m` is in `legalMovesBySpec p` exactly when it is legal in `p`. | `theorem mem_legalMovesBySpec : m ∈ legalMovesBySpec p ↔ Legal p m` | [sanity] |
| L5.2 | **If the generator agrees with the specification on `p`, then `legalMoves p` lists exactly the legal moves of `p` (M4 at `p`).** | `theorem mem_legalMoves_of_agreesWithLegal (h : agreesWithLegal p = true) : m ∈ legalMoves p ↔ Legal p m` | [core] *(checked)* |
| L5.3 | If the generator agrees with the specification on `p`, then `legalMoves p` lists no move twice (M5 at `p`). | `theorem nodup_legalMoves_of_agreesWithLegal (h : agreesWithLegal p = true) : (legalMoves p).Nodup` | [core] *(checked)* |

Proof notes *(checked)*. L5.1: `simp only [legalMovesBySpec, List.mem_filter, List.mem_flatMap,
List.mem_map, decide_eq_true_eq]`; forward is the filter's second component; backward, the move is
built from `m.src` (which passes the source filter by `simpa using h.1.colorAt_src`, Rules'
`PseudoLegal.colorAt_src`), `m.dst ∈ Square.all` and `m.promo` (placed by `cases m.promo <;> simp
[PromoKind.mem_all]`). L5.2: forward is L3.5; backward, unfold `agreesWithLegal` with
`Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq` and apply its first half to L5.1. L5.3: the
second half. These are design choice 8 applied to `agreesWithLegal`: its note's promise is a theorem
in the same file.

---

## 6. Section "Tests"

As `#guard`s and `example`s at the end of the file, until the test library exists. Two new named
positions, each a `def` with a docstring in the style of Rules §10; every other position is one of
Rules' named test positions (`foolsMate`, `castlePos`, `blackCastlePos`, `castleRookPos f`, `epPos`,
`epPinPos`, `kingsPos`, `promoPos`, `blackPromoPos`, `pinPos`, `blackEpPos`, `rookAttackedPos`,
`defendedPos`).

### D6.1 `epCheckPos : Position` (DESIGN §8.4's fifth bug class)

```lean
def epCheckPos : Position :=
  (⟨Board.empty |>.set ⟨4, 3⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 4⟩ (some ⟨.white, .pawn⟩)
    |>.set ⟨0, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨3, 6⟩ (some ⟨.black, .pawn⟩),
   .black, CastlingRights.none, none⟩ : Position).play ⟨⟨3, 6⟩, ⟨3, 4⟩, none⟩
```

Docstring: "The position after d7d5 from: White king e4 and pawn e5, Black king a8 and pawn d7,
Black to move, no castling rights. So: White to move, in check from the pawn on d5, en passant
target d6, no rights."

### D6.2 `promoKnightPos : Position` (DESIGN §8.4's fourth bug class, seen from the generator)

```lean
def promoKnightPos : Position := promoPos.play ⟨⟨1, 6⟩, ⟨0, 7⟩, some .knight⟩
```

Docstring: "`promoPos` after b7a8=N: White's pawn has captured Black's a8 rook and become a knight;
Black to move, Black's kingside right only."

(A queen on a8 would give check along the eighth rank and forbid both castlings, which would test
nothing about rights; a knight on a8 attacks b6 and c7 only.)

**The "So: …" sentences are checked.** Both positions are built by `play`, which is Rules code; a
later change to `play` could quietly turn them into other positions. Two `#guard`s pin down what the
docstrings say: `epCheckPos` has White to move, in check, en passant target d6 and no rights
(`castling.letters == "-"`); `promoKnightPos` has Black to move and the rights `"k"`.

### The tests *(each checked; timings in parentheses)*

Measured in the library build: the module elaborates in about 30 s (`lake build`; 24 s before
Round 4 added the kernel-checked agreement on `kingsPos`, about 5 s), of which about 21 s is kernel
checking of the nine `decide +kernel` examples (0.7 to 5 s each) and about 6 s the interpreted
`#guard`s (0.3 to 0.7 s for each slow one). Each test carries a one-line comment
saying what it checks, as in Rules §10.

- The two new positions are what their docstrings say: `#guard epCheckPos.turn == .white && decide
  (InCheck epCheckPos) && epCheckPos.epTarget == some ⟨3, 5⟩ && epCheckPos.castling.letters == "-"`
  and `#guard promoKnightPos.turn == .black && promoKnightPos.castling.letters == "k"`.
- Initial position: `example : (legalMoves Position.initial).length = 20 := by decide +kernel`
  (3.4 s; plain `decide` costs 2.7 s more in the elaborator). `#guard perft 2 Position.initial ==
  400` (0.6 s). `#guard ((perftDivide 1 Position.initial).map (·.2)).sum == 400`.
- Fool's mate, through the generator: `example : legalMoves foolsMate = [] := by decide +kernel`
  (3.9 s). With `InCheck foolsMate` (Rules) this is `Game.chess.Mated` for that position once L7.6
  (`checkmate_iff`) is proved; until then it is evidence, and Rules' own `#guard decide (Checkmate
  foolsMate)` is the proof.
- The empty board: `#guard (candidates ⟨Board.empty, .white, CastlingRights.full, none⟩).isEmpty`
  (no piece, and the castling rights alone propose nothing).
- Agreement with `Legal`: one `#guard agreesWithLegal p` line per position, so that a failure names
  its position, for each of the 17 positions `Position.initial`,
  `foolsMate`, `castlePos`, `blackCastlePos`, `castleRookPos 3` (Black rook d7), `castleRookPos 4`
  (Black rook e7, White in check), `epPos`,
  `epPinPos`, `kingsPos`, `promoPos`, `blackPromoPos`, `pinPos`, `blackEpPos`, `rookAttackedPos`,
  `defendedPos`, `epCheckPos`, `promoKnightPos` (0.1 to 0.7 s each; about 1.6 s for all).
- Agreement as a theorem, on one position: `example : ∀ m, m ∈ legalMoves kingsPos ↔ Legal kingsPos
  m := fun _ => mem_legalMoves_of_agreesWithLegal (by decide +kernel)` (about 5 s in the kernel; M4
  at `kingsPos`, kernel-checked). The other positions keep their `#guard`s, to hold the module's
  build time near 30 s; the test library may promote more of them.
- Regression counts, cross-checked by the agreement tests:
  `#guard [Position.initial, foolsMate, castlePos, blackCastlePos, castleRookPos 3, castleRookPos 4,
  epPos, epPinPos, kingsPos, promoPos, blackPromoPos, pinPos, blackEpPos, rookAttackedPos,
  defendedPos, epCheckPos, promoKnightPos].map (fun p => (legalMoves p).length) ==
  [20, 0, 23, 15, 23, 4, 7, 4, 2, 13, 9, 4, 7, 15, 2, 8, 15]`.
- Named moves, each by `decide +kernel` (1.0 to 3.0 s each). A move written as an anonymous
  constructor needs a type ascription on the left of `∈`, since nothing else fixes its type:
  `(⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ : Move) ∈ legalMoves epCheckPos`; moves written with `Move.castle` need
  none:
  - en passant out of check: `⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ ∈ legalMoves epCheckPos` (e5d6; it is legal
    only because it removes the checking pawn);
  - castling after a rook capture with promotion: `Move.castle .black .kingside ∈ legalMoves
    promoKnightPos` and `Move.castle .black .queenside ∉ legalMoves promoKnightPos`;
  - castling through an attacked square: `Move.castle .white .queenside ∈ legalMoves castlePos` and
    `Move.castle .white .kingside ∉ legalMoves castlePos` (f1 attacked);
  - a pin: `⟨⟨4, 1⟩, ⟨3, 2⟩, none⟩ ∉ legalMoves pinPos` (Be2d3).

Not here: perft depth 3 and beyond, and the six standard perft positions. `perft 3 Position.initial`
takes 17 s interpreted *(checked: 8 902)*, too long for a module build, and the standard positions
need `fen`, which lives in `Chess.ChessGame`. Both go to the test library, compiled, with the
published counts (*representation* §2.7) at depth 3 for all six positions and deeper where time
allows; any `native_decide` version is `_native` and lives only there (DESIGN §7.3).

---

## 7. Section "Completeness" (pulled into Stage 1; M5 still planned in `Chess/MoveGen/Correct.lean`)

With the definitions above, M2, M4 and M6 follow from one lemma, the cover. L7.1–L7.4, L7.6 and
L7.7 are in the section `Completeness` of `Chess/MoveGen.lean`, right after "The generator"
(MoveGen review C1). L7.5 (M5, `Nodup`) is longer and stays planned in `Chess/MoveGen/Correct.lean`.

Helpers of the cover, each with its docstring:

| ID | English (= Lean docstring) | Lean statement |
|---|---|---|
| L7.0a | A pawn move of the side to move whose target is one of its pawn targets, and which obeys the promotion rule, is a candidate from its source square. | `theorem mem_candidatesFrom_pawn (hs : p.board m.src = some ⟨p.turn, .pawn⟩) (ht : m.dst ∈ pawnTargets p.turn m.src) (hp : m.PromotionRule p.turn) : m ∈ candidatesFrom p m.src` |
| L7.0b | A candidate from a move's own source square is a candidate. | `theorem mem_candidates_of_mem_candidatesFrom (h : m ∈ candidatesFrom p m.src) : m ∈ candidates p` |
| L7.0c | A move with no promotion choice to a square short of the last rank obeys the promotion rule. | `theorem promotionRule_of_none (hp : m.promo = none) (h : m.dst.relRank p.turn ≠ 7) : m.PromotionRule p.turn` |

Docstrings of the main rows: L7.1 "**Every pseudo-legal move of `p` is a candidate of `p` (the
cover).**"; L7.2 "**`pseudoMoves p` lists exactly the pseudo-legal moves of `p` (M2).**"; L7.3
"Every legal move of `p` is listed by `legalMoves p` (M4, completeness)."; L7.4 "**`legalMoves p`
lists exactly the legal moves of `p` (M4).**"; L7.6 "**Checkmate is check with no listed move
(M6).**"; L7.7 "Stalemate is no check and no listed move (M6)." The two instances:
`Checkmate.decidableByGen` "Checkmate is decided through the generator: check, and no listed move.
This replaces the instance of `Chess.Rules`, which tests every move." and
`Stalemate.decidableByGen` "Stalemate is decided through the generator: no check, and no listed
move. This replaces the instance of `Chess.Rules`, which tests every move." Both are declared with
`priority := high`. `decide +kernel` proves `Checkmate foolsMate` in about 1.7 s.

`variable {p : Position} {m : Move}`

| ID | English | Lean statement | Target |
|---|---|---|---|
| L7.1 | **Every pseudo-legal move is a candidate.** | `theorem PseudoLegal.mem_candidates (h : PseudoLegal p m) : m ∈ candidates p` | the cover |
| L7.2 | The pseudo-legal moves are listed exactly. | `theorem mem_pseudoMoves : m ∈ pseudoMoves p ↔ PseudoLegal p m` | M2 |
| L7.3 | Every legal move is listed. | `theorem legalMoves_complete (h : Legal p m) : m ∈ legalMoves p` | M4 |
| L7.4 | **The legal moves are listed exactly.** | `theorem mem_legalMoves : m ∈ legalMoves p ↔ Legal p m` | M4 |
| L7.5 | No move is listed twice. | `theorem legalMoves_nodup (p : Position) : (legalMoves p).Nodup` (and `pseudoMoves_nodup`) | M5 |
| L7.6 | Checkmate is check with no listed move. | `theorem checkmate_iff : Checkmate p ↔ InCheck p ∧ legalMoves p = []` | M6 |
| L7.7 | Stalemate is no check and no listed move. | `theorem stalemate_iff : Stalemate p ↔ ¬ InCheck p ∧ legalMoves p = []` | M6 |

How each goes:
- **L7.1, the cover.** `rcases h` into the six rules. A step move: its source holds a non-pawn piece
  of the side to move and it `Reaches` its destination, so L1.3 puts the move in
  `candidatesFrom p m.src`. A push, double push, pawn capture or en passant capture: the rule's own
  geometric hypothesis puts `m.dst` in `pawnTargets` (D2.1 note), and L2.1 with the promotion rule
  (for a double push and an en passant capture: `promo = none` and the destination is on relative
  rank 3 or 5, not 7) puts `m` in `pawnMovesTo`. A castling: L2.2 and `CanCastle`'s right and
  `IsCastle`'s king. *Skeleton checked*: the step-move, push and castling cases are proved in
  scratch; the remaining three are rank arithmetic, so this is D1, about 60–80 lines. No reasoning
  about attacks, pins, victims or blockers is needed: L1.3 has already done the blockers.
- **L7.2–L7.4** are L3.1, L3.4 and L7.1, a few lines each.
- **L7.5** is L2.4 with `List.Nodup.filter` twice.
- **L7.6, L7.7**: `∀ m, ¬ Legal p m ↔ legalMoves p = []` by L7.4 and `List.eq_nil_iff_forall_not_mem`.
  The faster instance `instance : Decidable (Checkmate p) := decidable_of_iff _ checkmate_iff.symm`
  is declared after them; being declared later than Rules' instance, it is the one later modules
  find. (Rules' instance tests 20 480 moves; Rules review C3 measured it not finishing in 500 s in
  the kernel. Through the generator: 3.9 s.)
- M8 (perft counts legal lines) and M9 (perft colour symmetry) need the above and `Chess/Invariants`;
  they are Stage 2–3 and not shaped further here.

THEOREMS writes M4 as D2 ("hundreds to low thousands of lines"). With this design it is D1: the
soundness half is L3.5 (Stage 1, one line) and the completeness half is L7.1 (a geometric case
split). Open item 1 proposes pulling `Correct.lean` into Stage 1.

---

## 8. Design choices, with reasons

1. **Propose and dispose: candidates filtered by the rules themselves.** The generator never
   decides a movement rule itself; it proposes candidates by geometry and asks `PseudoLegal`, then
   the second half of `Legal`. Every other test it makes (the colour and kind of the piece on a
   square, empty squares and blockers, the edge of the board, the two guards of `castleCandidates`)
   only removes candidates. So none can add an illegal move (soundness is one line, L3.5), and
   completeness needs only that none removes a pseudo-legal move, which is the cover L7.1, proved
   in §7. Reasons:
   - *Faithful by construction.* Principle 6 of DESIGN ("one predicate per rule, shared by every
     user") applied to the generator: no second copy of en passant, castling or promotion exists to
     drift from the first. The prototype's generator restated every rule in its own encoding
     (`pawnMoves`, `castleMoves`), and that is where its bug classes lived.
   - *Soundness in Stage 1.* L3.5 is one line. Before M4, the only trusted claim about the generator
     is that it misses nothing, and that is exactly what `agreesWithLegal` tests.
   - *M4 becomes geometry.* The cover lemma L7.1 is a case split with no check, pin or blocker
     reasoning, and it is also the Rules review's C3.2 "candidate cover", obtained for free.
   - *Cost, measured.* Interpreted, on the initial position, per call: `candidates` 0.3 ms,
     `pseudoMoves` 2.1 ms, a constructive variant that restates the non-pawn rules instead of
     re-deciding them 1.1 ms, `legalMoves` 24 ms. The king-safety filter is about 90 % of the time;
     re-deciding `PseudoLegal` costs about 4 % (perft 3: 17.0 s against 16.2 s for the variant). In
     the kernel, conjunctions are evaluated lazily, so re-deciding a candidate costs one `Reaches`
     test against about sixteen in the king-safety test that follows.
   - *Rejected:* one generator per rule, each restating its rule's conditions (the prototype's
     shape, and THEOREMS M2's sketch). It is a little faster and needs M2's full per-rule proofs to
     be trusted.
2. **Candidates are tight where tightness is free.** Sliders stop at the first blocker (D1.2), as
   the task and DESIGN §5.7 say, so a blocked rook proposes one square, not seven; leapers propose
   only on-board squares. A loose cover (whole rays) would also be correct but would send more
   candidates through `PseudoLegal`, whose slider test is quadratic in the distance.
3. **Target lists mirror `Reaches` arm for arm and ignore the target's contents** (D1.3), so M1 is
   a single `↔` with `Reaches` (L1.3), and the same lists serve attack generation later (the fast
   layer's refinement, Rules review C9, relates to `Reaches` through them).
4. **Pawns propose four squares, uniformly** (D2.1), with promotion choices added by one function
   (D2.2). The pawn's rank, the en passant target and the emptiness of squares are the rules'
   business.
5. **Castling candidates need the right and a king on its home square** (D2.5): the king clause is
   what makes M5 true without `WellFormed`; the rights clause makes the candidates tighter and
   changes nothing downstream (not a measurable economy: see D2.5's notes).
6. **Move order is deterministic and not part of any contract.** Moves come in square order of
   their source, each piece's targets in the order of D1.3/D2.1, promotion choices in
   `PromoKind.all` order, castling last, kingside before queenside (`Wing.all` order). Every theorem
   meant for clients is about membership (and `Nodup`), as THEOREMS M4 asks, so a faster generator
   may order moves differently and still be proved equal up to permutation; L3.3 and L4.2 fix the
   order only internally.
7. **`legalMoves` filters with `decide (¬ …)`**, the second conjunct of `Legal` verbatim, so L3.3
   is `simp`, and DESIGN §5.7's sentence and the Lean are the same sentence.
8. **M1 here, not in `Correct.lean`.** DESIGN §8's table puts M1 in Stage 2. The target lists'
   docstrings say "exactly the squares it reaches"; that promise is proved where it is made, in
   about 45 checked lines. `Correct.lean` keeps the cover and what follows from it.
9. **`perft` reads no clock and no history** (Position has none), is structurally recursive on the
   depth, and counts leaves with `List.sum`; `perftDivide` is the debugging view every engine
   author uses, with L4.4 tying it to `perft`.
10. **Speed-ups: in Rules' instances, or as this module's own Boolean tests.** `pseudoMoves` and
    `legalMoves` capture the `Decidable` instances of `PseudoLegal` and `Board.KingAttacked` that
    exist when they are elaborated, that is, Rules' instances; a faster, proved-equal instance
    declared in this module or later would not change them. So a speed-up takes one of two forms:
    - *in `Chess.Rules`*: the Rules review's C3.1 (a ray-walk `Slides` instance; later the
      super-piece `KingAttacked`), which would need `Board.upToBlocker`, `slideTargets` and
      L1.1–L1.2 moved there;
    - *in this module*: `legalMoves` filters by its own Boolean, e.g. `kingSafeAfter p m`, computed
      from `reachTargets` from the king's square (the super-piece method, THEOREMS M3), with a lemma
      `kingSafeAfter p m = true ↔ ¬ (p.play m).board.KingAttacked p.turn`. L3.3 is then one
      `List.filter_congr` away, the cover and soundness proofs do not change, and the trusted Rules
      text stays the slow, obviously correct version.
    Which one is open item 4. Nothing in this spec's statements changes either way.
11. **No executable `inCheck`, no king finder, no sentinel** (DESIGN §2, Rules design choice 12).
    The only checks are `decide (InCheck p)` in tests and `decide (¬ … KingAttacked …)` in the
    filter.
12. **Tests in the module are small; the test library does the rest.** Kernel tests are limited to
    a few seconds each; deep perft and FEN positions wait for the test library (§6).
13. **The candidates read the board, the side to move and the castling rights, never the en passant
    target** (L2.5, proved by `rfl`). En passant is `EnPassantMove`'s business: the pawn proposes
    both diagonals whatever the target. This is what makes G16 (`legalMoves_normalize`, list
    equality) a pointwise `List.filter_congr`, and L2.5 makes any later optimization that reads
    `epTarget` in `candidates` fail to build.

---

## 9. Not in this module, and open items

Open items:
1. **Pull `Correct.lean` into Stage 1?** (owner or architect.) With design choice 1, M4 is D1 and its
   skeleton is checked. Proving L7.1–L7.7 in Stage 1 would remove the generator from the trusted
   base before the first milestone, and would make the G8 bridge (`Game.chess` means FIDE chess)
   Stage 1 too. Cost: about 150 lines.
2. **Rules review C1 and C5** (rules as structures; `StepMove` → `PieceMove`). This spec uses the
   names in `Chess/Rules.lean` today. A rename is a `sed` here; structures would make L7.1's
   `rcases` pattern independent of conjunct order, which is the main place this module takes the
   rules apart.
3. **`Move.castle` in Rules?** `Move.IsCastle p w m` could then be read "`m` is `Move.castle p.turn w`
   and a king of the side to move stands on its home square". Not proposed now: it would change
   trusted text for no proof it enables.
4. **Kernel cost of king safety: decide before certificate (C-tier) work starts.** (Owner of the
   Rules/MoveGen boundary.) Measured in the kernel: `legalMoves Position.initial` 3.4 s,
   `legalMoves foolsMate = []` 3.9 s; the prototype ran about 0.25 s per node. About 90 % is the
   king-safety filter, which uses Rules' `Board.Attacked`: 64 squares per king, each through
   `Slides`, which is quadratic per ray. The two ways out (design choice 10): faster instances in
   Rules (C3.1; then `Board.upToBlocker`, `slideTargets`, L1.1 and L1.2 move to `Chess.Rules`, and
   `Slides.decidable` becomes `decidable_of_iff _ mem_slideTargets` there), or a Boolean
   `kingSafeAfter` here with its `_iff` lemma, leaving Rules' text untouched. This is the biggest
   risk to the long-term goal of proving forced wins, since every certificate node pays it.
5. **DESIGN edits** (not made here): §5.7 should describe the generator as "candidates proposed by
   geometry, filtered by `PseudoLegal` and by king safety"; §7.3 should say that generator soundness
   is proved in Stage 1 (L3.5) and only completeness is trusted until M4; §8's table should list M1
   under `MoveGen`; §6.1's `isLegal` option is available in Stage 1 through L3.4.
6. **THEOREMS edits** (not made here): M1's sketch becomes `mem_slideTargets : t ∈ slideTargets d b s
   ↔ Slides d b s t` and `mem_reachTargets` (one lemma for all kinds; `OnRay`/`ClearBetween` are not
   used); M2's "Forces" should mention the candidate cover; M4's "Forces" should say `legalMoves`
   filters candidates and that soundness is Stage 1; M6 is stated with `InCheck p` (no executable
   `inCheck`, as DESIGN §12 already says); M7 should list `epCheckPos` and `promoKnightPos`.
   *Round 4:* M1, M3, M4, M6, G1 (`Chess.game.Mated`), the dependency map and open question 3 of
   THEOREMS were edited to match; the M2 and M7 remarks are still open.
7. **Position review C1 (closure boards in compiled code).** Perft 3 from the initial position takes
   17 s interpreted. Whether compiled code is fast enough for depth 4–5 should be measured in the
   test library's executable before anyone optimizes.
8. **A `Perm` lemma for M8 and M9.** Core has no "both lists free of repeats and with the same members,
   hence permutations" (Mathlib's `List.perm_ext_iff_of_nodup`); `List.perm_iff_count` is there. So
   `legalMoves_flip` stated as a `Perm` (M9) needs a helper of about ten lines, which belongs in
   `Chess.Basic` or a list-utilities module, not here. M8 needs only `List.length_flatMap` and
   `List.sum`.
9. **Test-only code ships in the library module.** `legalMovesBySpec`, `agreesWithLegal`, L5.1–L5.3,
   `epCheckPos` and `promoKnightPos` are imported by every downstream module. Move them to the test
   library when it exists (keeping L5.2 and L5.3 next to `agreesWithLegal`).
10. **One expression for the pawn diagonals.** `[s.offset (-1) c.forward, s.offset 1 c.forward]`
    appears in Rules' `Reaches .pawn`, in D1.3 and in D2.1, on purpose (the cover is then `simp
    [pawnTargets, h]`). A shared `pawnCaptureSquares c s` used by all three would remove the
    repetition without hurting the cover, but changes Rules' trusted text. Low priority.

Not here, on purpose:
- Check masks, pin rays, bitboards: later optimizations, each proved equal to `legalMoves` up to
  permutation (DESIGN §3.3, THEOREMS M10).
- FEN and UCI parsing: `Chess.ChessGame`.
- M8 (`LegalLine`, perft counts lines), M9 (perft colour symmetry): Stage 2–3.

---

## 10. Checklist for the translator

- `import Chess.Rules` only; add `import Chess.MoveGen` to `Chess.lean`.
- Module docstring `/-! # MoveGen … -/` with `## Main definitions` (`slideTargets`, `reachTargets`;
  `candidates` and its parts; `pseudoMoves`, `legalMoves`; `perft`, `perftDivide`;
  `legalMovesBySpec`, `agreesWithLegal`), `## Main statements` (`mem_slideTargets`,
  `mem_reachTargets` (M1);
  `legalMoves_eq_filter`, `legalMoves_sound` (M4 soundness); `candidates_ignores_epTarget`;
  `perft_one`, `sum_perftDivide`; `mem_legalMoves_of_agreesWithLegal`,
  `nodup_legalMoves_of_agreesWithLegal`), and
  `## Implementation notes` summarizing design choices 1, 5, 6, 10 and 13, and saying that completeness
  (M4) goes through the cover `PseudoLegal.mem_candidates` and that only M5 is still tested, not proved.
- Section order as in "Contents"; each a `/-! ## … -/` heading. Lemmas in `section Targets`,
  `section Candidates`, `section Generator`, `section Testing`, each opening with its `variable`
  line (§1–§3, §5); the perft lemmas need none (§4).
- Every `def`, `instance` and `theorem` carries the docstring given here, word for word. Nothing is
  `sorry`; no `native_decide`. [later] lemmas are not written.
- `@[simp]` exactly on `perft_zero`. Nothing else.
- Instances: none are defined in this module.
- Tests at the end, under `/-! ## Tests -/`: `epCheckPos` and `promoKnightPos` with their docstrings,
  then the tests of §6 in that order, squares as `⟨file, rank⟩` with the algebraic name in a comment.
  Kernel tests use `decide +kernel`. The module should elaborate in under 30 s; if it does not,
  demote the named-move examples to `#guard … ∈ legalMoves …` and record it in the process log.
- Lines at most 100 characters.
- Record in `docs/process/MoveGen.md` every place where the Lean forced the English to change.
