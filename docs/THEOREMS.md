# Target theorems for `Chess`

Author role: theorem architect (top-down). Date: 2026-11-01. Status: first draft, for review.

This document lists the theorems the library should aim to prove. It works backwards from the long-term
goal ("this move wins by force", "this is the only winning move", and approximations of "this move is
optimal"), and asks what has to be true underneath each claim. For each theorem it gives:

- **English**: a precise statement in plain words.
- **Lean**: a signature sketch. These are sketches, not compiled code. Names are proposals.
- **Forces**: the definitions the statement needs, and what shape they must have for the proof to go
  through. This is the input to `docs/DESIGN.md`.
- **Meta**: difficulty, kind (soundness, completeness, correctness, invariant, consistency), stage, and
  dependencies.

Sources: everything in `docs/research/` (cited as *landscape*, *game-theory*, *representation*,
*lean-eng*, *prior-work*), and the prototype in `prototype/`.

---

## 0. How to read this document

### 0.1 Vocabulary: soundness, completeness, correctness

These words are used in exactly these senses throughout.

| Artifact | Soundness | Completeness | Correctness |
|---|---|---|---|
| A generator `gen p : List Move` against a predicate `Legal p m` | everything generated is legal: `m ∈ gen p → Legal p m` | everything legal is generated: `Legal p m → m ∈ gen p` | both, plus `Nodup` when the list is used for counting |
| A checker `check … c : Bool` against a claim `Claim` | acceptance implies the claim: `check … c = true → Claim` | the claim implies some certificate is accepted: `Claim → ∃ c, check … c = true` (the format is not lossy) | not used; a checker only needs soundness to be trusted |
| A decision procedure `search … : Bool` | `search … = true → Claim` | `Claim → search … = true` | `search … = true ↔ Claim` |
| An implementation layer against the spec layer | (refinement) the implementation computes the spec function through an abstraction map: `abs (impl x) = spec (abs x)` | | |
| The spec itself against the FIDE Laws | **faithfulness**: not a theorem. Evidence is reading the English beside the Lean, perft agreement, and sanity theorems | | |

A soundness theorem is what makes a result *trustworthy*. A completeness theorem is what makes a tool
*not silently weaker* than the claim. Every checker in this library needs soundness. Completeness is
worth proving when it is cheap, because it guards against a certificate format that cannot express some
true claims.

### 0.2 Difficulty scale (from *landscape*)

- **D0**: closed by computation on concrete data (`decide`, `decide +kernel`, `native_decide`).
- **D1**: routine induction or case analysis once the definitions are right (tens of lines).
- **D2**: needs a planned lemma library (hundreds to low thousands of lines).
- **D3**: research-level, or out of computational reach today. Listed so nobody plans on it.

### 0.3 Stages

| Stage | Name | What it delivers |
|---|---|---|
| **1** | First milestone: the two ends meet | Abstract game theory (wins, budgets, consistency, decidability, certificates) proved once; chess spec and an executable generator, tested by perft; the prototype's mate-in-11 and only-move theorems re-proved on the new definitions. |
| **2** | The generator is proved | `mem_legalMoves`, invariants of legal play, perft as a counting theorem. Every Stage 1 chess theorem becomes a statement about FIDE legality instead of about the generator. |
| **3** | Draws and optimality | Traps (draw certificates), survival certificates, the game value, `Optimal`, and the ladder of approximations. |
| **4** | The rule-faithful game | Halfmove clock, termination, dead positions, and the theorem that a `WinsIn` win is a win under the actual FIDE draw rules. |
| **5** | Scale | Bitboard refinement, ranked-set (tablebase) certificates, strategy theorems over material classes, I/O round trips. |

Theorems marked **★** form the first milestone. They are listed together in Section 7.

### 0.4 Trust labels

Every headline theorem has one of these labels:

- **[kernel]**: `#print axioms` shows at most `propext`, `Classical.choice`, `Quot.sound`.
- **[native]**: also `Lean.ofReduceBool` and `Lean.trustCompiler` (from `native_decide` or `bv_decide`).
- **[hyp: H]**: conditional on an explicit hypothesis `H` in the statement, e.g. a tablebase assumption.

General theorems (Tiers 1 to 5) are all **[kernel]**. Only concrete instances (perft numbers, specific
mates) may be **[native]**, and each should also have a kernel-only version when feasible
(*lean-eng* §1, §10.2).

The label is recorded where it is checked, not in docstrings: `ChessTest/Axioms.lean`,
`ChessTest/AxiomsPerft.lean` and `ChessDemo/Axioms.lean` hold a `#guard_msgs in #print axioms`
entry for each headline theorem, so a build fails if its axioms change (DESIGN §7.3). Every theorem
listed there is **[kernel]** (2026-11-02). Only the perft theorems of `ChessTest/Perft.lean` also
state the label in their docstrings.

### 0.5 Notation shared by every sketch

These are the definitions the theorems below assume. Their exact Lean form is for `docs/DESIGN.md` and
`docs/spec/` to fix; this is the vocabulary the theorems are written in.

```lean
inductive Color | white | black                  -- `c.other` is the opposite colour
inductive Kind  | pawn | knight | bishop | rook | queen | king
structure Piece where color : Color; kind : Kind
structure Square where file : Fin 8; rank : Fin 8   -- a1 = ⟨0, 0⟩, h8 = ⟨7, 7⟩
def Board := Square → Option Piece                  -- what stands on each square
inductive Wing  | kingside | queenside
structure CastlingRights where                      -- four FEN flags, read by `get c w`
  whiteKingside whiteQueenside blackKingside blackQueenside : Bool
structure Position where                            -- the *move layer*: no clock, no history
  board : Board
  turn : Color
  castling : CastlingRights
  epTarget : Option Square
structure Move where src dst : Square; promo : Option PromoKind
```

Letters: `s t` squares, `b` boards, `p q` positions, `m` moves, `c` colours, `a` the **attacker** in a
forced-win claim (the defender is `a.other`), `n k` budgets. In the abstract game layer, `G` is a game
and `x y` are its states.

A **budget** counts the attacker's moves, including the mating move. "White mates in 3" with White to
move is `WinsIn .white 3 p` (at most 3) or `MateIn .white 3 p` (exactly 3).

---

## 1. The goal, stated first

The library exists to make statements of this shape true and checkable:

> **Goal statement.** In position `p`, the move `m` wins by force: whatever the opponent does, the
> mover can checkmate within `n` moves. After every other legal move, the mover has no forced win.
> (That this makes `m` the unique optimal move is O2, Stage 3.)

```lean
theorem gotham_only_move :
    Chess.OnlyWinningMove gotham (uci "b7b2") ∧ Chess.WinsIn .black 11 gotham   -- [kernel]
```

(Gotham is Black to move. The library proves the two halves as two theorems,
`ChessDemo.gotham_onlyWinningMove` and `ChessDemo.gotham_winsIn`, about `Puzzles.gotham`; see §7.)

Reading this statement down to the kernel requires every tier below:

1. `fen "…"` must provably mean the position the string describes (I/O, M11).
2. `uci "…"` must be a legal move, and "legal" must mean FIDE legality (Tier 2, M4).
3. `WinsIn` must mean "forces checkmate", without counting stalemate as a win (Tier 3, G2).
4. `OnlyWinningMove` needs evidence that alternatives *do not win*. When they lose, a win certificate for
   the opponent suffices (Stage 1). When they only draw, it needs a draw certificate (Stage 3, C5).
5. "Optimal" needs a definition of the game value and a proof that "only winning move" implies "unique
   optimal move" (Tier 5, O0 and O2).
6. "By force" in a real game must survive the 50/75-move and repetition rules (Stage 4, G15).

Exact optimality in a general middlegame is out of reach (D3). Section 6 gives a ladder of statements
that *are* provable and say precisely how much they claim.

---

## 2. Tier 1: Rules and invariants (R)

The move layer: `Position`, `Legal`, `play`. Nothing here mentions clocks, history, or results.

### R1 ★ Square indexing is a bijection

- **English.** Numbering squares `index s = 8 · rank + file` (a1 = 0, …, h8 = 63) is a bijection between
  squares and `Fin 64`.
- **Lean.**
  ```lean
  def Square.index (s : Square) : Fin 64
  def Square.ofIndex (i : Fin 64) : Square
  theorem Square.ofIndex_index (s : Square) : Square.ofIndex s.index = s
  theorem Square.index_ofIndex (i : Fin 64) : (Square.ofIndex i).index = i
  ```
- **Forces.** `Square` as a structure of two `Fin 8` (*lean-eng* §4). The index is the only bridge to
  packed boards and bitboards.
- **Meta.** D0/D1 (`grind`, measured in *lean-eng* §4). Stage 1. No dependencies.

### R2 ★ Finite types are enumerated

- **English.** Each finite type (`Color`, `Kind`, `PromoKind`, `Wing`, `Square`, `Piece`) has a list
  of all its values, with no repeats, and quantifiers over it are decidable. `Move` and
  `CastlingRights` have decidable quantifiers only, with no list (*spec/Position* header).
- **Lean.**
  ```lean
  def Square.all : List Square
  theorem Square.mem_all (s : Square) : s ∈ Square.all
  theorem Square.all_nodup : Square.all.Nodup
  instance (P : Square → Prop) [DecidablePred P] : Decidable (∀ s, P s)
  ```
- **Forces.** No `Fintype` exists without Mathlib, so this trio replaces it. The `Decidable ∀` instance
  must go through core `Fin` quantifiers, not the list, so that plain `decide` works (*lean-eng* §4, §6).
- **Meta.** D0. Stage 1.

### R3 Attack geometry and attack symmetry

- **English.**
  1. For a non-pawn kind `k`: a `k` on `s` attacks `t` on board `b` if and only if a `k` on `t` would
     attack `s` on the same board. (The geometry depends only on the occupancy of the squares strictly
     between, which is symmetric.)
  2. A white pawn on `s` attacks `t` if and only if a black pawn on `t` attacks `s`.
  3. Consequently: square `t` is attacked by colour `c` if and only if, for some kind `k`, a `k` of
     colour `c.other` standing on `t` would attack a `k` of colour `c` (the "super-piece" test).
- **Lean.**
  ```lean
  /-- `Reaches k c b s t`: a piece of kind `k` and colour `c` on `s` attacks `t` on board `b`,
      ignoring pins and ignoring what stands on `t` (FIDE 3.9.1). -/
  def Reaches (k : Kind) (c : Color) (b : Board) (s t : Square) : Prop

  theorem reaches_symm (hk : k ≠ .pawn) : Reaches k c b s t ↔ Reaches k c b t s
  theorem reaches_pawn_symm : Reaches .pawn c b s t ↔ Reaches .pawn c.other b t s
  theorem attackedBy_iff_superpiece :
      b.AttackedBy c t ↔ ∃ k, ∃ s, b s = some ⟨c, k⟩ ∧ Reaches k c.other b t s
  ```
  where "some piece of colour `c` attacks `t`" is, as `Chess.Rules` states it,
  `Board.attackedBy_iff : b.AttackedBy c t ↔ ∃ s k, b s = some ⟨c, k⟩ ∧ Reaches k c b s t`. (The
  definition of `Board.AttackedBy` reads the kind off the board, for speed; `attackedBy_iff` is the
  interface proofs use.)
- **Done in `Chess.Rules`.** `Reaches` with sliders through `Slides` (index form, DESIGN §5.2);
  `reaches_congr` (only the squares strictly between `s` and `t` are read), `reaches_set_src`,
  `reaches_set_dst`, `slides_symm`, `Board.attackedBy_iff`. **R3.1–R3.3 done** (2026-11-02, ROADMAP
  step 6, Rules spec L2.10–L2.12) with the names and statements above (`attackedBy_iff_superpiece` is
  `Board.attackedBy_iff_superpiece`).
- **Forces.**
  - Attack must be *geometric* (FIDE 3.9.1: pinned pieces still give check). It must not consult
    legality.
  - One primitive `Square.offset (s : Square) (df dr : Int) : Option Square` from which every leaper and ray
    is defined (*representation* §4).
  - Sliders defined by "every square strictly between is empty" (`ClearBetween b s t`), a symmetric
    relation, rather than by a directed walk. A walk can be a computed equivalent, proved equal.
- **Meta.** D0 for leapers (4096 pairs, `decide +kernel`, about 2 s); D1 for sliders. Stage 1 for
  leapers, Stage 2 for sliders. Kind: sanity of the spec.

### R4 ★ Frame lemmas for `play`

- **English.** Playing a move changes only the squares the move touches. Those are its source, its
  destination, the captured pawn's square for en passant, and the rook's two squares for castling. On
  every other square the board is unchanged. On the destination stands the moved piece, or the promoted
  piece if the move promotes.
- **Lean.**
  ```lean
  /-- The squares whose contents `m` may change in `p`. -/
  def Move.touched (p : Position) (m : Move) : List Square
  theorem play_board_of_not_mem (h : t ∉ m.touched p) : (p.play m).board t = p.board t
  theorem play_board_src (h : PseudoLegal p m) : (p.play m).board m.src = none
  theorem play_board_dst (h : PseudoLegal p m) :
      (p.play m).board m.dst = (p.board m.src).map (·.promote m.promo)
  theorem play_board_epVictim (h : m.IsEnPassant p) : (p.play m).board m.epVictim = none
  theorem play_board_rookHome (h : m.IsCastle p w) : (p.play m).board (rookHome p.turn w) = none
  theorem play_board_rookCastleSquare (h : m.IsCastle p w) :
      (p.play m).board (rookCastleSquare p.turn w) = p.board (rookHome p.turn w)
  theorem play_turn (p : Position) (m : Move) : (p.play m).turn = p.turn.other
  ```
  All proved in `Chess.Rules` (spec L7.1–L7.8), with `PseudoLegal.touched_nodup` (no square is
  written twice). `play` is a list of writes carried out by `Board.setMany`, and `touched` is that
  list's squares, so the frame lemma is unconditional.
- **Forces.**
  - `Position.play` is a *total* function on all moves (junk on illegal ones). Theorems say what it
    does on pseudo-legal moves only.
  - `play` is written as a short composition of named board updates (`Board.set`, with `set_same`
    and `set_ne` as `@[simp]` lemmas, and `set_comm` used with `rw`: a permutation lemma would make
    `simp`'s normal form depend on term order). Core has no `Function.update`, so the library defines its
    own (*lean-eng* §5).
  - `play_turn` is unconditional; it is the alternation law the game layer needs (G1).
- **Meta.** D1. Stage 1. Every invariant in this tier is proved from these lemmas.

### R5 ★ Sanity theorems: square colour

- **English.** A bishop move never changes the colour of the bishop's square. A knight move always
  changes it.
- **Lean.**
  ```lean
  def Square.IsLight (s : Square) : Prop := (s.file.val + s.rank.val) % 2 = 1
  theorem PseudoLegal.isLight_dst_iff_of_bishop (h : PseudoLegal p m)
      (hb : p.board.kindAt m.src = some .bishop) : m.dst.IsLight ↔ m.src.IsLight
  theorem PseudoLegal.isLight_dst_iff_of_knight (h : PseudoLegal p m)
      (hn : p.board.kindAt m.src = some .knight) : m.dst.IsLight ↔ ¬ m.src.IsLight
  ```
  Proved in `Chess.Rules` under these names (proposed here as `bishop_keeps_colour` and
  `knight_flips_colour`), beside `PseudoLegal.promo_ne_none_iff` (a move names a promotion choice
  exactly when a pawn reaches the last rank).
- **Forces.** Nothing new. These exist to catch a spec that says the wrong thing (*prior-work* L8).
- **Hazard.** The English "bishops stay on their colour" is about piece *identity* over time. A position
  does not track identity, and a promoted bishop may stand on either colour. So the per-position claim
  "at most one light-squared bishop per side" is **false** for reachable positions. The faithful
  statement is this per-move lemma plus the material budget (R7).
- **Meta.** D1. Stage 1.

### R6 Colour-flip symmetry

- **English.** Mirror the board top to bottom and swap the colours of all pieces, the side to move, the
  castling rights and the en passant target. A move is legal in the mirrored position exactly when its
  mirror is legal in the original, and playing commutes with mirroring.
- **Lean.**
  ```lean
  def Square.flip (s : Square) : Square := ⟨s.file, s.rank.rev⟩    -- index s ↦ index s ^^^ 56
  def Position.flip (p : Position) : Position
  def Move.flip (m : Move) : Move
  theorem Position.flip_flip : p.flip.flip = p
  theorem legal_flip_iff : Legal p.flip m.flip ↔ Legal p m
  theorem play_flip : (p.play m).flip = p.flip.play m.flip
  ```
- **Forces.**
  - Pawn direction is a function of colour (`Color.forward : Color → Int`), never two hand-written
    copies, so the white-pawn and black-pawn lemmas become one lemma about `forward`.
  - Castling rights indexed by colour and wing (`CastlingRights.get c w`) so that `flip` is a swap,
    not four special cases.
- **Hazard.** Left-right mirroring is **not** a symmetry when castling rights are present (the king
  starts on the e-file). If stated at all, it needs `p.castling = CastlingRights.none` (a bare `none`
  there would elaborate as `Option.none`).
- **Meta.** D1/D2. Stage 2. Used by M9 (perft symmetry) and, via G7, to halve case analyses and
  certificates.

### R7 Material can only go down, and promotions are paid for by pawns

- **English.**
  1. A legal move never increases the number of men on the board. It decreases it by exactly one if it
     is a capture (en passant included), and leaves it unchanged otherwise.
  2. A legal move never increases the number of pawns of either colour.
  3. For each colour `c`, define the **excess** as the number of pieces beyond the initial set:
     `excess c = (Q − 1)⁺ + (R − 2)⁺ + (N − 2)⁺ + (Bₗ − 1)⁺ + (B_d − 1)⁺`, where `Bₗ` and `B_d` count
     bishops on light and dark squares and `x⁺ = max x 0`. The **material budget** `excess c + pawns c`
     never increases under a legal move. In the initial position it is 8 for each colour.
- **Lean.**
  ```lean
  theorem men_play_le (h : PseudoLegal p m) : (p.play m).men ≤ p.men
  theorem men_play_lt_iff (h : PseudoLegal p m) : (p.play m).men < p.men ↔ m.IsCapture p
  theorem pawns_play_le (h : PseudoLegal p m) (c : Color) : (p.play m).pawns c ≤ p.pawns c
  theorem budget_play_le (h : PseudoLegal p m) (c : Color) : (p.play m).budget c ≤ p.budget c
  ```
- **Forces.** `Position.men`, `pawns c`, `budget c` as counts over `Square.all`; a definition of
  `IsCapture` that includes en passant. `budget_play_le` uses R5 (bishops keep square colour) and a
  promotion lemma (one pawn removed, at most one excess term raised by one).
- **Meta.** D1. Stage 2. Kind: invariant. Used by G13 (termination) and R10.

### R8 Castling rights only disappear

- **English.** After any move, every castling right still held was already held before.
- **Lean.** `theorem castling_play_le (p : Position) (m : Move) : (p.play m).castling ≤ p.castling`
  (pointwise order on `get`), unconditional. Proved in `Chess.Rules`: `play` changes rights only in
  step 4, `Move.castlingAfter`, where a right is held after the move exactly when it was held before
  and the move does not leave or land on that king's or that rook's home square (`Move.Revokes`,
  revocation by squares as in Stockfish; `get_play_castling`). `&&` can only clear a right.
- **Forces.** `play` updates rights by clearing, never setting. Clearing happens when a king or rook
  moves from its home square *and* when anything is captured on a rook's home square. The second case is
  a known engine bug class (*representation* §2.5, Lague).
- **Meta.** D1. Stage 2.

### R9 Well-formedness is preserved by legal moves

- **English.** Call a position **well formed** if:
  1. each side has exactly one king;
  2. no pawn stands on rank 1 or rank 8;
  3. every castling right is backed by the king and that rook on their home squares;
  4. if an en passant target is set, it lies on the third rank from the side that just moved, an enemy
     pawn stands just beyond it, and the target square is empty;
  5. the side **not** to move is not in check.

  If `p` is well formed and `m` is legal in `p`, then `p.play m` is well formed. Corollaries: kings are
  never adjacent, and no legal move captures a king.
- **Lean.**
  ```lean
  structure WellFormed (p : Position) : Prop where
    oneKing : ∀ c, (Square.all.filter (p.board · = some ⟨c, .king⟩)).length = 1
    noBackRankPawns : …
    castlingHome : …
    epConsistent : …
    notToMoveSafe : ¬ p.board.KingAttacked p.turn.other
  theorem WellFormed.play (h : WellFormed p) (hm : Legal p m) : WellFormed (p.play m)
  theorem WellFormed.kings_not_adjacent (h : WellFormed p) : …
  theorem WellFormed.no_king_capture (h : WellFormed p) (hm : PseudoLegal p m) :
      (p.board m.dst).map (·.kind) ≠ some .king
  ```
  `Chess.Rules` supplies the pieces: `Board.HasKing` (for `oneKing`), `PseudoLegal.attacksFrom_dst`
  (a move onto a piece attacks it, which with (5) gives `no_king_capture`), and
  `PseudoLegal.isEnPassant_iff`, `isCastle_iff`, `isDoublePush_iff` (each shape is exactly its rule
  among pseudo-legal moves, for the castling and en passant clauses).
- **Forces.**
  - `WellFormed` is a **predicate on plain data**, not proof fields inside `Position`. Literal positions
    stay `decide`-friendly, and `WellFormed (fen "…")` is checked by `decide` (*prior-work* §2).
    Storing the two king squares as fields is the alternative; it makes (1) true by construction but adds
    a consistency invariant of its own. DESIGN decides.
  - `Legal` must be "pseudo-legal and, after the move, the mover's king is not attacked", so that
    component 5 of the *new* position is literally the second half of `Legal`.
  - "Mover's king attacked" must be defined as `∃ s, b s = some ⟨c, .king⟩ ∧ AttackedBy b c.other s`,
    which is total and needs no "find the king" function. The prototype's `findKing` returned 64 on a
    kingless board and made such boards silently stalemated (*landscape* §2).
- **Meta.** D1/D2. Stage 2. Kind: invariant.

### R10 Invariants of reachable positions

- **English.** A position is **reachable** if some sequence of legal moves leads to it from the initial
  position (FIDE 3.10.3). Every reachable position is well formed, has material budget at most 8 per
  colour, and has castling rights only where the initial rights allow.
- **Lean.**
  ```lean
  inductive Reachable : Position → Prop
    | initial : Reachable Position.initial
    | step : Reachable p → Legal p m → Reachable (p.play m)
  theorem Reachable.wellFormed (h : Reachable p) : WellFormed p
  theorem Reachable.budget_le (h : Reachable p) (c : Color) : p.budget c ≤ 8
  ```
- **Forces.** Invariants proved by *preservation for well-formed positions* (R9), with reachability as a
  one-line corollary. Positions loaded from FEN are not known to be reachable but can be checked well
  formed (*landscape* §3.2).
- **Hazard.** "At most two checkers" holds for reachable positions but is **false** for arbitrary
  well-formed ones. It needs the `Reachable` induction and a discovered-check analysis. Do not put it in
  `WellFormed`.
- **Meta.** D1 given R7–R9. Stage 2. A FEN violating `budget_le` is certified unreachable for free.

### R11 ★ Terminal positions

- **English.** The side to move is **in check** if its king is attacked. It is **checkmated** if it is in
  check and has no legal move (FIDE 1.4–1.4.1). It is **stalemated** if it is not in check and has no legal
  move (FIDE 5.2.1). A position with no legal move is exactly one of the two.
- **Lean.**
  ```lean
  def InCheck (p : Position) : Prop := p.board.KingAttacked p.turn
  def Checkmate (p : Position) : Prop := InCheck p ∧ ∀ m, ¬ Legal p m
  def Stalemate (p : Position) : Prop := ¬ InCheck p ∧ ∀ m, ¬ Legal p m
  theorem checkmate_or_stalemate (h : ∀ m, ¬ Legal p m) : Checkmate p ∨ Stalemate p
  theorem not_checkmate_and_stalemate : ¬ (Checkmate p ∧ Stalemate p)
  ```
- **Forces.** Definitions phrased word for word from FIDE 1.4–1.4.1 and 5.2.1, over `Legal`, not over the
  generator. Their computable counterparts come in M6. Proved in `Chess.Rules`, with the facts about
  a side with no king (`not_inCheck_of_not_hasKing`, `legal_iff_pseudoLegal_of_not_hasKing`).
- **Meta.** D0/D1. Stage 1 (statements and proofs are trivial; the point is that the definitions exist
  in this form from the start).

---

## 3. Tier 2: Move generation (M)

`legalMoves p : List Move` is executable. `Legal p m : Prop` is the declarative rule. The tier's job is
to prove they agree, so that the readable `Legal` is the only definition a reader has to trust.

### M1 Per-piece targets are sound and complete

- **English.** For each piece kind, the executable list of squares a piece reaches from a square
  contains a square exactly when the declarative rule `Reaches` says the piece reaches it. Example:
  `t` is in `slideTargets d b s` iff a piece sliding from `s` in direction `d` reaches `t` on `b`:
  `t` is on that ray and every square before it is empty. Whether `t` may be moved to (empty, or
  an enemy piece) is the movement rules' business, not the target list's.
- **Lean.** (Proved in `Chess/MoveGen.lean`, Stage 1.)
  ```lean
  theorem mem_slideTargets : t ∈ slideTargets d b s ↔ Slides d b s t
  theorem mem_reachTargets : t ∈ reachTargets k c b s ↔ Reaches k c b s t
  ```
- **Forces.**
  - Rays as structurally recursive functions, not well-founded recursion (WF definitions are
    irreducible to `decide`; *lean-eng* §7): `Board.upToBlocker` recurses on the ray's list.
  - `Direction` as a small enum with steps `d.df`, `d.dr` (one step is `s.shift d 1`), so that "the
    four rook directions" is a list of four named values.
  - One `↔` lemma for all kinds, the target list mirroring `Reaches` arm for arm, rather than
    `_sound`/`_complete` pairs or an `OnRay`/`ClearBetween` reformulation.
- **Meta.** D1. Stage 1 (done).

### M2 Pseudo-legal generation is correct

- **English.** `pseudoMoves p` lists exactly the pseudo-legal moves of `p`: moves that obey the movement
  rules of FIDE Articles 3.1–3.8, including castling's conditions that the king is not in check and does
  not cross an attacked square, but ignoring whether the mover's own king is attacked afterwards.
- **Lean.** `theorem mem_pseudoMoves : m ∈ pseudoMoves p ↔ PseudoLegal p m`
- **Forces.**
  - `PseudoLegal` as **one named predicate per FIDE rule**, joined by a disjunction (DESIGN §5.4;
    built so in `Chess.Rules`): `PieceMove` (non-pawn move or capture), `PushMove`, `DoublePushMove`,
    `PawnCaptureMove`, `EnPassantMove`, `CastleMove w`. A chess player can review each rule against
    its FIDE article. The completeness proof is then a case split, `rcases h with h | h | h | h | h |
    ⟨w, h⟩`, as an inductive would give.
  - Castling preconditions stated **explicitly**: `CastleMove p w m := m.IsCastle p w ∧ p.CanCastle w
    ∧ m.promo = none`, where `Position.CanCastle` says the right is held, the rook stands on its home
    square, the squares between are empty, the side is not in check, and the square the king crosses
    is not attacked; `IsCastle` puts the king on its home square. Then M2 and M4 need no `WellFormed`
    hypothesis.
  - Promotion: `m.promo = some k` with `k ∈ {knight, bishop, rook, queen}` **iff** a pawn reaches the
    last rank. Otherwise `m.promo = none`. This kills the Lean-Hackathon bug where a position whose only
    moves are promotions was reported as having none (*prior-work* §6).
- **Meta.** D2. Stage 2.
- **Status (2026-11-02).** Done, as stated, in `section Completeness` of `Chess/MoveGen.lean`
  (MoveGen spec L7.2), through the candidate cover rather than an inductive: `PseudoLegal` is the
  disjunction of the six rules, and its proof is the case split described above.

### M3 A fast check test is correct (done, 2026-11-02)

- **Status.** Done in ROADMAP step 6 (MoveGen spec D3.4, L3.9), because the kernel cost of king
  safety was cut by a Boolean test in `Chess.MoveGen`. The statement needs `PseudoLegal p m`, since
  the test looks only where a king can stand after a pseudo-legal move:
  `kingSafeAfter_iff (h : PseudoLegal p m) : kingSafeAfter p m = true ↔ ¬ (p.play m).board.KingAttacked p.turn`.
  The text below is the plan as it was. Earlier status: deferred, not required. The design has no executable `inCheck`: tests and the game
  use `decide (InCheck p)`, and the generator filters by `decide (¬ … KingAttacked …)`, both through
  Rules' instances (DESIGN §12, `docs/spec/MoveGen.md` design choice 11). M3 returns only if the
  kernel cost of king safety is cut by a Boolean test in `Chess.MoveGen` rather than by faster
  instances in `Chess.Rules` (MoveGen spec design choice 10 and open item 4, to be decided before
  C-tier work).
- **English.** If added: the executable king-safety test answers "after `m`, is a king of the mover
  attacked?" correctly, computed by the super-piece method (look from the king's square with each
  kind's `reachTargets`).
- **Lean.** (If added.)
  ```lean
  theorem kingSafeAfter_iff : kingSafeAfter p m = true ↔ ¬ (p.play m).board.KingAttacked p.turn
  ```
- **Forces.** The super-piece method (R3.3), so its proof is R3 plus M1. `legalMoves_eq_filter`
  then follows by one `List.filter_congr`.
- **Meta.** D1 given R3, M1. Stage 2, if at all.

### M4 ★★ The legal-move generator is correct (Stage 2 headline)

- **English.** For **every** position `p` and move `m`: `m` is in `legalMoves p` if and only if `m` is
  legal in `p`. Soundness: everything generated is legal. Completeness: every legal move is generated.
- **Lean.**
  ```lean
  theorem legalMoves_sound : m ∈ legalMoves p → Legal p m
  theorem legalMoves_complete : Legal p m → m ∈ legalMoves p
  theorem mem_legalMoves : m ∈ legalMoves p ↔ Legal p m
  instance : Decidable (Legal p m) := decidable_of_iff _ mem_legalMoves
  ```
  with `Legal p m := PseudoLegal p m ∧ ¬ (p.play m).KingAttacked p.turn`.
- **Forces.**
  - `legalMoves p := (pseudoMoves p).filter (kingSafeAfter p)`, with `pseudoMoves p` the geometric
    candidates filtered by `PseudoLegal`, and `kingSafeAfter p m` the super-piece test of M3.
    `kingSafeAfter_iff` proves the test equal to `¬ (p.play m).board.KingAttacked p.turn` for every
    pseudo-legal `m`, and `legalMoves_eq_filter` states the result as `candidates p` filtered by
    `Legal`: the FIDE definition read as a program (*representation* §4). (Before ROADMAP step 6
    the filter was `decide (¬ (p.play m).board.KingAttacked p.turn)` itself.) Soundness is then one
    line, proved in Stage 1 (`legalMoves_sound`); completeness reduces to the candidate cover
    `PseudoLegal.mem_candidates` (`docs/spec/MoveGen.md` §7). Check masks and pin rays would be a
    later optimization, proved equal to the same filter.
  - **No `WellFormed` hypothesis.** This is achievable if `KingAttacked` is the total existential of R9
    and castling preconditions are explicit (M2). An unconditional theorem is simpler to use everywhere.
  - Phrased with `↔` on membership, not list equality, so move order stays an implementation freedom
    (*landscape* §3.3).
- **Meta.** D2 in the original plan; D1 with the candidate cover (`docs/spec/MoveGen.md` §7).
  Stage 2. Depends on the cover (or M2) and R4, and, since ROADMAP step 6, on M3
  (`kingSafeAfter_iff`, through `legalMoves_eq_filter`). Retires the prototype's main caveat
  ("the generator is tested, not proved").
- **Status (2026-11-02).** Done: `legalMoves_sound` (Stage 1) and `legalMoves_complete` and
  `mem_legalMoves` in `section Completeness` of `Chess/MoveGen.lean` (MoveGen spec L7.3–L7.4),
  with no `WellFormed` hypothesis. The generator filters by the Boolean test `kingSafeAfter` of
  M3 rather than by `decide (¬ … KingAttacked …)`; `legalMoves_eq_filter` proves it equal to
  `(candidates p).filter fun m => decide (Legal p m)`, in the same order. The sketched
  instance was not added: `Legal p m` is decided by `Legal.decidable` of `Chess.Rules`, which
  tests the definition directly.

### M5 No move is generated twice

- **English.** `legalMoves p` has no duplicates.
- **Lean.** `theorem legalMoves_nodup : (legalMoves p).Nodup`
- **Forces.** Moves are identified by data `(src, dst, promo)`. Castling is the king's two-square move,
  never a separate constructor that could duplicate it. Each source square is enumerated once.
- **Why it matters.** Perft *counts*. A duplicated move inflates perft while soundness and completeness
  still hold.
- **Meta.** D1/D2. Stage 2.

### M6 Checkmate and stalemate are decided by the generator

- **English.** A position is checkmate iff the side to move is in check and the generator returns no
  moves; likewise for stalemate, with "not in check".
- **Lean.**
  ```lean
  theorem checkmate_iff : Checkmate p ↔ InCheck p ∧ legalMoves p = []
  theorem stalemate_iff : Stalemate p ↔ ¬ InCheck p ∧ legalMoves p = []
  instance : Decidable (Checkmate p) := decidable_of_iff _ checkmate_iff.symm
  ```
- **Meta.** D1 given M4. Stage 2. Used by the game bridge G8.
- **Status (2026-11-02).** Done: `checkmate_iff` and `stalemate_iff` in `section Completeness` of
  `Chess/MoveGen.lean` (MoveGen spec L7.6–L7.7), with the instances `Checkmate.decidableByGen`
  and `Stalemate.decidableByGen` (priority high, so they replace Rules' instances, which test
  every move).

### M7 ★ Perft regression facts

- **English.** The executable generator reproduces the published perft counts of the six standard test
  positions (chessprogramming.org) at modest depths. Example: from the initial position there are 20,
  400, 8,902 and 197,281 legal move sequences of lengths 1–4.
- **Lean.**
  ```lean
  def perft : Nat → Position → Nat
    | 0, _ => 1
    | n + 1, p => ((legalMoves p).map fun m => perft n (p.play m)).sum
  theorem perft_initial_3 : perft 3 Position.initial = 8902 := by decide +kernel  -- [kernel]
  theorem perft_kiwipete_3 : perft 3 kiwipete = 97862 := by native_decide          -- [native]
  ```
- **Forces.** `perft` lives in the move layer and must **not** read a clock or history; otherwise it
  stops matching the published numbers (Position 5's FEN has clocks `1 8`). Also include the three bug
  classes from *representation* §2.5 as named small positions (rook captured on its home square, pin
  broken, en passant uncovering a rank check).
- **Why this is in Stage 1.** Before M4 is proved, perft agreement is the evidence that the *generator*
  is right. After M4, the same facts become evidence that the *specification `Legal`* agrees with how the
  chess-programming community reads FIDE. That is the one thing no Lean proof can establish
  (*landscape* §3.4). These theorems stay valuable forever.
- **Meta.** D0. Stage 1. Kind: differential test of the spec.
- **Status (2026-11-02).** Done, in the test library: `ChessTest/Perft.lean` proves the published
  counts at depth 1 for all six positions and at depth 2 for the initial position and Position 3 by
  `decide +kernel` (`perft_initial_1`, `perft_initial_2`, `perft_kiwipete_1`, `perft_position3_1`,
  `perft_position3_2`, `perft_position4_1`, `perft_position5_1`, `perft_position6_1`, all
  [kernel]); `#guard`s check depth 2 of the rest, depth 3 of all six and depth 4 of Position 3.
  `perft_initial_3` in the kernel, as sketched above, was judged out of reach in step 3, when depth
  2 of the initial position took 42 s and 3.9 GB. Since step 6 that takes 9.8 s (the whole module
  39 s, 3.7 GB peak; `docs/spec/ChessTest.Perft.md` §3); depth 3 has not been tried since, so
  whether it now fits is open (ROADMAP §5). No `_native` theorem was needed. The bug-class
  positions are the named positions of `ChessTest/Rules.lean` and `ChessTest/MoveGen.lean`.
  Beyond the build, the compiled `chess-perft` agrees with python-chess on all six positions to
  depth 4 and on several hundred random positions (`docs/process/ChessTest.md`).

### M8 Perft counts legal lines

- **English.** `perft n p` is the number of sequences of `n` moves, each legal in the position reached
  so far, starting from `p`.
- **Lean.**
  ```lean
  inductive LegalLine : Position → List Move → Prop
    | nil : LegalLine p []
    | cons : Legal p m → LegalLine (p.play m) ms → LegalLine p (m :: ms)
  def lines : Nat → Position → List (List Move)
  theorem mem_lines : ms ∈ lines n p ↔ LegalLine p ms ∧ ms.length = n
  theorem lines_nodup : (lines n p).Nodup
  theorem perft_eq_length_lines : perft n p = (lines n p).length
  ```
- **Forces.** Stated through an explicit list of lines, so no counting library is needed.
- **Meta.** D1 given M4, M5. Stage 2.

### M9 Perft is colour-symmetric

- **English.** The mirrored position has the same perft counts as the original.
- **Lean.**
  ```lean
  theorem legalMoves_flip : (legalMoves p.flip).Perm ((legalMoves p).map Move.flip)
  theorem perft_flip : perft n p.flip = perft n p
  ```
- **Meta.** D1 given R6, M4. Stage 2/3. The chessprogramming wiki's "mirrored Position 4" is this
  theorem applied once.

### M10 Bitboard refinement (optional fast layer)

- **English.** A `BitVec 64` read as a set of squares is a faithful finite set. The fast layer (two
  colour bitboards plus six kind bitboards) represents a spec position through an abstraction map
  `abs`. Its move generator produces the spec's legal moves up to order, and its `play` agrees with the
  spec's `play` through `abs`.
- **Lean.**
  ```lean
  theorem SquareSet.mem_union : s ∈ A ∪ B ↔ s ∈ A ∨ s ∈ B          -- and inter, compl, sdiff, singleton
  theorem mem_shift (d : Direction) : t ∈ shift d A ↔ ∃ s ∈ A, s.shift d 1 = some t
  theorem Fast.mem_knightAttacks : t ∈ Fast.knightAttacks A ↔ ∃ s ∈ A, Reaches .knight c b s t
  theorem Fast.legalMoves_perm (h : f.WF) : (Fast.legalMoves f).Perm (legalMoves (abs f))
  theorem Fast.play_abs (h : f.WF) (hm : Legal (abs f) m) : abs (Fast.play f m) = (abs f).play m
  ```
- **Forces.**
  - `SquareSet` as a thin structure over `BitVec 64` with `Membership` and `ext`. It can be used in the
    spec as well (attacked squares, empty squares), so the set layer refines for free.
  - Bitboard functions as compositions of small named maps, no `let`, named masks. Additivity proved
    compositionally, singleton cases by `decide +kernel` (*representation* §3).
  - Sliders by the classical ray method (first blocker = lowest or highest set bit). **No** magic or
    PEXT tables: their constants are found by search, and a reader cannot see why they are right.
  - `BitVec 64`, not `UInt64`, in anything the kernel evaluates or that is reasoned about
    (*lean-eng* §3).
- **Payoff.** With G7 (game morphisms), every certificate theorem checked on the fast layer transfers to
  the spec by one rewrite.
- **Meta.** D2. Stage 5. Nothing above Tier 2 depends on it.

### M11 Input and output

- **English.**
  1. The FEN parser either fails or returns a well-formed position.
  2. Printing a sane position to FEN and parsing it back returns the same position. The en passant
     target is written as stored, so nothing is lost; G16 is needed only to compare with FENs that
     other tools write.
  3. Every legal move round-trips through UCI notation; through SAN as well, with disambiguation.
- **Lean.**
  ```lean
  theorem parseFEN_wellFormed : parseFEN str = some p → WellFormed p
  theorem parseFEN_toFEN (h : p.Sane) : parseFEN p.toFEN = some p
  theorem parseUCI_toUCI : parseUCI m.toUCI = some m
  theorem parseSAN_toSAN (h : Legal p m) : parseSAN p (toSAN p m) = some m
  ```
- **Forces.** Parsers over `List Char` so that `fen "…"` reduces in the kernel (the prototype's
  `Fen.lean` does this). Moves are data; notation is only a parser (*prior-work* §5, the dwrensha SAN
  pitfall). The **clock fields** of a FEN belong to the game layer (G12), not to `Position`.
- **Status** (`docs/spec/ChessGame.md`, Round 4). M11.2 and the UCI half of M11.3 are proved in
  Stage 1, together with the characterisations `fen_eq_iff : fen s h = p ↔ p.Sane ∧ IsFEN s p` and
  `uci_eq_iff : uci s h = m ↔ m.toUCI = s`, so the parsers are out of the trusted base. M11.1 waits
  for `WellFormed` (Stage 2) and for an owner decision: it holds only if `parseFEN`'s filter is
  strengthened to include `WellFormed`, which ChessGame review C4 advises against (it would change
  `fen_eq_iff`). Today's parser accepts positions no `WellFormed` would, for example
  `4k3/8/8/8/8/8/8/4K3 w KQkq - 0 1` (castling rights with no rook). See ChessGame spec §7 and
  ROADMAP §5, open owner decisions. SAN is dropped (that spec's choice 13). Reading the halfmove clock,
  which G15 needs, is that spec's open item 5.
- **Meta.** D1/D2 (string reasoning is tedious in core). Parsers in Stage 1 (tested); theorems in
  Stage 5. Until they are proved, every headline theorem's statement should also be checkable as a
  literal `Position`, so the reader is not trusting the parser.

---

## 4. Tier 3: Game semantics and consistency (G)

Everything in this tier except G8 and G12–G16 is stated **once, for an abstract game**, and instantiated
with chess. The game theory never needs to know how a knight moves (*game-theory* §8.1, *prior-work*
L1). It can be tested on toy games where `decide` is instant.

### G1 ★ The abstract game interface and the chess instance

- **English.** A game has states, moves, a side to move, a finite list of moves available in each state,
  a function that plays a move, and a predicate "the side to move has been mated". Two laws: playing a
  move passes the turn to the other side, and a mated side has no moves.
- **Lean.**
  ```lean
  structure Game where
    State : Type
    Move : Type
    turn : State → Color
    moves : State → List Move
    play : State → Move → State
    Mated : State → Prop
    [decMated : DecidablePred Mated]
    [decEqMove : DecidableEq Move]
    turn_play : ∀ {x m}, m ∈ moves x → turn (play x m) = (turn x).other
    moves_eq_nil_of_mated : ∀ {x}, Mated x → moves x = []

  abbrev Game.chess : Game where
    State := Position
    turn := Position.turn
    moves := legalMoves
    play := Position.play
    Mated := fun p => InCheck p ∧ legalMoves p = []
  ```
- **Forces.**
  - The chess instance is built from the **executable** layer (`legalMoves`, and `InCheck` through
    its `Decidable` instance; there is no Boolean `inCheck`). That keeps Stage 1 unblocked: no
    generator proof is needed to instantiate the game. G8 then proves the instance means FIDE.
  - "Mated" is the only losing condition. Stalemate is *not* encoded anywhere; it is simply a state with
    no moves that is not mated, and the definitions below must make it a non-win (G2).
  - The game is G∞ in the terminology of *game-theory* §1.2: no clock, no repetition, infinite play is
    not a win for anyone. Clocked games are other instances (G12).
- **Meta.** D0. Stage 1. Toy instances: two take-away games, `Game.Toy.takeAway` and
  `Game.Toy.takeAwayStalemate`, in `Chess/Game/Examples.lean`.

### G2 ★ Forced win within a budget

- **English.** `WinsIn a n x`: the attacker `a` can force the defender to be mated using at most `n`
  attacker moves, whatever the defender does. Inductively:
  1. **(mate)** the defender is to move and is mated;
  2. **(move)** the attacker is to move, has a legal move after which it wins within `n − 1`;
  3. **(replies)** the defender is to move, has **at least one** legal move, and after **every** legal
     move the attacker wins within `n`.

  A side **wins** if it wins within some budget. Basic facts: with budget 0, the attacker wins only if
  the defender is already mated; a stalemated defender is never lost.
- **Lean.**
  ```lean
  inductive WinsIn (a : Color) : Nat → G.State → Prop
    | mate : G.turn x = a.other → G.Mated x → WinsIn a n x
    | move (m : G.Move) : G.turn x = a → m ∈ G.moves x → WinsIn a n (G.play x m) → WinsIn a (n + 1) x
    | replies : G.turn x = a.other → G.moves x ≠ [] →
        (∀ m ∈ G.moves x, WinsIn a n (G.play x m)) → WinsIn a n x
  def Wins (a : Color) (x : G.State) : Prop := ∃ n, WinsIn a n x

  theorem winsIn_zero_iff : WinsIn a 0 x ↔ G.turn x = a.other ∧ G.Mated x
  theorem not_wins_of_stalemate (hnm : ¬ G.Mated x) (hl : G.moves x = []) : ¬ Wins a x
  ```

  (As built in `Chess/Game/Laws.lean`: no hypothesis on whose turn it is, so the statement also
  covers a stalemated attacker. An earlier sketch had `ht : G.turn x = a.other`.)
- **Forces.**
  - The **"has at least one legal move"** guard in `replies`. Without it, a stalemated defender
    vacuously loses. dwrensha's `ForcedWin` has exactly this bug, marked `FIXME` (*prior-work* §5). Hurd
    subtracts terminal positions for the same reason.
  - A **depth index** from the start. Without it, "mate in n", "fastest mate" and "no mate within n" are
    not expressible (*prior-work* L3).
  - `mate` at **any** `n` makes the index mean "within". This is what makes G3 hold.
  - The budget counts **attacker moves**, and the mating move counts. Docstrings must say so.
- **Design decision to make at Stage 1 (see O8).** Define `WinsIn` as the instance
  `Reach a (DefenderMated a)` of a goal-directed `Reach a T n x` ("the attacker forces the play into
  target set `T`"). Every theorem in G3, G5 and C1–C2 then holds for arbitrary decidable goals (win
  material, promote, reach a tablebase position) at no extra cost. Only G4 and G9 are mate-specific.
- **Meta.** D0 (definitions), D1 (lemmas). Stage 1.

### G3 ★ More budget never hurts

- **English.** If the attacker wins within `n`, it wins within any `n' ≥ n`.
- **Lean.** `theorem WinsIn.mono (h : WinsIn a n x) (hn : n ≤ n') : WinsIn a n' x`
- **Meta.** D1, induction on the derivation. Stage 1. Missing from the prototype.

### G4 ★ No state is a forced win for both sides

- **English.** It is impossible that both colours can force a win from the same state, whatever the two
  budgets.
- **Lean.**
  ```lean
  theorem WinsIn.not_both (h : WinsIn a n x) (h' : WinsIn a.other k x) : False
  theorem Wins.not_both (h : Wins a x) (h' : Wins a.other x) : False
  ```
- **Forces.** `moves_eq_nil_of_mated` (G1): a mated side has no moves, so `mate` cannot meet `move`.
- **Why it matters.** This is the bridge from "this move wins" to "this move is better": an alternative
  that hands the opponent a forced win is strictly worse than a win. It is the consistency theorem of the
  semantics.
- **Meta.** D1, induction on the first derivation. Stage 1. Proved in the prototype (`not_both`).

### G5 ★ Bounded forced wins are decidable

- **English.** There is a terminating search `searchWin a n x : Bool` (bounded minimax) that returns
  `true` exactly when the attacker wins within `n`. Hence `WinsIn a n x` is decidable, and negative
  facts such as "there is no mate within 4" can be proved by computation.
- **Lean.**
  ```lean
  def searchWin (a : Color) (n : Nat) (x : G.State) : Bool
  theorem searchWin_iff : searchWin a n x = true ↔ WinsIn a n x
  instance : Decidable (WinsIn a n x) := decidable_of_iff _ searchWin_iff
  ```
- **Forces.**
  - Structural recursion on `n` with the defender step inlined (attacker nodes decrement `n`; defender
    nodes do not). No fuel and no well-founded recursion, so `decide` can evaluate it (*lean-eng* §7).
  - The alternation law `turn_play` (G1), so a child of an attacker node is a defender node.
- **Why it matters.** A certificate checker can only verify wins. Every claim of the form "and nothing
  else wins within `n`" needs this theorem or the survival certificates of C4 (*prior-work* L6). This is
  Zermelo–Kalmár backward induction for depth `n`.
- **Meta.** D1. Stage 1. Kind: correctness (soundness and completeness of the search).

### G6 ★ Exact distance to mate

- **English.** The attacker **mates in exactly `n`** if it wins within `n` but not within any smaller
  budget. Exact distance is unique. With G3, "exactly `n + 1`" is the same as "within `n + 1` but not
  within `n`".
- **Lean.**
  ```lean
  def MateIn (a : Color) (n : Nat) (x : G.State) : Prop := WinsIn a n x ∧ ∀ k < n, ¬ WinsIn a k x
  theorem mateIn_succ_iff : MateIn a (n + 1) x ↔ WinsIn a (n + 1) x ∧ ¬ WinsIn a n x
  theorem MateIn.unique (h : MateIn a n x) (h' : MateIn a k x) : n = k
  theorem Wins.exists_mateIn (h : Wins a x) : ∃ n, MateIn a n x
  ```
- **Hazard.** In chess usage, "mate in 3" means mate is delivered on the third move. `WinsIn a 3 p` means
  *at most* 3. Theorem statements must use `MateIn` when they mean "exactly" (*landscape* §5).
- **Meta.** D1. Stage 1. Hurd's `win2_by n ∧ ¬ win2_by (n − 1)` and Marzion's `mate_eq`.

### G7 Game morphisms preserve forced wins

- **English.** Suppose a map sends states of game `G` to states of game `H` and moves to moves, possibly
  swapping colours, such that turns correspond, mating corresponds, playing commutes with the map, and
  the moves available at the image state are exactly the images of the moves available at the original
  state (up to order). Then the attacker wins within `n` in `G` iff its image wins within `n` in `H`.
- **Lean.**
  ```lean
  structure Game.Hom (G H : Game) where
    state : G.State → H.State
    move : G.Move → H.Move
    recolor : Color → Color                       -- `id` or `Color.other`
    recolor_other : recolor c.other = (recolor c).other
    turn_state : H.turn (state x) = recolor (G.turn x)
    mated_iff : H.Mated (state x) ↔ G.Mated x
    moves_perm : ((G.moves x).map move).Perm (H.moves (state x))
    play_state : m ∈ G.moves x → state (G.play x m) = H.play (state x) (move m)

  theorem Game.Hom.winsIn_iff (f : Game.Hom G H) : WinsIn (f.recolor a) n (f.state x) ↔ WinsIn a n x
  ```
- **Forces.** Nothing chess-specific. It forces `play` and `moves` to be stated so that the three uses
  below are morphisms.
- **Why it matters.** One theorem, three uses:
  1. **Colour flip** (R6, M9): a certificate for White transfers to the mirrored position for Black.
  2. **Refinement** (M10): certificates checked fast on bitboards transfer to the spec.
  3. **Normalization** (G16): positions differing only in an unusable en passant target have the same
     wins, which the repetition argument (G15) needs.
- **Meta.** D1. Stage 2/3.

### G8 ★★ The chess game means FIDE chess (Stage 2)

- **English.** In the chess instance, the available moves are exactly the FIDE-legal moves, and "mated"
  is exactly FIDE checkmate. Therefore every `WinsIn` statement about `Game.chess` is a statement about
  legal chess, not about the generator.
- **Lean.**
  ```lean
  theorem Chess.mem_chess_moves : m ∈ Game.chess.moves p ↔ Legal p m      -- = mem_legalMoves
  theorem Chess.chess_mated_iff_checkmate : Game.chess.Mated p ↔ Checkmate p  -- = checkmate_iff
  theorem Chess.winsIn_iff_specWinsIn : WinsIn a n p ↔ SpecWinsIn a n p
  ```
  where `SpecWinsIn` is the same inductive with `m ∈ moves` replaced by `Legal p m` and `Mated` by
  `Checkmate`, written out so a reader never has to look at the generator.
- **Status (2026-11-02): proved**, [kernel] (`#print axioms`: `propext`, `Classical.choice`,
  `Quot.sound`). Definitions in `Chess/Spec/Winning.lean` (imports `Chess.Rules` only):
  `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecMateIn`, `SpecOnlyWinningMove`. Theorems in
  `Chess/ChessGame/Fide.lean`: the three above, `forces_iff_specForces` (every target),
  `wins_iff_specWins`, `mateIn_iff_specMateIn` and `onlyWinningMove_iff_specOnlyWinningMove`.
  Specs: `docs/spec/Spec.Winning.md`, `docs/spec/ChessGame.Fide.md`.
  As built, `SpecWinsIn` is not itself an inductive: it is an `abbrev` for
  `SpecForces a (fun q => q.turn = a.other ∧ Checkmate q)`, and `SpecForces` is the inductive (the
  three rules of `Game.Forces`, with `Legal p m` for `m ∈ moves` and a `replies` rule guarded by
  `∃ m, Legal p m`).
- **Why it matters.** Before this theorem, Stage 1 chess theorems are honestly labelled "according to
  `legalMoves`". After it, they are theorems about chess. No Stage 1 statement has to change.
- **Meta.** D1 given M4, M6. Stage 2.

### G9 Draw certificates: traps

- **English.** A set `S` of states is a **trap** against attacker `a` if, for every state in `S`:
  1. if the defender is to move, it is not mated;
  2. if the defender is to move, it either has no move at all (stalemate) or has some move that stays
     in `S`;
  3. if the attacker is to move, every attacker move stays in `S`.

  The defender **holds** at `x` if `x` lies in some trap. If the defender holds, the attacker does not
  win with any budget. Conversely, if the attacker does not win, the defender holds: the set of states
  that the attacker does not win is itself a trap.
- **Lean.**
  ```lean
  structure Trap (a : Color) (S : G.State → Prop) : Prop where
    not_mated : ∀ x, S x → G.turn x = a.other → ¬ G.Mated x
    defender : ∀ x, S x → G.turn x = a.other → G.moves x = [] ∨ ∃ m ∈ G.moves x, S (G.play x m)
    attacker : ∀ x, S x → G.turn x = a → ∀ m ∈ G.moves x, S (G.play x m)
  def Holds (a : Color) (x : G.State) : Prop := ∃ S, Trap a S ∧ S x

  theorem Trap.not_winsIn (hS : Trap a S) (hx : S x) : ¬ WinsIn a n x
  theorem holds_iff_not_wins : Holds a x ↔ ¬ Wins a x
  ```
- **Forces.**
  - "Holding" is a **greatest fixed point**, given by the existence of an invariant set
    (Knaster–Tarski style). It needs no `coinductive` and no Mathlib (*game-theory* §2.3).
  - `moves` is a `List`, so a defender node has finitely many children. The converse direction takes the
    maximum of their budgets and uses G3. It is classical (excluded middle on `Wins`), which is fine for
    a semantic theorem.
- **Proof note.** `Trap.not_winsIn` is by induction on the `WinsIn` derivation, generalizing over the
  state in `S`. Induction on `n` does not work, because `replies` does not decrease `n`
  (*prior-work* Rec. 5).
- **Why it matters.** Wins are certified by finite trees (induction). "Cannot win" is certified by closed
  sets (an invariant). This is the half of the semantics the prototype lacked, and the gateway from "only
  winning move" to "optimal move" when alternatives draw. `holds_iff_not_wins` is also positional
  determinacy of the reachability game: the defender never needs memory.
- **Meta.** D1. Stage 3. Kind: consistency and completeness of the draw notion.

### G10 The game value and its negamax equations

- **English.** The **value** of a state, from the point of view of the side to move, is `win` if that
  side wins, `loss` if the opponent wins, and `draw` otherwise. By G4 the first two exclude each other.
  The value satisfies the negamax equations:
  - a mated side has value `loss`;
  - a side with no moves that is not mated has value `draw`;
  - otherwise, the value is the best, over all moves, of the negated value of the resulting state.
- **Lean.**
  ```lean
  inductive Outcome | loss | draw | win          -- ordered loss < draw < win; `Outcome.neg` swaps win/loss
  noncomputable def value (x : G.State) : Outcome
  theorem value_eq_win_iff : value x = .win ↔ Wins (G.turn x) x
  theorem value_eq_loss_iff : value x = .loss ↔ Wins (G.turn x).other x
  theorem value_mated (h : G.Mated x) : value x = .loss
  theorem value_stalemate (h : ¬ G.Mated x) (h' : G.moves x = []) : value x = .draw
  theorem value_eq_max (hm : ¬ G.Mated x) (h : G.moves x ≠ []) :
      value x = (G.moves x).foldr (fun m o => max o (value (G.play x m)).neg) .loss
  ```
- **Forces.** An `Outcome` type with `neg` satisfying `neg (neg o) = o` and `neg (min o o') = max (neg o)
  (neg o')` (the two negamax laws; *prior-work* §4, Nipkow). `value` is noncomputable in G∞; it becomes
  computable in a clocked game (G14).
- **Hazard.** In G∞ the negamax equations do **not** determine `value`: on a cycle, more than one
  assignment satisfies them. `value` is defined from `Wins`, not as "the solution of the equations".
- **Meta.** D1 given G4, G9. Stage 3.

### G11 Unwinnable and dead positions

- **English.** The attacker **can mate** from `x` if some sequence of legal moves, with both sides
  cooperating, ends with the defender mated. A state is **unwinnable** for `a` if it cannot. In chess, a
  position is **dead** (FIDE 5.2.2) if it is unwinnable for both colours. A forced win implies that a
  mate can be reached; so an unwinnable or dead position is never a forced win.
- **Lean.**
  ```lean
  inductive CanMate (a : Color) : G.State → Prop
    | mate : G.turn x = a.other → G.Mated x → CanMate a x
    | step : m ∈ G.moves x → CanMate a (G.play x m) → CanMate a x
  theorem WinsIn.canMate (h : WinsIn a n x) : CanMate a x
  def Dead (p : Position) : Prop := ¬ CanMate .white p ∧ ¬ CanMate .black p
  theorem Dead.value_eq_draw (h : Dead p) : value p = .draw
  theorem dead_of_bare_kings (hw : WellFormed p) (h : p.men = 2) : Dead p
  ```
- **Forces.** The `replies` guard again: the proof of `WinsIn.canMate` needs a defender move to follow.
- **Hazard.** **Dead is existential (helpmate), a forced win is universal.** A position can be not dead
  and still drawn. FIDE 6.9 (timeout) uses the one-sided notion `¬ CanMate a`; the library should name
  both (*landscape* §3.5, Ambrona).
- **Meta.** D1 for the general facts; D1/D2 for bare kings (only king moves exist, and a king cannot give
  check in a well-formed position); D2 for K+B v K and K+N v K, or D0 by enumeration. Stage 4.

### G12 The clocked game, and wins that ignore the clock

- **English.** For a ply limit `L`, the **clocked game** has states `(p, c)` with a halfmove clock `c`.
  A move resets the clock to 0 if it is a capture or a pawn move and adds 1 otherwise. When the clock
  reaches `L` and the position is not checkmate, the game is drawn: no moves remain. A checkmate delivered
  on the last allowed ply still counts (FIDE 9.6.2: mate takes precedence). `L = 150` is the automatic
  75-move rule; `L = 100` models a defender who always claims the 50-move draw. Then:
  1. a win in the clocked game is a win in G∞;
  2. a G∞ win within `n` is a clocked win within `n` from any clock with `c + 2n ≤ L`;
  3. so, from clock 0, a G∞ win is a win in the clocked game for some large enough `L`.
- **Lean.**
  ```lean
  def Clocked (L : Nat) : Game                     -- State := Position × Nat
  theorem Clocked.winsIn_forget (h : WinsIn (G := Clocked L) a n (p, c)) : WinsIn (G := Game.chess) a n p
  theorem Clocked.winsIn_of (h : WinsIn (G := Game.chess) a n p) (hc : c + 2 * n ≤ L) :
      WinsIn (G := Clocked L) a n (p, c)
  theorem wins_iff_exists_limit : Wins (G := Game.chess) a p ↔ ∃ L, Wins (G := Clocked L) a (p, 0)
  ```
- **Forces.**
  - The clock lives in the **game layer**, not in `Position`. `Position` stays the move layer, perft
    stays clock-free, and `Clocked L` is just another `Game` instance, so all of Tier 3 applies to it.
  - The draw-by-rule is encoded as "no moves and not mated", which the semantics already treats as a
    draw. No new constructor is needed.
- **Hazard.** Syzygy "cursed wins" are G∞ wins that are draws in `Clocked 100` (*game-theory* §3.1). A
  theorem citing a tablebase must say which game it is about.
- **Meta.** D1 for (1); D1/D2 for (2). Stage 4.

### G13 The clocked game terminates

- **English.** In `Clocked L`, every sequence of legal moves is finite. Proof idea: the triple
  (number of men, total pawn steps remaining, `L − clock`) decreases lexicographically with every move.
  A capture lowers the number of men. A non-capturing pawn move keeps it and lowers the pawn steps. Any
  other move keeps both and raises the clock, which is below `L` while moves remain.
- **Lean.**
  ```lean
  def measure (L : Nat) (x : Position × Nat) : Nat × Nat × Nat := (x.1.men, x.1.pawnSteps, L - x.2)
  theorem measure_play_lt (hm : m ∈ (Clocked L).moves x) :
      Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (measure L ((Clocked L).play x m)) (measure L x)
  theorem Clocked.wellFounded : WellFounded fun y x => ∃ m ∈ (Clocked L).moves x, y = (Clocked L).play x m
  ```
- **Forces.** `pawnSteps` = for each pawn, the squares it still has to advance before promoting. R7 for
  `men`. No repetition reasoning is needed (*landscape* §3.6).
- **Meta.** D1/D2. Stage 4. It gives a crude bound of the right order (about 9,500 moves against
  Wismuth's exact 8,848.5).

### G14 Backward induction computes the value of the clocked game

- **English.** In `Clocked L`, the value is the **unique** function satisfying the negamax equations of
  G10, and it is computed by well-founded recursion along G13 (Zermelo–Kalmár backward induction).
- **Lean.**
  ```lean
  def valueRec (L : Nat) : Position × Nat → Outcome            -- by well-founded recursion on `measure`
  theorem valueRec_eq_value : valueRec L x = value (G := Clocked L) x
  theorem value_unique (f : _ → Outcome) (hf : SatisfiesNegamax (Clocked L) f) : f = value
  ```
- **Meta.** D2. Stage 4. Mostly of conceptual value (the computation is astronomically large). It is the
  theorem behind "chess is determined" under the automatic rules.

### G15 ★★ A `WinsIn` win is a win under the FIDE draw rules (Stage 4 headline)

- **English.** Suppose the attacker wins from `p` within `n` in G∞. Play from `p` under the actual result
  rules: draw when the halfmove clock reaches `L`, and draw when a position occurs for the `R`-th time
  (counting earlier occurrences in the game's history). If the clock has headroom (`c + 2n ≤ L`) and no
  position has occurred `R − 1` times already, then the attacker still forces mate within `n`.
  With `L = 150, R = 5` these are the automatic FIDE rules (9.6). With `L = 100, R = 3` they model a
  defender who claims every 50-move and threefold draw.
- **Lean.**
  ```lean
  def Fide (L R : Nat) : Game     -- State := { pos : Position, clock : Nat, history : List Position }
  theorem Fide.winsIn_of (h : WinsIn (G := Game.chess) a n p) (hc : c + 2 * n ≤ L)
      (hr : ∀ q, (hist.map normalize).count (normalize q) + 1 < R) :
      WinsIn (G := Fide L R) a n ⟨p, c, hist⟩
  ```
- **Proof idea.** Let the attacker always play a move that lowers its *exact* distance to mate (G6).
  Along any resulting line the distance strictly decreases every two plies, so no position occurs twice
  in the line. With the history hypothesis no position reaches `R` occurrences. The clock hypothesis
  keeps the move rule from firing before mate. A dead position never occurs because mate stays
  reachable (G11).
- **Forces.**
  - FIDE 9.2.3 "same position" means same pieces, same side to move, and the **same possible moves**. An
    en passant target counts only if an en passant capture is actually possible. So history is compared
    after `normalize` (G16), never by raw record equality or FEN text.
  - Dead-position draws are left out of `Fide` itself (deciding deadness is not cheap). G11 shows they
    can never interrupt a forced win.
- **Hazard.** The 50-move claim can be made with a move that *would* complete 50 moves (FIDE 9.3.1), one
  ply before our automatic `L = 100`. The spec for `Fide` must either use `L = 99` for the claim model or
  justify that the difference does not matter. This needs checking against the text.
- **Meta.** D2. Stage 4. This is the theorem that discharges the prototype README's caveat "the 50-move
  and repetition rules are not modelled". Depends on G6, G7, G11, G12, G16.

### G16 Position identity: en passant normalization

- **English.** Two positions with the same board, side to move and castling rights, that differ only in
  an en passant target from which no en passant capture is legal, have the same legal moves and the same
  results of every move. `normalize` drops such a target. Normalization is a game morphism (G7), so it
  preserves every forced win.
- **Lean.**
  ```lean
  def Position.normalize (p : Position) : Position
  theorem legalMoves_normalize : legalMoves p.normalize = legalMoves p
  theorem play_normalize (hm : Legal p m) : p.normalize.play m = p.play m
  def SameFIDE (p q : Position) : Prop := p.normalize = q.normalize
  ```
- **Design option.** Make `play` set an en passant target only when an enemy pawn stands beside the
  pushed pawn. That shrinks the gap but does not remove it (a pinned capturer still makes the capture
  illegal), so `normalize` is still needed for FIDE identity.
- **Meta.** D1. Stage 4 (but the decision about `play` belongs to Stage 1).

---

## 5. Tier 4: Certificates and checker soundness (C)

An untrusted search (Stockfish, a tablebase, a script) emits a certificate. A small Boolean checker
evaluates it in the kernel. A soundness theorem turns `check … = true` into the semantic claim. The
searcher never enters the trusted base (*game-theory* §5, the certifying-algorithms pattern).

### C1 ★ Win certificates are sound

- **English.** A **win certificate** is a strategy tree: at attacker nodes it names one move and a
  subtree; at defender nodes it gives a subtree for each defender reply; a leaf says "mated". If the
  checker accepts a certificate for attacker `a`, budget `n` and state `x`, then `a` wins within `n` from
  `x`.
- **Lean.**
  ```lean
  inductive Cert (M : Type)
    | mate
    | move (m : M) (next : Cert M)
    | replies (rs : List (M × Cert M))
  def checkWin (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) : Bool
  theorem checkWin_sound : checkWin a n x c = true → WinsIn a n x
  ```
- **Forces.**
  - The checker mirrors the three constructors of G2, including "the defender has a move" at `replies`.
  - A certificate move at an attacker node is checked by membership in `G.moves x`, and every defender
    move is looked up in `rs`; a missing reply fails.
  - Recursion: structural on the certificate if Lean accepts the nested `List (M × Cert M)` recursion
    in a kernel-reducible way; otherwise fuel, with a lemma that enough fuel never changes the answer.
    DESIGN decides. The prototype used fuel.
- **Meta.** D1. Stage 1. Proved in the prototype (`check_sound`); re-proved here for the abstract game.

### C2 ★ Win certificates are complete

- **English.** Whenever the attacker wins within `n`, some certificate is accepted. The format is not
  lossy.
- **Lean.** `theorem checkWin_complete (h : WinsIn a n x) : ∃ c, checkWin a n x c = true`
- **Meta.** D1, induction on the derivation (needs `DecidableEq G.Move` for the lookup). Stage 1.

### C3 ★ Per-node kernel proofs

- **English.** A certificate can be compiled into many small theorems, one per node, each stating the
  position after a move as a literal (`play p m = q`). Chaining them proves the same `WinsIn` statement
  without one giant evaluation.
- **Lean.** Glue lemmas such as
  ```lean
  theorem WinsIn.of_play_eq (h : G.play x m = y) (w : WinsIn a n y) : WinsIn a n (G.play x m)
  theorem forall_mem_cons_winsIn … ; theorem iff_refuted … ; theorem iff_best …
  ```
  as in the prototype's `Cert.lean`.
- **Realized** (ROADMAP step 5) in `Chess/Game/Cert.lean`, `section PerNode`: `Forces.of_play_eq`,
  `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`, `Forces.forall_mem_nil`,
  `Forces.forall_mem_cons` and `WinsIn.of_mated` (Game spec §4.1, L4.8–L4.10, L4.12, L4.17,
  L4.18). Step 7 added the only-move root glue `OnlyWinningMove.of_moves_eq`,
  `OnlyWinningMove.refuted_nil`, `OnlyWinningMove.refuted_cons_self` and
  `OnlyWinningMove.refuted_cons` (L4.19–L4.22), and, for chess, `mem_chess_moves`
  (`Chess.ChessGame.Fide`), which shows an attacker's move available. The complete list of names a
  generated file may use is in Game spec §4.3 and `scripts/README.md`; `ChessTest/Interface.lean`
  records their signatures.
- **Why it matters.** Kernel cost grows superlinearly with unnormalized chains of moves (*lean-eng* §5).
  Literal checkpoints keep each declaration small. This is how the prototype got a kernel-only mate in
  11 (320 theorems, about 80 s, about 6 GB).
- **Meta.** D0/D1. Stage 1.

### C4 Survival certificates (bounded "no forced mate")

- **English.** A **survival certificate** is the mirror image of a win certificate: at defender nodes it
  names one reply, at attacker nodes it covers every attacker move, and its leaves are "attacker's budget
  exhausted", "stalemate", or "attacker has no move". If the checker accepts it, the attacker does
  **not** win within `n`.
- **Lean.**
  ```lean
  def checkSurvive (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) : Bool
  theorem checkSurvive_sound : checkSurvive a n x c = true → ¬ WinsIn a n x
  theorem checkSurvive_complete (h : ¬ WinsIn a n x) : ∃ c, checkSurvive a n x c = true
  ```
- **Forces.** The same `Cert` type with roles swapped, and one checker written generically in the role,
  so the two soundness proofs share their structure (*game-theory* §6).
- **Why not just use G5?** `searchWin` branches over every defender reply; a survival certificate names
  one. It is the compact witness for "no mate within `n`", as a win certificate is for "mate within `n`".
- **Meta.** D1. Stage 3.

### C5 Trap certificates (unbounded "no forced win")

- **English.** A finite **trap certificate** is a list of states, each with the defender's chosen move
  where the defender is to move. The checker verifies the three trap conditions of G9 for every listed
  state. If it accepts, the attacker does not win from any listed state, with any budget. A trap may also
  be given **symbolically**, by a decidable predicate whose closure conditions are proved by reasoning;
  this is how fortresses are certified.
- **Lean.**
  ```lean
  def checkTrap (a : Color) (S : List (G.State × Option G.Move)) : Bool
  theorem checkTrap_sound (h : checkTrap a S = true) (hx : x ∈ S.map Prod.fst) : ¬ Wins a x
  -- symbolic form: any `Trap a P` with `P` decidable, proved by hand (G9)
  ```
- **Forces.**
  - States compared by `DecidableEq` on normalized positions (G16), never by FEN text or by hash.
    A Zobrist hash may index a `HashMap`, but equality decides membership (*representation* §2.6).
  - **Composition**: a trap may exit into states already certified (by another trap, a tablebase slice,
    or a lemma). State this as `Trap` relative to a set `Safe` with `∀ x, Safe x → ¬ Wins a x`.
- **Why it matters.** A trap is the only way to certify that a move merely draws. Examples: a
  wrong-coloured-bishop fortress, a perpetual check (the trap is the cycle plus every escape), a
  tablebase draw region. Engines misjudge fortresses badly; a symbolic trap is where Lean adds the most
  over Stockfish (*game-theory* §4.3).
- **Meta.** D1 to state and prove; D0–D2 per instance. Stage 3.

### C6 Ranked-set certificates (DAGs and tablebases)

- **English.** A **ranked set** lists states with a rank and, at attacker nodes, a chosen move. Local
  checks: at an attacker node of rank `r > 0`, the chosen move leads to a listed state of rank below `r`;
  at a defender node of rank `r`, the defender is mated, or it has a move and every move leads to a listed
  attacker node of rank at most `r`. If the checker accepts, every listed state is a win within its rank.
  A strategy tree is a ranked set whose rank is the height; a DAG is a tree with shared subtrees; a
  verified endgame table is a ranked set covering a material class.
- **Lean.**
  ```lean
  def checkRanked (a : Color) (T : RankedSet G) : Bool
  theorem checkRanked_sound (h : checkRanked a T = true) (hx : T.rank? x = some r) : WinsIn a r x
  ```
- **Forces.** A finite map from (normalized) states to entries that the kernel can evaluate. `Array`
  equality is about 40× slower than `List` in the kernel (*lean-eng* §5), so the map must be chosen with
  kernel cost in mind.
- **Hazard (graph history interaction).** Sharing subtrees is sound in G∞, because values depend only on
  the position. In a clocked game, entries must be keyed by `(position, clock)` (*game-theory* §4.2).
- **Meta.** D1/D2. Stage 5. The Hurd/Marzion route to verified 3–4 piece tables: checked with forward
  move generation only, so no un-move generator enters the trusted base.

### C8 Per-node lower bounds

- **English.** "The attacker does not win within `n`", checked one node at a time: with the attacker
  to move and budget 0 it holds; with budget `n + 1`, every available move (an explicit move list)
  leads to a state where it holds with budget `n`; with the defender to move, it holds when the
  defender is not mated and one move escapes to a state where it holds, when the defender is
  stalemated, when the budget is 0, or when the defender itself wins within some budget. With
  `Forces.mono`, winning within `n + 1` and not within `n` is `MateIn (n + 1)`.
- **Lean.** `Game.not_winsIn_zero_of_turn`, `not_winsIn_succ_of_moves_eq`, `not_winsIn_of_escape`,
  `not_winsIn_zero_of_defender`, `not_winsIn_of_stalemate`, `not_winsIn_of_winsIn_other`,
  `not_winsIn_forall_mem_nil`, `not_winsIn_forall_mem_cons`, `not_winsIn_mono`,
  `MateIn.of_winsIn_of_not`, in `Chess/Game/Cert.lean`, section `Bounds`.
- **Evidence.** `ChessDemoBound.GothamMateIn.gotham_mateIn`: the Gotham puzzle is mate in exactly 11,
  the lower half by a generated certificate (`scripts/gen_bound.py`, `docs/research/minimality.md`).

### C7 ★ The only-move checker

- **English.** Given a state, a proposed best move with a win certificate, and, for every other legal
  move, a **refutation**, the checker accepts only if the best move is legal, its certificate is
  accepted, and every refutation is accepted. A refutation is either a win certificate for the opponent
  (Stage 1) or a trap certificate showing the mover cannot win (Stage 3). If the checker accepts, then
  after any legal move `m` the mover still wins iff `m` is the proposed move.
- **Lean.**
  ```lean
  inductive Refutation (G : Game)
    | opponentWins (n : Nat) (c : Cert G.Move)
    | moverHeld (S : List (G.State × Option G.Move))         -- Stage 3
  def checkOnlyMove (n : Nat) (x : G.State) (best : G.Move) (c : Cert G.Move)
      (refs : List (G.Move × Refutation G)) : Bool
  theorem checkOnlyMove_sound (h : checkOnlyMove n x best c refs = true) :
      OnlyWinningMove x best ∧ WinsIn (G.turn x) n x
  ```
- **Forces.** G4 (`not_both`) for the `opponentWins` case; C5 for the `moverHeld` case.
- **Realized** (ROADMAP step 5) as `checkOnlyMove n x best oc` with `oc : OnlyMoveCert`
  (`next`, `refBudget`, `refs`), one refutation budget for all alternatives, and Stage 1
  refutations only, so there is no `Refutation` type yet (Game spec D4.4–D4.5, choice 24).
  The budget `n` is counted at `x`, before the best move: the conclusion is
  `G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x`, not `… n (G.play x best)` as an earlier
  sketch had it (DESIGN §7.2). So "mate in 11" with the best move as the first of the 11 is
  `checkOnlyMove 11 x best oc`.
- **Hazard.** The prototype's `onlyMove` could only use `opponentWins`, so it could not prove only-move
  theorems where an alternative merely draws (its `Line.lean` records this). That is why C5 exists.
- **Meta.** D1. Stage 1 (wins only), Stage 3 (with traps).

### C8 Closed-set certificates for unwinnability

- **English.** A set of states closed under **all** moves of both sides and containing no state in which
  the defender is mated certifies that the attacker cannot mate even with cooperation (G11).
- **Lean.** `theorem checkClosed_sound (h : checkClosed a S = true) (hx : x ∈ S) : ¬ CanMate a x`
- **Meta.** D1. Stage 4. Ambrona's unwinnability algorithm can serve as the untrusted oracle.

---

## 6. Tier 5: Approximations of optimality (O)

Every theorem in this tier is stated over the abstract game and therefore also holds for `Clocked L` and
`Fide L R`. Engine numbers never appear in any statement. The honest English for an engine-assisted
result is "Lean checks that Stockfish's choice is the only move that keeps a forced mate", never
"Stockfish evaluates this as +M11".

### O0 Optimal moves

- **English.** A move is **optimal** (WDL-optimal) if it is legal and no legal move leads to a better
  outcome for the mover. Equivalently, it preserves the value of the position.
- **Lean.**
  ```lean
  def Optimal (x : G.State) (m : G.Move) : Prop :=
    m ∈ G.moves x ∧ ∀ m' ∈ G.moves x, (value (G.play x m')).neg ≤ (value (G.play x m)).neg
  theorem optimal_iff (hm : m ∈ G.moves x) : Optimal x m ↔ (value (G.play x m)).neg = value x
  theorem exists_optimal (h : G.moves x ≠ []) : ∃ m, Optimal x m
  ```
- **Meta.** D1 given G10. Stage 3.

### O1 Every winning move is optimal (a hazard, stated as a theorem)

- **English.** In a won position, every move that keeps a forced win is optimal in the WDL sense.
- **Lean.** `theorem optimal_of_wins (hm : m ∈ G.moves x) (h : Wins (G.turn x) (G.play x m)) : Optimal x m`
- **Why it is listed.** It shows that WDL-optimality is a weak notion in won positions. "Best move" in
  ordinary chess language usually means the *only* winning move (O2) or the *fastest* mate (O3). Theorem
  names must say which (*game-theory* §8.4).
- **Meta.** D1. Stage 3.

### O2 ★ The only winning move is the unique optimal move

- **English.** `m` is the **only winning move** at `x` if it is legal, the mover wins after it, and after
  every other legal move the mover does not win. Then `m` is optimal and no other move is.
- **Lean.**
  ```lean
  def OnlyWinningMove (x : G.State) (m : G.Move) : Prop :=
    m ∈ G.moves x ∧ Wins (G.turn x) (G.play x m) ∧
      ∀ m' ∈ G.moves x, m' ≠ m → ¬ Wins (G.turn x) (G.play x m')
  theorem OnlyWinningMove.wins_iff (h : OnlyWinningMove x m) (hm' : m' ∈ G.moves x) :
      Wins (G.turn x) (G.play x m') ↔ m' = m
  theorem OnlyWinningMove.optimal_iff (h : OnlyWinningMove x m) (hm' : m' ∈ G.moves x) :
      Optimal x m' ↔ m' = m
  ```
- **Evidence.** C7. Stage 1 covers alternatives that *lose*; Stage 3 covers alternatives that *draw*.
- **Meta.** D1. `wins_iff` in Stage 1 (it is the prototype's `onlyMove_sound` conclusion);
  `optimal_iff` in Stage 3.

### O3 Fastest mate (distance-to-mate optimal)

- **English.** At a state where the mover mates in exactly `n + 1`, a move is **fastest** if after it the
  mover still wins within `n`. A fastest move exists, and every fastest move is optimal.
- **Lean.**
  ```lean
  def FastestMate (x : G.State) (m : G.Move) : Prop :=
    m ∈ G.moves x ∧ ∃ n, MateIn (G.turn x) (n + 1) x ∧ WinsIn (G.turn x) n (G.play x m)
  theorem exists_fastestMate (h : MateIn (G.turn x) (n + 1) x) : ∃ m, FastestMate x m
  theorem FastestMate.optimal (h : FastestMate x m) : Optimal x m
  ```
- **Evidence.** A win certificate for `m` at `n` (C1) plus "no win within `n`" for `x` (G5 by
  computation, or C4 for each alternative).
- **Meta.** D1. Stage 3 (decidable, so instances are D0).

### O4 Only mate within a horizon

- **English.** `m` is the **only move that mates within `N`**: after `m` the mover wins within `N − 1`,
  and after any other move it does not. Decidable for fixed `N`.
- **Lean.**
  ```lean
  def OnlyMateWithin (N : Nat) (x : G.State) (m : G.Move) : Prop :=
    m ∈ G.moves x ∧ WinsIn (G.turn x) (N - 1) (G.play x m) ∧
      ∀ m' ∈ G.moves x, m' ≠ m → ¬ WinsIn (G.turn x) (N - 1) (G.play x m')
  ```
- **Hazard.** This is weaker than O2: another move may win more slowly. A tactics puzzle's "only move"
  usually means this. The theorem name must carry the horizon.
- **Meta.** D0 per instance. Stage 3.

### O5 No-blunder and only-non-losing moves within a horizon

- **English.**
  1. `m` **does not lose within `k`**: after `m`, the opponent cannot force mate within `k`.
  2. `m` is the **only non-losing move within `k`**: it does not lose within `k`, and after every other
     move the opponent forces mate within `k`.
  3. If `m` is the only non-losing move within `k` and the position is not lost, then `m` is the unique
     optimal move.
- **Lean.**
  ```lean
  def NoLossWithin (k : Nat) (x : G.State) (m : G.Move) : Prop :=
    m ∈ G.moves x ∧ ¬ WinsIn (G.turn x).other k (G.play x m)
  def OnlyNonLosingWithin (k : Nat) (x : G.State) (m : G.Move) : Prop :=
    NoLossWithin k x m ∧ ∀ m' ∈ G.moves x, m' ≠ m → WinsIn (G.turn x).other k (G.play x m')
  theorem OnlyNonLosingWithin.optimal_unique (h : OnlyNonLosingWithin k x m)
      (hx : value x ≠ .loss) (hm' : Optimal x m') : m' = m
  ```
- **Why it matters.** These are the honest approximations for middlegames: "`m` is optimal as far as any
  `k`-move forcing line can tell". They are decidable and get stronger as `k` grows. Item 3 is exact,
  conditional only on the position not being lost.
- **Meta.** D0 per instance, D1 for item 3. Stage 3.

### O6 Holding a draw

- **English.** In a drawn position, `m` **holds the draw** if the opponent cannot win after it, and
  **nothing wins** if no legal move gives the mover a forced win. If both hold, `m` is optimal and the
  value is `draw`.
- **Lean.**
  ```lean
  /-- After `m`, the opponent (now the attacker) cannot force a win. -/
  def HoldsDraw (x : G.State) (m : G.Move) : Prop := m ∈ G.moves x ∧ Holds (G.turn x).other (G.play x m)
  /-- After every legal move, the mover cannot force a win: the opponent holds. -/
  def NothingWins (x : G.State) : Prop := ∀ m ∈ G.moves x, Holds (G.turn x) (G.play x m)
  theorem optimal_of_holdsDraw (h : HoldsDraw x m) (h' : NothingWins x) : Optimal x m ∧ value x = .draw
  ```
  (Recall `Holds a y` means attacker `a` cannot win from `y`.)
- **Evidence.** One trap after `m`; one trap for the opponent's role after every move (C5).
- **Meta.** D1. Stage 3. First demonstration: a symbolic fortress.

### O7 Interval certificates: one framework for O2, O5, O6

- **English.** Suppose that for each legal move we certify a lower and an upper bound on its outcome for
  the mover. Lower bound `win` comes from a win certificate, `draw` from a trap against the opponent.
  Upper bound `loss` comes from an opponent's win certificate, `draw` from a trap against the mover. If
  the lower bound of `m` is at least the upper bound of every legal move, then `m` is optimal. When the
  bounds do not close, the certificate still proves a precise partial claim: "`m` guarantees at least
  `lo m`, and no move guarantees more than `max hi`".
- **Lean.**
  ```lean
  structure Bounds (x : G.State) where
    lo hi : G.Move → Outcome
    lo_le : ∀ m ∈ G.moves x, lo m ≤ (value (G.play x m)).neg
    le_hi : ∀ m ∈ G.moves x, (value (G.play x m)).neg ≤ hi m
  theorem Bounds.optimal (B : Bounds x) (hm : m ∈ G.moves x) (h : ∀ m' ∈ G.moves x, B.hi m' ≤ B.lo m) :
      Optimal x m
  /-- `ev m` holds the certificates behind `lo m` and `hi m` (win certificates and traps). -/
  def checkBounds (x : G.State) (lo hi : G.Move → Outcome) (ev : G.Move → Evidence G) : Bool
  theorem checkBounds_sound (h : checkBounds x lo hi ev = true) :
      (∀ m ∈ G.moves x, lo m ≤ (value (G.play x m)).neg) ∧
      (∀ m ∈ G.moves x, (value (G.play x m)).neg ≤ hi m)
  ```
- **Meta.** D1. Stage 3. This degrades gracefully, which is what an engine-driven pipeline needs.

### O8 Goal-directed forcing (decide the definition in Stage 1)

- **English.** `Reach a T n x`: the attacker can force play into the target set `T` within `n` attacker
  moves. `WinsIn` is the case `T = "defender to move and mated"`. Other targets: "win material",
  "promote", "reach a state certified won". Composition: if the attacker forces `T` within `n`, and wins
  within `k` from every state in `T`, it wins within `n + k`.
- **Lean.**
  ```lean
  inductive Reach (a : Color) (T : G.State → Prop) : Nat → G.State → Prop
    | goal : T x → Reach a T n x
    | move … | replies …                       -- as in G2
  abbrev WinsIn (a : Color) := Reach a (fun x => G.turn x = a.other ∧ G.Mated x)
  theorem Reach.trans (h : Reach a T n x) (hT : ∀ y, T y → WinsIn a k y) : WinsIn a (n + k) x
  ```
- **Hazard.** A theorem about `Reach a T` is a claim about `T`, not about the game value. "This move wins
  a piece by force" is a precise statement; "this move is winning" is a different one. The English must
  say which.
- **Why it matters.** `Reach.trans` with a verified table as `T` is how a long forced win is split into
  "reach a known-won endgame" plus a table lookup.
- **Meta.** D1. Definition decided in Stage 1; theorems in Stage 3.

### O9 Tablebases: verified or assumed

- **English.**
  1. **Verified**: a small table (3–4 pieces, pawnless first), checked as a ranked set (C6) plus a trap
     for its draw region (C5), proves the exact value of every position it covers.
  2. **Assumed**: a large table (Syzygy) enters a theorem only as an **explicit hypothesis** that it is
     sound, never as an `axiom`. The dependence is then visible in the statement.
- **Lean.**
  ```lean
  def TableSound (G : Game) (tb : G.State → Option Outcome) : Prop :=
    ∀ x o, tb x = some o → value x = o
  theorem only_move_of_table (htb : TableSound (Clocked 100) tb) (h : checkWithTable … = true) : …
  ```
- **Hazards.** Syzygy WDL assumes clock 0 and the 50-move rule, marks cursed wins and blessed losses
  separately, excludes positions with castling rights, and its DTZ can be off by one ply. So `tb` must be
  read as a statement about `Clocked 100` at clock 0, not about G∞ (*game-theory* §3.1). DTM tables
  (Lomonosov) are about G∞.
- **Meta.** D1 to state; D0–D2 per table. Stage 5.

### O10 Strategy theorems over material classes

- **English.** For every legal position of a material class (for example every KRK position with White
  to move), a short rule-based strategy for the attacker mates within a stated bound. Proof by an
  invariant and a decreasing measure, not by enumeration.
- **Lean.**
  ```lean
  theorem krk_wins (hp : WellFormed p) (hK : p.Material = krk) (ht : p.turn = .white) : WinsIn .white 16 p
  ```
- **Forces.** Spec definitions that do not hard-code more geometry than needed, so that the strategy
  proof is about rules, not coordinates (*prior-work* §3, "make definitions independent of the problem
  dimensions").
- **Meta.** D2. Stage 5+. The Marić–Janičić–Maliković KRK proof in Isabelle is the model. KRK in Lean
  could also be D0 by a verified table (O9.1); the symbolic proof is the more elegant result.

### O11 Out of reach (D3), so nobody plans on them

- The value of the initial position, or of a general middlegame position.
- "At most 218 legal moves in any reachable position" (true, but only claimed via an integer program;
  little use here).
- Deciding `Reachable p` in general; minimality of long shortest proof games.
- Verifying Stockfish's evaluation function. Its numbers are calibrated win probabilities in self-play,
  not game values (*game-theory* §5.1).

---

## 7. The first milestone (Stage 1)

These are the ★ theorems. Together they deliver the library's first end-to-end result on new
definitions, and both ends (the semantics at the top, the rules at the bottom) exist in final form.

| ID | Theorem | Kind | Difficulty |
|---|---|---|---|
| R1 | `Square.ofIndex_index`, `index_ofIndex` | bijection | D0/D1 |
| R2 | `Square.mem_all`, `all_nodup`, `Decidable ∀` | enumeration | D0 |
| R4 | frame lemmas for `play`, `play_turn` | spec sanity | D1 |
| R5 | `PseudoLegal.isLight_dst_iff_of_bishop`, `…_of_knight` | spec sanity | D1 |
| R11 | `Checkmate`, `Stalemate` as FIDE definitions; exclusivity | definitions | D0/D1 |
| M7 | perft regression facts (6 positions, small depths) | differential test | D0 |
| G1 | `Game`, `Game.chess` | interface | D0 |
| G2 | `WinsIn`, `winsIn_zero_iff`, `not_wins_of_stalemate` | semantics | D1 |
| G3 | `WinsIn.mono` | semantics | D1 |
| G4 | `WinsIn.not_both` | consistency | D1 |
| G5 | `searchWin_iff` | decision procedure correctness | D1 |
| G6 | `MateIn`, `MateIn.unique` | semantics | D1 |
| C1 | `checkWin_sound` | checker soundness | D1 |
| C2 | `checkWin_complete` | checker completeness | D1 |
| C3 | per-node glue lemmas | proof engineering | D0/D1 |
| C7 | `checkOnlyMove_sound` (opponent-win refutations) | checker soundness | D1 |
| C8 | per-node glue for lower bounds (`not_winsIn_*`, `MateIn.of_winsIn_of_not`) | proof engineering | D0/D1 |
| O2 | `OnlyWinningMove.wins_iff` | optimality (first rung) | D1 |

**Demonstration that closes Stage 1.** Re-prove the prototype's GothamChess results on the new
definitions: `MateIn .white 11 gotham` (exactly 11, using G5 or C4 for the lower bound, which the
prototype could not state), and `OnlyWinningMove gotham best`, each in a **[kernel]** version, with
`#print axioms` recorded.

*Done (2026-11-02, ROADMAP step 7)*, with one change of claim: `WinsIn .black 11 Puzzles.gotham`
(Black is to move; within 11, not exactly 11: no lower bound is proved) and
`OnlyWinningMove Puzzles.gotham (uci "b7b2")`, both [kernel], in `ChessDemo/Gotham.lean`, also
read through G8, with the refutations behind the only move stated too (`gotham_refuted`: after
each other move of Black, White forces mate); exact `MateIn` is proved for three small mates (`ChessDemo/Mates.lean`): the mates in 1 and 2 by search, the mate in 3 by a certificate for the win and a search for minimality.

**Decisions Stage 1 must make even though their theorems come later.**

1. `Position` has no clock and no history (forced by M7, G12, G15).
2. `WinsIn` is defined as an instance of `Reach` (O8), or not.
3. `play` sets the en passant target always, or only when an enemy pawn is adjacent (G16).
4. `Legal` is "pseudo-legal and own king not attacked", with `KingAttacked` total (M4, R9).
5. `PseudoLegal` is one named predicate per FIDE rule, joined by a disjunction (M2; settled in
   `Chess.Rules`).
6. `WellFormed` is a predicate on plain data, or king squares are fields (R9).
7. `checkWin` recursion: structural on the certificate, or fuel (C1).

**Stage 2 headline:** M4 (`mem_legalMoves`) and G8 (`Chess.winsIn_iff_specWinsIn`). After these,
every Stage 1 theorem is a theorem about FIDE chess under its rules of movement and checkmate
(Articles 3 and 5.1), without the clock and draw rules (G15), with no change to its statement.
*Both are proved (2026-11-02; M4 in `Chess/MoveGen.lean`, G8 in `Chess/ChessGame/Fide.lean`).*

---

## 8. Dependency map

```
R1, R2 ─► R3 (geometry, symmetry) ─► M1 (targets) ─► M2 (pseudo-legal) ─► M4 ★★ mem_legalMoves
             │                           │                                  │    M5 nodup
             ▼                           ▼                                  ▼
          R4 frame ─► R5 sanity      M3 kingSafeAfter_iff M4 ──────────► M6 checkmate_iff
             │                                                              │
             ├─► R7 material, R8 castling ─► R9 WellFormed.play ─► R10 Reachable invariants
             │                                                              │
             └─► R6 flip ─► M9 perft_flip        M7 perft facts ─► M8 perft_spec
                                                                            │
G1 Game ─► G2 WinsIn ─► G3 mono, G4 not_both, G5 searchWin_iff, G6 MateIn   │
              │                     │                                       ▼
              ├─► C1, C2, C3 ──► C7 only-move ──► O2              G8 ★★ chess game = FIDE
              ├─► G7 morphisms (flip, refinement M10, normalize G16)
              ├─► G9 traps ─► C4, C5 ─► G10 value ─► O0–O7 optimality ladder
              ├─► G11 dead ─► C8
              └─► G12 clocked ─► G13 termination ─► G14 backward induction
                       └──────────────► G15 ★★ FIDE agreement (also uses G6, G7, G11, G16)
C6 ranked sets ─► O9 tablebases ─► O10 strategy theorems
```

---

## 9. English-to-Lean hazards that these statements are designed around

| English | Trap | Where it is handled |
|---|---|---|
| "in check" | using legal attacks (respecting pins) | R3: geometric `Reaches` (FIDE 3.9.1) |
| "legal move" | silently assuming a well-formed position | M4 unconditional; `WellFormed` only where needed |
| "forced win" | stalemated defender counted as lost | G2 `replies` guard |
| "mate in n" | "at most n" versus "exactly n" | G6 `MateIn` |
| "bishops stay on their colour" | false per position after promotion | R5 per move, R7 budget |
| "material only decreases" | promotion changes kinds | R7: men, pawns, budget |
| "same position" | record or FEN equality | G16 `normalize`, FIDE 9.2.3 |
| "the game ends" | 50-move rule is a claim, not automatic | G12, G15 with explicit `L`, `R` |
| "dead position" | helpmate (exists) versus forced (for all) | G11 `CanMate` |
| "best move" | WDL-optimal is weak in won positions | O1, then O2/O3/O4 by name |
| "only move" | only winning move versus only mate within N | O2 versus O4 |
| "Stockfish says" | engine numbers inside theorems | never; engines only produce certificates |
| "tablebase says win" | which game (G∞, 50-move, 75-move)? | O9: hypotheses name the game |

---

## 10. Open questions for DESIGN and for the owner

1. **Side-indexed or side-relative semantics.** This document uses `WinsIn a n x` with an explicit
   attacker colour, as the prototype does, because claims are usually "White wins". A side-relative pair
   (`WinsIn n x` / `LosesIn n x`, "the side to move wins/loses") halves some case splits (*prior-work*
   §7). Recommendation: keep the attacker explicit; `value` (G10) is already side-relative.
2. **`Game` as a structure or a class.** A structure makes morphisms (G7) and multiple instances on the
   same state type (G∞ and `Clocked L` both on positions) easy to name. Recommendation: structure.
3. **How `Game.chess.Mated` is defined.** Executable (`InCheck p ∧ legalMoves p = []`) keeps Stage 1
   unblocked; the spec `Checkmate` is linked in G8. Recommendation: executable, bridged.
4. **Whether `Position` stores king squares.** See R9.
5. **The 50-move claim timing** (G15 hazard): check FIDE 9.3 and pick `L = 99` or `100` for the claim
   model.
6. **Which game is the default in headline theorems.** Recommendation: state wins in G∞ (`Game.chess`)
   and add the G15 corollary for the FIDE game whenever the clock headroom is available, so each
   headline theorem says both "wins in pure chess" and "wins under the FIDE rules from this clock".
