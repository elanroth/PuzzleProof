import Chess.Position

/-!
# Rules

The trusted specification of the FIDE Laws of Chess for moves: what a piece reaches and attacks,
check, the six movement rules, what a move does to a position, legality, checkmate and stalemate.
Specification: `docs/spec/Rules.md`; every definition below carries the docstring given there.

## Main definitions

* `Slides` and `Reaches`: the squares a piece of a given kind and colour would reach from a square,
  reading only the squares strictly between.
* `Board.AttacksFrom`, `Board.Attacked`, `Board.KingAttacked`, `Board.HasKing`, `InCheck`.
* The shapes of moves: `Move.IsEnPassant`, `Move.IsCastle`, `Move.IsDoublePush`, shared by the rules
  and by `play`; `Move.PromotionRule`, `Move.IsCapture`.
* The six rules `StepMove`, `PushMove`, `DoublePushMove`, `PawnCaptureMove`, `EnPassantMove`,
  `CastleMove`, joined by a disjunction into `PseudoLegal`. `Position.CanCastle` is the part of
  castling that does not depend on the move (FIDE 3.8.2.1–3.8.2.2).
* `Position.play`, total, as six named steps: `Move.pieceWrites`, `Move.enPassantWrites`,
  `Move.castleWrites` (the board, as lists of writes carried out by `Board.setMany`),
  `Move.castlingAfter`, `Move.epTargetAfter` and the turn.
* `Legal`, `Checkmate`, `Stalemate`.

## Main statements

* (R4) `play_board_of_not_mem`: a square the move does not touch keeps its contents, whatever the
  move. `play_board_src`, `play_board_dst`, `play_board_epVictim`, `play_board_rookHome`,
  `play_board_rookCastleSquare`: what the touched squares hold.
* (G1) `play_turn`: playing a move passes the turn, whatever the move.
* (R8) `castling_play_le`: playing a move adds no castling right.
* (R5) `PseudoLegal.isLight_dst_iff_of_bishop`, `PseudoLegal.isLight_dst_iff_of_knight`; and
  `PseudoLegal.promo_ne_none_iff`, the promise of `Move.promo`'s docstring.
* (R11) `checkmate_or_stalemate`, `not_checkmate_and_stalemate`.
* `reaches_congr`: `Reaches` reads only the squares strictly between (DESIGN §5.2), the shape R3's
  attack symmetry needs; `reaches_set_src`, `reaches_set_dst`, `slides_symm`.
* `Board.attacked_iff`: an attacked square is one some piece of that colour reaches, the form the
  attack theorems use.
* Bridges between `play` and the rules: `PseudoLegal.isEnPassant_iff`, `PseudoLegal.isCastle_iff`
  and `PseudoLegal.isDoublePush_iff` (among pseudo-legal moves each shape is exactly its rule);
  `PseudoLegal.attacksFrom_dst` (a move onto a piece is an attack on it);
  `PseudoLegal.touched_nodup` (no square is written twice).

## Implementation notes

* `Slides` is in index form: `t` is `i` steps away and every square `j < i` steps away is empty.
  "The square `j` steps away is empty" is `(s.shift d j).bind b = none`, which needs no quantifier
  over squares; in general `o.bind b` reads "what stands on the square `o`". Keep the binder order
  `∀ j < i, 0 < j → …`: it is the one core's bounded `Nat` instance decides.
* Every step of `play` reads only the position before the move. Steps 1–3 return lists of writes,
  and `Board.setMany` is the one place they are carried out, so R4's frame lemma is one list lemma
  (`Board.setMany_of_not_mem`) and `Move.touched` is the write list's squares by definition.
* Castling rights are revoked by squares (`Move.Revokes`): a move that leaves or lands on the home
  square of a king or of a rook costs the rights tied to that square, as in Stockfish. No board is
  read, so R8 is two lines.
* `CastleMove.decidable` is written by hand, guarded by the shape `Move.IsCastle`: the derived
  instance evaluated the attack tests for every candidate move in compiled code (measured 80 times
  slower). The guarded part is `Position.CanCastle`, so the instance restates nothing. Every other
  instance is `by unfold X; infer_instance`.
* After `cases k` on a `Kind`, goals come in constructor order (pawn, knight, bishop, rook, queen,
  king); proofs name them with `case`.
-/

namespace Chess

/-! ## Board helpers -/

/-- The colour of the piece on `s`, or `none` if `s` is empty. -/
def Board.colorAt (b : Board) (s : Square) : Option Color := (b s).map (·.color)

/-- The kind of the piece on `s`, or `none` if `s` is empty. -/
def Board.kindAt (b : Board) (s : Square) : Option Kind := (b s).map (·.kind)

/-- The board `b` after the writes `l`, made in order: each write, a pair of a square and its new
contents, makes that square hold those contents, and a later write to a square replaces an earlier
one. -/
def Board.setMany (b : Board) (l : List (Square × Option Piece)) : Board :=
  l.foldl (fun b wr => b.set wr.1 wr.2) b

namespace Board

variable {b : Board} {l : List (Square × Option Piece)} {s t : Square} {pc : Piece}
  {x : Option Piece}

/-- If `s` holds `pc`, the colour on `s` is `pc`'s colour. -/
@[simp] theorem colorAt_of_eq_some (h : b s = some pc) : b.colorAt s = some pc.color := by
  simp [colorAt, h]

/-- If `s` holds `pc`, the kind on `s` is `pc`'s kind. -/
@[simp] theorem kindAt_of_eq_some (h : b s = some pc) : b.kindAt s = some pc.kind := by
  simp [kindAt, h]

/-- No writes leave the board as it is. -/
@[simp] theorem setMany_nil (b : Board) : b.setMany [] = b := rfl

/-- Writing a list that starts with `wr` is making the write `wr`, then the rest. -/
@[simp] theorem setMany_cons (b : Board) (wr : Square × Option Piece)
    (l : List (Square × Option Piece)) : b.setMany (wr :: l) = (b.set wr.1 wr.2).setMany l := rfl

/-- Writing two lists one after the other is writing them one at a time. -/
theorem setMany_append (b : Board) (l l' : List (Square × Option Piece)) :
    b.setMany (l ++ l') = (b.setMany l).setMany l' :=
  List.foldl_append ..

/-- A square that no write mentions keeps its contents. -/
theorem setMany_of_not_mem (h : t ∉ l.map (·.1)) : b.setMany l t = b t := by
  induction l generalizing b with
  | nil => rfl
  | cons wr l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [setMany_cons, ih h.2, Board.set_ne h.1]

/-- If the writes `l` write no square twice, a square that `l` writes holds what was written
there. -/
theorem setMany_of_mem (hnd : (l.map (·.1)).Nodup) (h : (t, x) ∈ l) : b.setMany l t = x := by
  induction l generalizing b with
  | nil => cases h
  | cons wr l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | h
    · exact (setMany_of_not_mem hnd.1).trans (set_same ..)
    · exact ih hnd.2 h

/-- After the writes `l`, a square holds what it held before or what some write in `l` put there. -/
theorem setMany_eq_or_mem (b : Board) (l : List (Square × Option Piece)) (t : Square) :
    b.setMany l t = b t ∨ (t, b.setMany l t) ∈ l := by
  induction l generalizing b with
  | nil => exact .inl rfl
  | cons wr l ih =>
    rw [setMany_cons]
    rcases ih (b.set wr.1 wr.2) with h | h
    · rw [h, set_apply]
      split
      · next e => exact .inr (by subst e; simp)
      · exact .inl rfl
    · exact .inr (List.mem_cons_of_mem _ h)

end Board

/-! ## Reaching and attacking -/

/-- A piece sliding from `s` in direction `d` on board `b` reaches `t`: for some number of steps `i`
from 1 to 7, `t` is the square `i` steps from `s` in direction `d`, and for every `j` with
`0 < j < i` the square `j` steps from `s` is empty. So it reaches every square along `d` up to and
including the first occupied one. Only the squares strictly between `s` and `t` are read; `t`
itself may be empty or occupied (FIDE 3.5). -/
def Slides (d : Direction) (b : Board) (s t : Square) : Prop :=
  ∃ i < 8, 0 < i ∧ s.shift d i = some t ∧ ∀ j < i, 0 < j → (s.shift d j).bind b = none

/-- Sliding is decided by trying each number of steps from 1 to 7 and checking the squares in
between. -/
instance Slides.decidable (d : Direction) (b : Board) (s t : Square) :
    Decidable (Slides d b s t) := by
  unfold Slides; infer_instance

/-- A piece of kind `k` and colour `c` would reach `t` from `s` on board `b`, whatever actually
stands on `s`: a pawn the squares diagonally forward (at most two), a knight the squares a knight's
jump away, a king the adjacent squares (up to eight), and a bishop, rook or queen every square
along one of its directions up to and including the first occupied one. En passant aside, these
are the squares the piece could capture on. What stands on `s` and on `t` is not read, and neither
are pins (FIDE 3.1.3, 3.2–3.4, 3.6, 3.7.3, 3.8.1, 3.9.1). -/
def Reaches (k : Kind) (c : Color) (b : Board) (s t : Square) : Prop :=
  match k with
  | .pawn   => s.offset (-1) c.forward = some t ∨ s.offset 1 c.forward = some t
  | .knight => ∃ j ∈ knightJumps, s.offset j.1 j.2 = some t
  | .king   => ∃ d : Direction, s.shift d 1 = some t
  | .bishop | .rook | .queen => ∃ d ∈ k.slideDirections, Slides d b s t

/-- Reaching is decided kind by kind. -/
instance Reaches.decidable (k : Kind) (c : Color) (b : Board) (s t : Square) :
    Decidable (Reaches k c b s t) := by
  cases k <;> unfold Reaches <;> infer_instance

/-- The piece on `s` attacks `t`: `s` is not empty and the piece standing there reaches `t`. -/
def Board.AttacksFrom (b : Board) (s t : Square) : Prop :=
  match b s with
  | none    => False
  | some pc => Reaches pc.kind pc.color b s t

/-- Whether the piece on `s` attacks `t` is decided by reading `s` and then deciding `Reaches`. -/
instance Board.AttacksFrom.decidable (b : Board) (s t : Square) :
    Decidable (b.AttacksFrom s t) := by
  unfold Board.AttacksFrom; split <;> infer_instance

/-- Square `t` is attacked by colour `c`: some square holds a piece of colour `c` that attacks
`t`. En passant captures are not counted; they never capture a king. -/
def Board.Attacked (b : Board) (c : Color) (t : Square) : Prop :=
  ∃ s, b.colorAt s = some c ∧ b.AttacksFrom s t

/-- Whether `t` is attacked is decided by looking at every square. -/
instance Board.Attacked.decidable (b : Board) (c : Color) (t : Square) :
    Decidable (b.Attacked c t) := by
  unfold Board.Attacked; infer_instance

/-- A king of colour `c` is attacked: some square holding a king of colour `c` is attacked by the
other colour. False on a board with no king of colour `c`. -/
def Board.KingAttacked (b : Board) (c : Color) : Prop :=
  ∃ s, b s = some ⟨c, .king⟩ ∧ b.Attacked c.other s

/-- Whether a king of colour `c` is attacked is decided by looking at every square. -/
instance Board.KingAttacked.decidable (b : Board) (c : Color) : Decidable (b.KingAttacked c) := by
  unfold Board.KingAttacked; infer_instance

/-- Colour `c` has a king on board `b`: some square holds a king of colour `c`. -/
def Board.HasKing (b : Board) (c : Color) : Prop :=
  ∃ s, b s = some ⟨c, .king⟩

/-- Whether colour `c` has a king is decided by looking at every square. -/
instance Board.HasKing.decidable (b : Board) (c : Color) : Decidable (b.HasKing c) := by
  unfold Board.HasKing; infer_instance

/-- The side to move is in check: a king of the side to move is attacked (FIDE 3.9.1). -/
def InCheck (p : Position) : Prop := p.board.KingAttacked p.turn

/-- Whether the side to move is in check is decided on the board. -/
instance InCheck.decidable (p : Position) : Decidable (InCheck p) := by
  unfold InCheck; infer_instance

section Reaching

variable {k : Kind} {c : Color} {b b' : Board} {s t u : Square} {d : Direction}
  {x : Option Piece} {pc : Piece}

/-- Sliding needs no bound on the number of steps: `t` is reached exactly when it is a positive
number of steps away, with every square strictly between `s` and `t` empty. -/
theorem slides_iff : Slides d b s t ↔
    ∃ i, 0 < i ∧ s.shift d i = some t ∧ ∀ j < i, 0 < j → (s.shift d j).bind b = none := by
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, hi, h, hb⟩
    refine ⟨i, ?_, hi, h, hb⟩
    exact Nat.lt_of_not_le fun h8 => by simp [Square.shift_eq_none_of_eight_le h8] at h

/-- A pawn reaches the squares diagonally forward (at most two). -/
theorem reaches_pawn :
    Reaches .pawn c b s t ↔ s.offset (-1) c.forward = some t ∨ s.offset 1 c.forward = some t :=
  Iff.rfl

/-- A knight reaches the squares a knight's jump away. -/
theorem reaches_knight : Reaches .knight c b s t ↔ ∃ j ∈ knightJumps, s.offset j.1 j.2 = some t :=
  Iff.rfl

/-- A king reaches the adjacent squares (up to eight). -/
theorem reaches_king : Reaches .king c b s t ↔ ∃ d : Direction, s.shift d 1 = some t :=
  Iff.rfl

/-- A bishop reaches what it slides to diagonally. -/
theorem reaches_bishop :
    Reaches .bishop c b s t ↔ ∃ d ∈ Direction.diagonals, Slides d b s t :=
  Iff.rfl

/-- A rook reaches what it slides to along files and ranks. -/
theorem reaches_rook : Reaches .rook c b s t ↔ ∃ d ∈ Direction.orthogonals, Slides d b s t :=
  Iff.rfl

/-- A queen reaches what it slides to in any direction. -/
theorem reaches_queen : Reaches .queen c b s t ↔ ∃ d ∈ Direction.all, Slides d b s t :=
  Iff.rfl

/-- No piece reaches its own square. -/
theorem reaches_ne (h : Reaches k c b s t) : t ≠ s := by
  cases k
  case pawn => rcases h with h | h <;> exact Square.offset_ne_self (by simp) h
  case knight =>
    obtain ⟨j, hj, h⟩ := h
    rw [mem_knightJumps_iff] at hj
    exact Square.offset_ne_self (by omega) h
  case king =>
    obtain ⟨d, h⟩ := h
    rintro rfl
    exact Square.shift_ne_self Nat.one_pos h
  all_goals
    obtain ⟨d, -, i, -, hi, h, -⟩ := h
    rintro rfl
    exact Square.shift_ne_self hi h

/-- Only the squares strictly between `s` and `t` are read: two boards that agree on every square
other than `s` and `t` give the same answer. -/
theorem reaches_congr (h : ∀ u, u ≠ s → u ≠ t → b u = b' u) :
    Reaches k c b s t ↔ Reaches k c b' s t := by
  cases k <;> simp only [Reaches, Slides] <;> try exact Iff.rfl
  all_goals
    refine exists_congr fun d => and_congr_right fun _ => exists_congr fun i =>
      and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun ht =>
        forall_congr' fun j => forall_congr' fun hj => forall_congr' fun hj0 => ?_
    cases hu : s.shift d j with
    | none => rfl
    | some u =>
      -- `u` is `j` steps from `s`, with `0 < j < i`, and `t` is `i` steps away.
      have hus : u ≠ s := fun e => Square.shift_ne_self hj0 (e ▸ hu)
      have hut : u ≠ t := fun e =>
        Nat.ne_of_lt hj (Square.steps_eq_of_shift_eq hu (e ▸ ht))
      simp [h u hus hut]

/-- What stands on the attacker's square is not read. -/
theorem reaches_set_src : Reaches k c (b.set s x) s t ↔ Reaches k c b s t :=
  reaches_congr fun _ hu _ => Board.set_ne hu

/-- What stands on the target square is not read. -/
theorem reaches_set_dst : Reaches k c (b.set t x) s t ↔ Reaches k c b s t :=
  reaches_congr fun _ _ hu => Board.set_ne hu

/-- If `s` holds `pc`, the piece on `s` attacks `t` exactly when `pc` reaches `t` from `s`. -/
theorem attacksFrom_of_eq_some (h : b s = some pc) :
    b.AttacksFrom s t ↔ Reaches pc.kind pc.color b s t := by
  simp [Board.AttacksFrom, h]

/-- An empty square attacks nothing. -/
theorem not_attacksFrom_of_eq_none (h : b s = none) : ¬ b.AttacksFrom s t := by
  simp [Board.AttacksFrom, h]

/-- Square `t` is attacked by colour `c` exactly when some square holds a piece of colour `c` and
some kind `k` that reaches `t`. -/
theorem Board.attacked_iff :
    b.Attacked c t ↔ ∃ s k, b s = some ⟨c, k⟩ ∧ Reaches k c b s t := by
  constructor
  · rintro ⟨s, hc, ha⟩
    cases hs : b s with
    | none => exact absurd ha (not_attacksFrom_of_eq_none hs)
    | some pc =>
      obtain rfl : pc.color = c := by simpa [hs] using hc
      exact ⟨s, pc.kind, hs, (attacksFrom_of_eq_some hs).mp ha⟩
  · rintro ⟨s, k, hs, hr⟩
    exact ⟨s, by simp [hs], (attacksFrom_of_eq_some hs).mpr hr⟩

/-- On the empty board no king is attacked. -/
theorem not_kingAttacked_empty (c : Color) : ¬ Board.empty.KingAttacked c := by
  simp [Board.KingAttacked]

/-- One direction of `slides_symm`: a slide from `s` to `t` is a slide back from `t` to `s`. -/
theorem Slides.symm (h : Slides d b s t) : Slides d.opposite b t s := by
  obtain ⟨i, hi8, hi, hst, hb⟩ := h
  refine ⟨i, hi8, hi, Square.shift_eq_some_iff_opposite.mp hst, fun j hj hj0 => ?_⟩
  -- The square `j` steps back from `t` is the square `i - j` steps from `s`.
  have e := Square.shift_eq_shift_opposite hst (Nat.sub_le i j)
  rw [Nat.sub_sub_self (Nat.le_of_lt hj)] at e
  rw [← e]
  exact hb (i - j) (by omega) (by omega)

/-- Sliding is symmetric: a slider on `s` reaches `t` in direction `d` exactly when one on `t`
reaches `s` in the opposite direction. -/
theorem slides_symm : Slides d b s t ↔ Slides d.opposite b t s :=
  ⟨Slides.symm, fun h => by simpa using h.symm⟩

/-- A board with no king of colour `c` has no attacked king of colour `c`. -/
theorem not_kingAttacked_of_not_hasKing (h : ¬ b.HasKing c) : ¬ b.KingAttacked c :=
  fun ⟨s, hs, _⟩ => h ⟨s, hs⟩

end Reaching

/-! ## Shapes of moves -/

/-- Move `m` has the shape of an en passant capture in `p`: it moves a pawn of the side to move to
the en passant target, which is empty, changing file. Whether it is allowed is `EnPassantMove`. -/
def Move.IsEnPassant (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ p.epTarget = some m.dst ∧ p.board m.dst = none ∧
    m.src.file ≠ m.dst.file

/-- Whether `m` has the shape of an en passant capture is decided by reading the position. -/
instance Move.IsEnPassant.decidable (p : Position) (m : Move) : Decidable (m.IsEnPassant p) := by
  unfold Move.IsEnPassant; infer_instance

/-- Move `m` has the shape of castling to wing `w` in `p`: the side to move's king goes from its
home square to its castling square on wing `w` (e1g1, e1c1, e8g8, e8c8). Whether it is allowed is
`CastleMove`. -/
def Move.IsCastle (p : Position) (w : Wing) (m : Move) : Prop :=
  m.src = kingHome p.turn ∧ p.board m.src = some ⟨p.turn, .king⟩ ∧
    m.dst = kingCastleSquare p.turn w

/-- Whether `m` has the shape of castling to `w` is decided by reading the position. -/
instance Move.IsCastle.decidable (p : Position) (w : Wing) (m : Move) :
    Decidable (m.IsCastle p w) := by
  unfold Move.IsCastle; infer_instance

/-- Move `m` has the shape of a pawn's two-square advance in `p`: it moves a pawn of the side to
move two squares straight forward. Whether it is allowed is `DoublePushMove`. -/
def Move.IsDoublePush (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.src.offset 0 (2 * p.turn.forward) = some m.dst

/-- Whether `m` has the shape of a double push is decided by reading the position. -/
instance Move.IsDoublePush.decidable (p : Position) (m : Move) :
    Decidable (m.IsDoublePush p) := by
  unfold Move.IsDoublePush; infer_instance

/-- The square of the pawn an en passant capture `m` removes: on `m.dst`'s file and `m.src`'s
rank, beside the capturing pawn. -/
def Move.epVictim (m : Move) : Square := ⟨m.dst.file, m.src.rank⟩

/-- The promotion rule for a pawn move `m` by colour `c`: `m` names a promotion choice exactly when
it ends on `c`'s last rank. A pawn reaching the last rank must promote (FIDE 3.7.3.3). -/
def Move.PromotionRule (c : Color) (m : Move) : Prop :=
  m.promo ≠ none ↔ m.dst.relRank c = 7

/-- Whether the promotion rule holds is decided by comparing two facts. -/
instance Move.PromotionRule.decidable (c : Color) (m : Move) : Decidable (m.PromotionRule c) := by
  unfold Move.PromotionRule; infer_instance

/-- Move `m` is a capture in `p`: its destination holds a piece, or it captures en passant. -/
def Move.IsCapture (p : Position) (m : Move) : Prop :=
  p.board m.dst ≠ none ∨ m.IsEnPassant p

/-- Whether `m` is a capture is decided by reading the position. -/
instance Move.IsCapture.decidable (p : Position) (m : Move) : Decidable (m.IsCapture p) := by
  unfold Move.IsCapture; infer_instance

section Shapes

variable {p : Position} {m : Move} {w w' : Wing}

/-- A move has the shape of castling to at most one wing. -/
theorem Move.IsCastle.wing_eq (h : m.IsCastle p w) (h' : m.IsCastle p w') : w = w' := by
  have := h.2.2.symm.trans h'.2.2
  revert this
  cases p.turn <;> cases w <;> cases w' <;> decide

/-- A move with the shape of en passant does not have the shape of castling. -/
theorem Move.IsEnPassant.not_isCastle (h : m.IsEnPassant p) (w : Wing) : ¬ m.IsCastle p w := by
  intro hc
  have := h.1.symm.trans hc.2.1
  simp at this

/-- For a move with the shape of en passant, the victim square is not the source square. -/
theorem Move.IsEnPassant.epVictim_ne_src (h : m.IsEnPassant p) : m.epVictim ≠ m.src :=
  fun e => h.2.2.2 (congrArg Square.file e).symm

end Shapes

/-! ## Movement rules -/

/-- A step move is any non-pawn move other than castling: a knight, bishop, rook, queen or king of
the side to move goes from `m.src` to a square it reaches, which does not hold a piece of its own
colour; no promotion choice (FIDE 3.1, 3.2–3.6, 3.8.1). -/
def StepMove (p : Position) (m : Move) : Prop :=
  ∃ k, k ≠ .pawn ∧ p.board m.src = some ⟨p.turn, k⟩ ∧ Reaches k p.turn p.board m.src m.dst ∧
    p.board.colorAt m.dst ≠ some p.turn ∧ m.promo = none

/-- Whether `m` is a step move is decided by reading the position. -/
instance StepMove.decidable (p : Position) (m : Move) : Decidable (StepMove p m) := by
  unfold StepMove; infer_instance

/-- A pawn of the side to move goes one square straight forward to an empty square, and promotes
exactly when that square is on the last rank (FIDE 3.7.1, 3.7.3.3). -/
def PushMove (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.src.offset 0 p.turn.forward = some m.dst ∧
    p.board m.dst = none ∧ m.PromotionRule p.turn

/-- Whether `m` is a push is decided by reading the position. -/
instance PushMove.decidable (p : Position) (m : Move) : Decidable (PushMove p m) := by
  unfold PushMove; infer_instance

/-- A pawn of the side to move on its second rank goes two squares straight forward; the square it
passes over and the square it lands on are both empty; no promotion choice (FIDE 3.7.2). -/
def DoublePushMove (p : Position) (m : Move) : Prop :=
  m.IsDoublePush p ∧ m.src.relRank p.turn = 1 ∧
    (m.src.offset 0 p.turn.forward).bind p.board = none ∧ p.board m.dst = none ∧ m.promo = none

/-- Whether `m` is a double push is decided by reading the position. -/
instance DoublePushMove.decidable (p : Position) (m : Move) : Decidable (DoublePushMove p m) := by
  unfold DoublePushMove; infer_instance

/-- A pawn of the side to move captures a piece of the other colour diagonally forward, and promotes
exactly when it lands on the last rank (FIDE 3.7.3, 3.7.3.3). -/
def PawnCaptureMove (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ Reaches .pawn p.turn p.board m.src m.dst ∧
    p.board.colorAt m.dst = some p.turn.other ∧ m.PromotionRule p.turn

/-- Whether `m` is a pawn capture is decided by reading the position. -/
instance PawnCaptureMove.decidable (p : Position) (m : Move) :
    Decidable (PawnCaptureMove p m) := by
  unfold PawnCaptureMove; infer_instance

/-- A pawn of the side to move captures en passant: it moves diagonally forward onto the en passant
target, which is empty and lies on its sixth rank; a pawn of the other colour stands on the square
beside the capturing pawn on the target's file (the victim square); the square that pawn would
have come from, one square further forward than the target from the capturer's side, is empty; no
promotion choice (FIDE 3.7.3.1–3.7.3.2). -/
def EnPassantMove (p : Position) (m : Move) : Prop :=
  m.IsEnPassant p ∧ Reaches .pawn p.turn p.board m.src m.dst ∧ m.dst.relRank p.turn = 5 ∧
    p.board m.epVictim = some ⟨p.turn.other, .pawn⟩ ∧
    (m.dst.offset 0 p.turn.forward).bind p.board = none ∧ m.promo = none

/-- Whether `m` is an en passant capture is decided by reading the position. -/
instance EnPassantMove.decidable (p : Position) (m : Move) : Decidable (EnPassantMove p m) := by
  unfold EnPassantMove; infer_instance

/-- The side to move may castle to wing `w` now, as far as the position before the move decides:
it still holds that castling right; its rook stands on its home square on wing `w`; every square
between king and rook is empty; the side to move is not in check; and the square the king crosses
is not attacked by the other colour (FIDE 3.8.2.1, 3.8.2.2). The square the king lands on is
tested by `Legal`. -/
def Position.CanCastle (p : Position) (w : Wing) : Prop :=
  p.castling.get p.turn w = true ∧ p.board (rookHome p.turn w) = some ⟨p.turn, .rook⟩ ∧
    (∀ s ∈ betweenKingAndRook p.turn w, p.board s = none) ∧
    ¬ InCheck p ∧ ¬ p.board.Attacked p.turn.other (rookCastleSquare p.turn w)

/-- Whether the side to move may castle to `w` is decided by reading the position. -/
instance Position.CanCastle.decidable (p : Position) (w : Wing) : Decidable (p.CanCastle w) := by
  unfold Position.CanCastle; infer_instance

/-- The side to move castles to wing `w`: its king moves from its home square to its castling
square (`Move.IsCastle`), castling to `w` is allowed now (`Position.CanCastle`), and the move names
no promotion choice (FIDE 3.8.2). -/
def CastleMove (p : Position) (w : Wing) (m : Move) : Prop :=
  m.IsCastle p w ∧ p.CanCastle w ∧ m.promo = none

/-- Castling is decided by checking the shape of the move first, so that the attack tests run only
for the king's two castling moves. -/
instance CastleMove.decidable (p : Position) (w : Wing) (m : Move) :
    Decidable (CastleMove p w m) :=
  if h : m.IsCastle p w then
    decidable_of_iff (p.CanCastle w ∧ m.promo = none) (and_iff_right h).symm
  else isFalse fun hc => h hc.1

/-- Move `m` obeys the movement rules for the side to move in `p` (FIDE 3.1–3.8), ignoring whether
its own king is attacked afterwards: it is a step, a push, a double push, a pawn capture, an en
passant capture, or castling to some wing. -/
def PseudoLegal (p : Position) (m : Move) : Prop :=
  StepMove p m ∨ PushMove p m ∨ DoublePushMove p m ∨ PawnCaptureMove p m ∨ EnPassantMove p m ∨
    ∃ w, CastleMove p w m

/-- Whether `m` is pseudo-legal is decided rule by rule. -/
instance PseudoLegal.decidable (p : Position) (m : Move) : Decidable (PseudoLegal p m) := by
  unfold PseudoLegal; infer_instance

section Movement

variable {p : Position} {m : Move} {k : Kind} {w : Wing}

/-- A pawn's rank step is not zero. -/
private theorem Color.forward_ne_zero (c : Color) : c.forward ≠ 0 := by
  cases c <;> decide

/-- A pawn's two-square rank step is not zero. -/
private theorem Color.two_mul_forward_ne_zero (c : Color) : 2 * c.forward ≠ 0 := by
  cases c <;> decide

/-- An offset with no file step stays on the file. -/
private theorem Square.file_eq_of_offset_zero {s t : Square} {dr : Int}
    (h : s.offset 0 dr = some t) : s.file = t.file := by
  rw [Square.offset_eq_some_iff] at h
  exact Fin.ext (by omega)

/-- The king's castling square is not one king step from its home square. -/
private theorem shift_kingHome_one_ne (c : Color) (w : Wing) (d : Direction) :
    (kingHome c).shift d 1 ≠ some (kingCastleSquare c w) := by
  revert d; cases c <;> cases w <;> decide

/-- A pseudo-legal move moves a piece of the side to move. -/
theorem PseudoLegal.colorAt_src (h : PseudoLegal p m) : p.board.colorAt m.src = some p.turn := by
  rcases h with ⟨k, -, h, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨w, ⟨-, h, -⟩, -⟩ <;>
    simp [h]

/-- A pseudo-legal move does not stay on its square. -/
theorem PseudoLegal.dst_ne_src (h : PseudoLegal p m) : m.dst ≠ m.src := by
  rcases h with ⟨k, -, -, hr, -⟩ | ⟨-, ho, -⟩ | ⟨⟨-, ho⟩, -⟩ | ⟨-, hr, -⟩ | ⟨-, hr, -⟩ |
    ⟨w, ⟨hs, -, hd⟩, -⟩
  · exact reaches_ne hr
  · exact Square.offset_ne_self (.inr (Color.forward_ne_zero _)) ho
  · exact Square.offset_ne_self (.inr (Color.two_mul_forward_ne_zero _)) ho
  · exact reaches_ne hr
  · exact reaches_ne hr
  · rw [hs, hd]
    exact kingCastleSquare_ne_kingHome _ _ _

/-- A pseudo-legal pawn move changes rank. -/
theorem PseudoLegal.rank_ne_of_pawn (h : PseudoLegal p m)
    (hp : p.board m.src = some ⟨p.turn, .pawn⟩) : m.dst.rank ≠ m.src.rank := by
  -- Any offset with a nonzero rank step changes rank.
  have key : ∀ df dr : Int, dr ≠ 0 → m.src.offset df dr = some m.dst →
      m.dst.rank ≠ m.src.rank := by
    intro df dr hdr ho e
    rw [Square.offset_eq_some_iff, e] at ho
    omega
  have hf := Color.forward_ne_zero p.turn
  have h2 := Color.two_mul_forward_ne_zero p.turn
  rcases h with ⟨k, hk, hs, -⟩ | ⟨-, ho, -⟩ | ⟨⟨-, ho⟩, -⟩ | ⟨-, hr, -⟩ | ⟨-, hr, -⟩ |
    ⟨w, ⟨-, hs, -⟩, -⟩
  · rw [hp] at hs
    cases hs
    exact absurd rfl hk
  · exact key _ _ hf ho
  · exact key _ _ h2 ho
  · rcases hr with ho | ho <;> exact key _ _ hf ho
  · rcases hr with ho | ho <;> exact key _ _ hf ho
  · rw [hp] at hs
    cases hs

/-- A pseudo-legal move of a piece that is neither a pawn nor a king is a step move. -/
theorem PseudoLegal.stepMove_of_kindAt (h : PseudoLegal p m) (hk : p.board.kindAt m.src = some k)
    (hp : k ≠ .pawn) (hking : k ≠ .king) : StepMove p m := by
  rcases h with h | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨w, ⟨-, h, -⟩, -⟩
  · exact h
  all_goals
    simp [Board.kindAt, h] at hk
    first | exact absurd hk.symm hp | exact absurd hk.symm hking

/-- A pseudo-legal move does not land on a piece of the mover's own colour. -/
theorem PseudoLegal.colorAt_dst_ne (h : PseudoLegal p m) :
    p.board.colorAt m.dst ≠ some p.turn := by
  rcases h with ⟨k, -, -, -, h, -⟩ | ⟨-, -, he, -⟩ | ⟨-, -, -, he, -⟩ | ⟨-, -, h, -⟩ |
    ⟨⟨-, -, he, -⟩, -⟩ | ⟨w, ⟨-, -, hd⟩, ⟨-, -, hb, -⟩, -⟩
  · exact h
  · simp [Board.colorAt, he]
  · simp [Board.colorAt, he]
  · rw [h]
    simp
  · simp [Board.colorAt, he]
  · -- The castling square lies between king and rook, all of which are empty.
    rw [hd, Board.colorAt, hb _ (kingCastleSquare_mem_between _ _)]
    simp

/-- A pseudo-legal move has the shape of a double push exactly when it is a double push. -/
theorem PseudoLegal.isDoublePush_iff (h : PseudoLegal p m) :
    m.IsDoublePush p ↔ DoublePushMove p m := by
  refine ⟨fun hd => ?_, fun hd => hd.1⟩
  obtain ⟨hp, ho⟩ := hd
  -- Two offsets from `m.src` that reach `m.dst` have the same steps.
  have same := fun {df dr : Int} (h' : m.src.offset df dr = some m.dst) =>
    Square.steps_eq_of_offset_eq ho h'
  have hf := Color.forward_ne_zero p.turn
  rcases h with ⟨k, hk, hs, -⟩ | ⟨-, ho', -⟩ | h | ⟨-, hr, -⟩ | ⟨-, hr, -⟩ |
    ⟨w, ⟨-, hs, -⟩, -⟩
  · rw [hp] at hs
    cases hs
    exact absurd rfl hk
  · have := (same ho').2
    omega
  · exact h
  · rcases hr with ho' | ho' <;> have := (same ho').1 <;> omega
  · rcases hr with ho' | ho' <;> have := (same ho').1 <;> omega
  · rw [hp] at hs
    cases hs

/-- A pseudo-legal move has the shape of an en passant capture exactly when it is one. -/
theorem PseudoLegal.isEnPassant_iff (h : PseudoLegal p m) :
    m.IsEnPassant p ↔ EnPassantMove p m := by
  refine ⟨fun he => ?_, fun he => he.1⟩
  obtain ⟨hp, -, hd, hfile⟩ := he
  rcases h with ⟨k, hk, hs, -⟩ | ⟨-, ho, -⟩ | ⟨⟨-, ho⟩, -⟩ | ⟨-, -, hc, -⟩ | h |
    ⟨w, ⟨-, hs, -⟩, -⟩
  · -- The source holds a pawn, not another kind.
    rw [hp] at hs
    cases hs
    exact absurd rfl hk
  · exact absurd (Square.file_eq_of_offset_zero ho) hfile
  · exact absurd (Square.file_eq_of_offset_zero ho) hfile
  · simp [Board.colorAt, hd] at hc
  · exact h
  · rw [hp] at hs
    cases hs

/-- A pseudo-legal move has the shape of castling to wing `w` exactly when it castles to `w`. -/
theorem PseudoLegal.isCastle_iff (h : PseudoLegal p m) : m.IsCastle p w ↔ CastleMove p w m := by
  refine ⟨fun hc => ?_, fun hc => hc.1⟩
  obtain ⟨hsrc, hk, hdst⟩ := hc
  rcases h with ⟨k, -, hs, hr, -⟩ | ⟨hs, -⟩ | ⟨⟨hs, -⟩, -⟩ | ⟨hs, -⟩ | ⟨⟨hs, -⟩, -⟩ |
    ⟨w', hcm⟩
  · -- A king's step is one square; castling moves it two.
    rw [hk] at hs
    cases hs
    obtain ⟨d, hd⟩ := hr
    rw [hsrc, hdst] at hd
    exact absurd hd (shift_kingHome_one_ne _ _ _)
  -- The four pawn rules need a pawn on the source, which holds a king.
  iterate 4 · rw [hk] at hs; cases hs
  · obtain rfl := hcm.1.wing_eq ⟨hsrc, hk, hdst⟩
    exact hcm

/-- A pseudo-legal move onto a square holding a piece attacks that square. -/
theorem PseudoLegal.attacksFrom_dst (h : PseudoLegal p m) (hd : p.board m.dst ≠ none) :
    p.board.AttacksFrom m.src m.dst := by
  rcases h with ⟨k, -, hs, hr, -⟩ | ⟨-, -, he, -⟩ | ⟨-, -, -, he, -⟩ | ⟨hs, hr, -⟩ |
    ⟨⟨-, -, he, -⟩, -⟩ | ⟨w, ⟨-, -, hdst⟩, ⟨-, -, hb, -⟩, -⟩
  · exact (attacksFrom_of_eq_some hs).mpr hr
  · exact absurd he hd
  · exact absurd he hd
  · exact (attacksFrom_of_eq_some hs).mpr hr
  · exact absurd he hd
  · -- The castling square lies between king and rook, all of which are empty.
    rw [hdst] at hd
    exact absurd (hb _ (kingCastleSquare_mem_between _ _)) hd

end Movement

/-! ## Playing a move -/

/-- Step 1 of a move, the piece moves: `m.src` becomes empty, and `m.dst` receives the piece that
stood on `m.src`, whatever its kind, promoted as `m.promo` says. (If `m.src` was empty, `m.dst`
becomes empty.) -/
def Move.pieceWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  [(m.src, none), (m.dst, (p.board m.src).map (·.promote m.promo))]

/-- Step 2 of a move, en passant: if `m` has the shape of an en passant capture, the victim square
becomes empty. -/
def Move.enPassantWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  if m.IsEnPassant p then [(m.epVictim, none)] else []

/-- Step 3 of a move, castling: for each wing `w`, if `m` has the shape of castling to `w`, whatever
stands on the rook's home square on `w` moves to the square the king crosses. (If that square is
empty, the crossed square becomes empty.) -/
def Move.castleWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  Wing.all.flatMap fun w =>
    if m.IsCastle p w then
      [(rookHome p.turn w, none), (rookCastleSquare p.turn w, p.board (rookHome p.turn w))]
    else []

/-- Everything move `m` writes on the board, in order: steps 1, 2 and 3. -/
def Move.boardWrites (p : Position) (m : Move) : List (Square × Option Piece) :=
  m.pieceWrites p ++ m.enPassantWrites p ++ m.castleWrites p

/-- The squares move `m` writes on: its source and destination, the victim square of an en passant
capture, and the rook's two squares when castling. No other square changes (R4). -/
def Move.touched (p : Position) (m : Move) : List Square := (m.boardWrites p).map (·.1)

/-- Move `m` costs colour `c` its castling right on wing `w`: it leaves or lands on the home square
of `c`'s king or of `c`'s rook on wing `w`. A move of the king or of that rook from home, and a
capture of that rook at home, all do this (FIDE 3.8.2.1); landing on the rook's home square also
revokes the right, so that no other rook arriving there later can be castled with. -/
def Move.Revokes (m : Move) (c : Color) (w : Wing) : Prop :=
  m.src = kingHome c ∨ m.src = rookHome c w ∨ m.dst = kingHome c ∨ m.dst = rookHome c w

/-- Whether `m` costs a right is decided by comparing squares. -/
instance Move.Revokes.decidable (m : Move) (c : Color) (w : Wing) : Decidable (m.Revokes c w) := by
  unfold Move.Revokes; infer_instance

/-- The castling rights given by `f`: for every colour `c` and wing `w`, `c`'s right on `w` is held
exactly when `f c w` is true. -/
def CastlingRights.ofGet (f : Color → Wing → Bool) : CastlingRights :=
  ⟨f .white .kingside, f .white .queenside, f .black .kingside, f .black .queenside⟩

/-- The rights built from `f` hold `c`'s right on `w` exactly when `f c w` is true. -/
@[simp] theorem CastlingRights.get_ofGet (f : Color → Wing → Bool) (c : Color) (w : Wing) :
    (CastlingRights.ofGet f).get c w = f c w := by
  cases c <;> cases w <;> rfl

/-- Step 4 of a move, castling rights: a right is held after `m` exactly when it was held before
and `m` does not cost it. -/
def Move.castlingAfter (p : Position) (m : Move) : CastlingRights :=
  CastlingRights.ofGet fun c w => p.castling.get c w && !decide (m.Revokes c w)

/-- Step 5 of a move, the en passant target: after a pawn's two-square advance, the square it
passed over; after any other move, none. -/
def Move.epTargetAfter (p : Position) (m : Move) : Option Square :=
  if m.IsDoublePush p then m.src.offset 0 p.turn.forward else none

/-- The position after move `m` in `p`: the board after steps 1–3, the turn passed to the other
side (step 6), the castling rights after step 4, and the en passant target of step 5. Defined for
every move; the theorems say what it does to pseudo-legal ones. -/
def Position.play (p : Position) (m : Move) : Position where
  board    := p.board.setMany (m.boardWrites p)
  turn     := p.turn.other
  castling := m.castlingAfter p
  epTarget := m.epTargetAfter p

/-! ## Legality and terminal positions -/

/-- Move `m` is legal in `p`: it obeys the movement rules, and after it no king of the mover's
colour is attacked (FIDE 3.9.2). -/
def Legal (p : Position) (m : Move) : Prop :=
  PseudoLegal p m ∧ ¬ (p.play m).board.KingAttacked p.turn

/-- Whether `m` is legal is decided by deciding the rules and then playing the move. -/
instance Legal.decidable (p : Position) (m : Move) : Decidable (Legal p m) := by
  unfold Legal; infer_instance

/-- The side to move is checkmated: it is in check and has no legal move (FIDE 5.1.1). -/
def Checkmate (p : Position) : Prop := InCheck p ∧ ∀ m, ¬ Legal p m

/-- Checkmate is decided by checking every candidate move. -/
instance Checkmate.decidable (p : Position) : Decidable (Checkmate p) := by
  unfold Checkmate; infer_instance

/-- The side to move is stalemated: it is not in check and has no legal move (FIDE 5.2.1). -/
def Stalemate (p : Position) : Prop := ¬ InCheck p ∧ ∀ m, ¬ Legal p m

/-- Stalemate is decided by checking every candidate move. -/
instance Stalemate.decidable (p : Position) : Decidable (Stalemate p) := by
  unfold Stalemate; infer_instance

/-! ## What a move changes (R4, R8) -/

section Play

variable {p : Position} {m : Move} {c : Color} {w : Wing} {t : Square}

/-- Playing a move passes the turn, whatever the move. -/
@[simp] theorem play_turn (p : Position) (m : Move) : (p.play m).turn = p.turn.other := rfl

/-- The board after `m` is the board with `m`'s writes made. -/
theorem play_board (p : Position) (m : Move) :
    (p.play m).board = p.board.setMany (m.boardWrites p) := rfl

/-- The rights after `m` are those of step 4. -/
theorem play_castling (p : Position) (m : Move) : (p.play m).castling = m.castlingAfter p := rfl

/-- The en passant target after `m` is that of step 5. -/
theorem play_epTarget (p : Position) (m : Move) : (p.play m).epTarget = m.epTargetAfter p := rfl

/-- For a move without the shape of en passant, step 2 writes nothing. -/
theorem Move.enPassantWrites_of_not_isEnPassant (h : ¬ m.IsEnPassant p) :
    m.enPassantWrites p = [] := by
  simp [Move.enPassantWrites, h]

/-- For a move with the shape of en passant, step 2 clears the victim square. -/
theorem Move.enPassantWrites_of_isEnPassant (h : m.IsEnPassant p) :
    m.enPassantWrites p = [(m.epVictim, none)] := by
  simp [Move.enPassantWrites, h]

/-- For a move with the shape of castling to no wing, step 3 writes nothing. -/
theorem Move.castleWrites_of_forall_not_isCastle (h : ∀ w, ¬ m.IsCastle p w) :
    m.castleWrites p = [] := by
  simp [Move.castleWrites, Wing.all, h]

/-- For a move with the shape of castling to wing `w`, step 3 moves what stands on that wing's rook
home square to the square the king crosses. -/
theorem Move.castleWrites_of_isCastle (h : m.IsCastle p w) :
    m.castleWrites p =
      [(rookHome p.turn w, none), (rookCastleSquare p.turn w, p.board (rookHome p.turn w))] := by
  have hne : ∀ w', w' ≠ w → ¬ m.IsCastle p w' := fun w' hw h' => hw (h'.wing_eq h)
  cases w
  · simp [Move.castleWrites, Wing.all, h, hne .queenside (by decide)]
  · simp [Move.castleWrites, Wing.all, h, hne .kingside (by decide)]

/-- `t` is touched by `m` exactly when it is the source, the destination, the victim square of a
move with the shape of en passant, or one of the rook's two squares of a move with the shape of
castling. -/
theorem Move.mem_touched :
    t ∈ m.touched p ↔ t = m.src ∨ t = m.dst ∨ (m.IsEnPassant p ∧ t = m.epVictim) ∨
      ∃ w, m.IsCastle p w ∧ (t = rookHome p.turn w ∨ t = rookCastleSquare p.turn w) := by
  have hep : (m.IsEnPassant p ∧ t = m.epVictim) ↔ t ∈ (m.enPassantWrites p).map (·.1) := by
    by_cases he : m.IsEnPassant p
    · simp [Move.enPassantWrites_of_isEnPassant he, he]
    · simp [Move.enPassantWrites_of_not_isEnPassant he, he]
  have hcastle : (∃ w, m.IsCastle p w ∧ (t = rookHome p.turn w ∨ t = rookCastleSquare p.turn w)) ↔
      t ∈ (m.castleWrites p).map (·.1) := by
    by_cases hc : ∃ w, m.IsCastle p w
    · obtain ⟨w, hw⟩ := hc
      rw [Move.castleWrites_of_isCastle hw]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun ⟨w', hw', ht⟩ => hw'.wing_eq hw ▸ ht, fun ht => ⟨w, hw, ht⟩⟩
    · rw [Move.castleWrites_of_forall_not_isCastle (not_exists.mp hc)]
      simp only [List.map_nil, List.not_mem_nil, iff_false]
      exact fun ⟨w, hw, _⟩ => hc ⟨w, hw⟩
  rw [hep, hcastle]
  simp [Move.touched, Move.boardWrites, Move.pieceWrites]

/-- The square a castling rook lands on is not a king's home square. -/
theorem rookCastleSquare_ne_kingHome (c c' : Color) (w : Wing) :
    rookCastleSquare c w ≠ kingHome c' := by
  cases c <;> cases c' <;> cases w <;> decide

/-- (R4) A square that the move does not touch keeps its contents, whatever the move. -/
theorem play_board_of_not_mem (h : t ∉ m.touched p) : (p.play m).board t = p.board t :=
  Board.setMany_of_not_mem h

/-- Steps 2 and 3 of a pseudo-legal move write neither its source nor its destination. -/
private theorem PseudoLegal.not_mem_rest (h : PseudoLegal p m) (ht : t = m.src ∨ t = m.dst) :
    t ∉ (m.enPassantWrites p ++ m.castleWrites p).map (·.1) := by
  simp only [List.map_append, List.mem_append, not_or]
  constructor
  · by_cases he : m.IsEnPassant p
    · -- The victim is on the source's rank but another file, so it is neither square.
      rw [Move.enPassantWrites_of_isEnPassant he]
      have hrank := h.rank_ne_of_pawn he.1
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      rintro rfl
      rcases ht with e | e
      · exact he.epVictim_ne_src e
      · exact hrank (by rw [← e]; rfl)
    · simp [Move.enPassantWrites_of_not_isEnPassant he]
  · by_cases hc : ∃ w, m.IsCastle p w
    · -- The king's two squares are neither of the rook's two squares.
      obtain ⟨w, hw⟩ := hc
      rw [Move.castleWrites_of_isCastle hw]
      rcases ht with rfl | rfl
      · simp [hw.1, kingHome_ne_rookHome, (rookCastleSquare_ne_kingHome _ _ _).symm]
      · simp [hw.2.2, kingCastleSquare_ne_rookHome,
          (rookCastleSquare_ne_kingCastleSquare _ _ _ _).symm]
    · rw [Move.castleWrites_of_forall_not_isCastle (not_exists.mp hc)]
      simp

/-- A pseudo-legal move writes no square twice. -/
theorem PseudoLegal.touched_nodup (h : PseudoLegal p m) : (m.touched p).Nodup := by
  rw [Move.touched, Move.boardWrites, List.append_assoc, List.map_append, List.nodup_append]
  refine ⟨?_, ?_, fun t ht t' ht' e => ?_⟩
  · -- Step 1 writes the source and the destination, which differ.
    simp [Move.pieceWrites, Ne.symm h.dst_ne_src]
  · -- Steps 2 and 3 write one square, or the rook's two squares, which differ, or nothing.
    by_cases he : m.IsEnPassant p
    · rw [Move.enPassantWrites_of_isEnPassant he,
        Move.castleWrites_of_forall_not_isCastle he.not_isCastle]
      simp
    · rw [Move.enPassantWrites_of_not_isEnPassant he]
      by_cases hc : ∃ w, m.IsCastle p w
      · obtain ⟨w, hw⟩ := hc
        simp [Move.castleWrites_of_isCastle hw, (rookCastleSquare_ne_rookHome _ _ _ _).symm]
      · simp [Move.castleWrites_of_forall_not_isCastle (not_exists.mp hc)]
  · -- Step 1's squares are not written by steps 2 and 3.
    subst e
    exact h.not_mem_rest (by simpa [Move.pieceWrites] using ht) ht'

/-- (R4) After a pseudo-legal move its source square is empty. -/
theorem play_board_src (h : PseudoLegal p m) : (p.play m).board m.src = none :=
  Board.setMany_of_mem h.touched_nodup (by simp [Move.boardWrites, Move.pieceWrites])

/-- (R4) After a pseudo-legal move its destination holds the piece from the source, promoted as the
move says. -/
theorem play_board_dst (h : PseudoLegal p m) :
    (p.play m).board m.dst = (p.board m.src).map (·.promote m.promo) :=
  Board.setMany_of_mem h.touched_nodup (by simp [Move.boardWrites, Move.pieceWrites])

/-- (R4) After a move with the shape of en passant the victim square is empty. -/
theorem play_board_epVictim (h : m.IsEnPassant p) : (p.play m).board m.epVictim = none := by
  rw [play_board, Move.boardWrites, Move.castleWrites_of_forall_not_isCastle (h.not_isCastle ·),
    Move.enPassantWrites_of_isEnPassant h]
  simp [Board.setMany_append]

/-- (R4) After a move with the shape of castling to wing `w` the rook's home square on `w` is
empty. -/
theorem play_board_rookHome (h : m.IsCastle p w) :
    (p.play m).board (rookHome p.turn w) = none := by
  have he : ¬ m.IsEnPassant p := fun he => he.not_isCastle w h
  rw [play_board, Move.boardWrites, Move.castleWrites_of_isCastle h,
    Move.enPassantWrites_of_not_isEnPassant he]
  simp [Board.setMany_append, Board.set_ne (rookCastleSquare_ne_rookHome _ _ _ _).symm]

/-- (R4) After a move with the shape of castling to wing `w` the square the king crossed holds what
stood on the rook's home square. -/
theorem play_board_rookCastleSquare (h : m.IsCastle p w) :
    (p.play m).board (rookCastleSquare p.turn w) = p.board (rookHome p.turn w) := by
  have he : ¬ m.IsEnPassant p := fun he => he.not_isCastle w h
  rw [play_board, Move.boardWrites, Move.castleWrites_of_isCastle h,
    Move.enPassantWrites_of_not_isEnPassant he]
  simp [Board.setMany_append]

/-- (R8) After `m`, colour `c` holds its right on wing `w` exactly when it held it before and `m`
does not cost it. -/
theorem get_play_castling :
    (p.play m).castling.get c w = true ↔ p.castling.get c w = true ∧ ¬ m.Revokes c w := by
  simp [Position.play, Move.castlingAfter]

/-- (R8) Playing any move adds no castling right. -/
theorem castling_play_le (p : Position) (m : Move) : (p.play m).castling ≤ p.castling :=
  fun _ _ h => (get_play_castling.mp h).1

end Play

/-! ## Sanity theorems (R5 and the promotion promise) -/

section Sanity

variable {p : Position} {m : Move}

/-- (R5) A pseudo-legal bishop move lands on a square of the same shade (light or dark) as the one
it left. -/
theorem PseudoLegal.isLight_dst_iff_of_bishop (h : PseudoLegal p m)
    (hb : p.board.kindAt m.src = some .bishop) : m.dst.IsLight ↔ m.src.IsLight := by
  obtain ⟨k, -, hsrc, hr, -⟩ := h.stepMove_of_kindAt hb (by decide) (by decide)
  obtain rfl : k = .bishop := by simpa [Board.kindAt, hsrc] using hb
  obtain ⟨d, hd, i, -, -, hi, -⟩ := hr
  exact Square.isLight_shift_of_mem_diagonals hd hi

/-- (R5) A pseudo-legal knight move lands on a square of the other shade. -/
theorem PseudoLegal.isLight_dst_iff_of_knight (h : PseudoLegal p m)
    (hn : p.board.kindAt m.src = some .knight) : m.dst.IsLight ↔ ¬ m.src.IsLight := by
  obtain ⟨k, -, hsrc, hr, -⟩ := h.stepMove_of_kindAt hn (by decide) (by decide)
  obtain rfl : k = .knight := by simpa [Board.kindAt, hsrc] using hn
  obtain ⟨j, hj, hjt⟩ := hr
  exact Square.isLight_iff_of_mem_knightJumps hj hjt

/-- A pseudo-legal move names a promotion choice exactly when a pawn reaches the last rank. -/
theorem PseudoLegal.promo_ne_none_iff (h : PseudoLegal p m) :
    m.promo ≠ none ↔ p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.dst.relRank p.turn = 7 := by
  rcases h with ⟨k, hk, hs, -, -, hpr⟩ | ⟨hs, -, -, hpr⟩ | ⟨⟨hs, ho⟩, h1, -, -, hpr⟩ |
    ⟨hs, -, -, hpr⟩ | ⟨-, -, h5, -, -, hpr⟩ | ⟨w, ⟨-, hs, -⟩, -, hpr⟩
  · -- A step move names no choice, and its piece is not a pawn.
    simp [hpr, hs, hk]
  · simpa [hs] using hpr
  · -- A double push lands on relative rank 3.
    have h3 := Square.relRank_of_offset_forward (dr := 2) ho
    rw [h1] at h3
    simp only [hpr, ne_eq, not_true_eq_false, false_iff, not_and]
    intro _ h7
    rw [h7] at h3
    revert h3
    decide
  · simpa [hs] using hpr
  · simp [hpr, h5]
  · simp [hpr, hs]

end Sanity

/-! ## Terminal positions (R11) -/

section Terminal

variable {p : Position} {m : Move}

/-- (R11) A side to move with no legal move is checkmated or stalemated. -/
theorem checkmate_or_stalemate (h : ∀ m, ¬ Legal p m) : Checkmate p ∨ Stalemate p :=
  if hc : InCheck p then .inl ⟨hc, h⟩ else .inr ⟨hc, h⟩

/-- (R11) No position is both checkmate and stalemate. -/
theorem not_checkmate_and_stalemate : ¬ (Checkmate p ∧ Stalemate p) :=
  fun ⟨h, h'⟩ => h'.1 h.1

/-- A legal move is pseudo-legal. -/
theorem Legal.pseudoLegal (h : Legal p m) : PseudoLegal p m := h.1

/-- After a legal move no king of the mover's colour is attacked. -/
theorem Legal.not_kingAttacked (h : Legal p m) : ¬ (p.play m).board.KingAttacked p.turn := h.2

/-- A side to move with no king is not in check. -/
theorem not_inCheck_of_not_hasKing (h : ¬ p.board.HasKing p.turn) : ¬ InCheck p :=
  not_kingAttacked_of_not_hasKing h

/-- A side to move with no king is not checkmated. -/
theorem not_checkmate_of_not_hasKing (h : ¬ p.board.HasKing p.turn) : ¬ Checkmate p :=
  fun hc => not_inCheck_of_not_hasKing h hc.1

/-- On the empty board the side to move is stalemated. -/
theorem stalemate_of_board_eq_empty (h : p.board = Board.empty) : Stalemate p := by
  refine ⟨?_, fun m hm => ?_⟩
  · unfold InCheck
    rw [h]
    exact not_kingAttacked_empty _
  · have := hm.pseudoLegal.colorAt_src
    simp [h, Board.colorAt] at this

/-- A side to move with no king has none after any move: promotion never makes a king, and the
castling writes need a king on the source square. -/
theorem not_hasKing_play (h : ¬ p.board.HasKing p.turn) :
    ¬ (p.play m).board.HasKing p.turn := by
  rintro ⟨t, ht⟩
  rcases Board.setMany_eq_or_mem p.board (m.boardWrites p) t with e | e
  · exact h ⟨t, e ▸ ht⟩
  · -- The king was written by the move. Steps 2 and 3 write no king here, so step 1 did.
    rw [play_board] at ht
    rw [ht] at e
    have hc : m.castleWrites p = [] :=
      Move.castleWrites_of_forall_not_isCastle fun _ hw => h ⟨_, hw.2.1⟩
    obtain ⟨-, e⟩ : t = m.dst ∧
        some ⟨p.turn, .king⟩ = (p.board m.src).map (·.promote m.promo) := by
      simpa [Move.boardWrites, Move.pieceWrites, Move.enPassantWrites, hc] using e
    obtain ⟨pc, hs, hp⟩ := Option.map_eq_some_iff.mp e.symm
    -- A promoted piece is a king only if it was one and no promotion was chosen.
    cases ho : m.promo with
    | none => exact h ⟨m.src, by rw [hs, ← hp, ho, Piece.promote_none]⟩
    | some pk =>
      rw [ho, Piece.promote_some] at hp
      exact PromoKind.toKind_ne_king pk (congrArg Piece.kind hp)

/-- For a side to move with no king, every pseudo-legal move is legal. -/
theorem legal_iff_pseudoLegal_of_not_hasKing (h : ¬ p.board.HasKing p.turn) :
    Legal p m ↔ PseudoLegal p m :=
  ⟨Legal.pseudoLegal, fun hm => ⟨hm, not_kingAttacked_of_not_hasKing (not_hasKing_play h)⟩⟩

end Terminal

/-! ## Tests -/

-- The initial position.
example : ¬ InCheck Position.initial := by decide
example : Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩ := by decide           -- e2e4
example : Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩ := by decide +kernel
example : ¬ Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 4⟩, none⟩ := by decide         -- e2e5
example : ¬ Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 3⟩, some .queen⟩ := by decide  -- e2e4=Q
example : Legal Position.initial ⟨⟨6, 0⟩, ⟨5, 2⟩, none⟩ := by decide           -- Ng1f3
example : ¬ Legal Position.initial ⟨⟨6, 0⟩, ⟨5, 2⟩, some .queen⟩ := by decide  -- Ng1f3=Q
example : ¬ Legal Position.initial ⟨⟨5, 0⟩, ⟨2, 3⟩, none⟩ := by decide         -- Bf1c4
example : (Position.initial.play ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩).epTarget = some ⟨4, 2⟩ := by decide
-- The initial position has exactly 20 legal moves.
#guard (Square.all.flatMap fun s => Square.all.flatMap fun t =>
  (none :: PromoKind.all.map some).filter fun o => decide (Legal Position.initial ⟨s, t, o⟩)).length
  == 20
-- e2e4 is blocked by a piece on e3, the square it passes over.
example : ¬ Legal
    { Position.initial with board := Position.initial.board.set ⟨4, 2⟩ (some ⟨.white, .knight⟩) }
    ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩ := by
  decide

/-- Fool's mate: 1. f3 e5 2. g4 Qh4#. -/
def foolsMate : Position :=
  (((Position.initial.play ⟨⟨5, 1⟩, ⟨5, 2⟩, none⟩).play ⟨⟨4, 6⟩, ⟨4, 4⟩, none⟩).play
    ⟨⟨6, 1⟩, ⟨6, 3⟩, none⟩).play ⟨⟨3, 7⟩, ⟨7, 3⟩, none⟩

example : InCheck foolsMate := by decide
#guard decide (Checkmate foolsMate)

/-- White king e1, rooks a1 and h1; Black king e8, rooks f8 and b8; White to move, White's two
rights only (Black's rooks are not at home). -/
def castlePos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨7, 0⟩ (some ⟨.white, .rook⟩)
    |>.set ⟨0, 0⟩ (some ⟨.white, .rook⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨5, 7⟩ (some ⟨.black, .rook⟩) |>.set ⟨1, 7⟩ (some ⟨.black, .rook⟩),
   .white, ⟨true, true, false, false⟩, none⟩

-- e1g1 crosses f1, which the f8 rook attacks.
example : ¬ Legal castlePos ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide
-- e1c1: b1 must be empty but may be attacked (by the b8 rook).
example : Legal castlePos ⟨⟨4, 0⟩, ⟨2, 0⟩, none⟩ := by decide
example : (castlePos.play ⟨⟨4, 0⟩, ⟨2, 0⟩, none⟩).board ⟨3, 0⟩ = some ⟨.white, .rook⟩ := by
  decide
example : (castlePos.play ⟨⟨4, 0⟩, ⟨2, 0⟩, none⟩).castling = CastlingRights.none := by decide
-- Rh1h2 costs White the kingside right only.
example : (castlePos.play ⟨⟨7, 0⟩, ⟨7, 1⟩, none⟩).castling = ⟨false, true, false, false⟩ := by
  decide

/-- Black king e8 and rook h8; White king e1; Black to move, Black's kingside right only. -/
def blackCastlePos : Position :=
  ⟨Board.empty |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨7, 7⟩ (some ⟨.black, .rook⟩)
    |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩),
   .black, ⟨false, false, true, false⟩, none⟩

-- e8g8, and the rook lands on f8.
example : Legal blackCastlePos ⟨⟨4, 7⟩, ⟨6, 7⟩, none⟩ := by decide
example : (blackCastlePos.play ⟨⟨4, 7⟩, ⟨6, 7⟩, none⟩).board ⟨5, 7⟩ = some ⟨.black, .rook⟩ := by
  decide

/-- White king e1, rooks a1 and h1; Black king b8 and a rook on `f`7; White to move, White's two
rights only. -/
def castleRookPos (f : Fin 8) : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨7, 0⟩ (some ⟨.white, .rook⟩)
    |>.set ⟨0, 0⟩ (some ⟨.white, .rook⟩) |>.set ⟨1, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨f, 6⟩ (some ⟨.black, .rook⟩),
   .white, ⟨true, true, false, false⟩, none⟩

-- Castling out of check (rook on e7): neither side.
example : ¬ Legal (castleRookPos 4) ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide
example : ¬ Legal (castleRookPos 4) ⟨⟨4, 0⟩, ⟨2, 0⟩, none⟩ := by decide
-- Castling through an attacked d1 (rook on d7): not queenside, but kingside.
example : ¬ Legal (castleRookPos 3) ⟨⟨4, 0⟩, ⟨2, 0⟩, none⟩ := by decide
example : Legal (castleRookPos 3) ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide

/-- White king e1 and pawn e5; Black king e8 and pawn d7; Black to move, no rights; then d7d5. -/
def epPos : Position :=
  (⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨4, 4⟩ (some ⟨.white, .pawn⟩) |>.set ⟨3, 6⟩ (some ⟨.black, .pawn⟩),
   .black, .none, none⟩ : Position).play ⟨⟨3, 6⟩, ⟨3, 4⟩, none⟩

example : epPos.epTarget = some ⟨3, 5⟩ := by decide
example : Legal epPos ⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ := by decide                       -- e5d6
example : (epPos.play ⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩).board ⟨3, 4⟩ = none := by decide
-- A stale target: after e1d1 and e8d8 the capture is gone.
example : (epPos.play ⟨⟨4, 0⟩, ⟨3, 0⟩, none⟩).epTarget = none := by decide
example : ¬ Legal ((epPos.play ⟨⟨4, 0⟩, ⟨3, 0⟩, none⟩).play ⟨⟨4, 7⟩, ⟨3, 7⟩, none⟩)
    ⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ := by decide

/-- White king a5 and pawn b5; Black king h8, rook h5 and pawn c7; Black to move, no rights; then
c7c5. -/
def epPinPos : Position :=
  (⟨Board.empty |>.set ⟨0, 4⟩ (some ⟨.white, .king⟩) |>.set ⟨1, 4⟩ (some ⟨.white, .pawn⟩)
    |>.set ⟨7, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨7, 4⟩ (some ⟨.black, .rook⟩)
    |>.set ⟨2, 6⟩ (some ⟨.black, .pawn⟩),
   .black, .none, none⟩ : Position).play ⟨⟨2, 6⟩, ⟨2, 4⟩, none⟩

-- b5c6 en passant empties b5 and c5, opening the fifth rank to the rook.
example : PseudoLegal epPinPos ⟨⟨1, 4⟩, ⟨2, 5⟩, none⟩ := by decide
example : ¬ Legal epPinPos ⟨⟨1, 4⟩, ⟨2, 5⟩, none⟩ := by decide

/-- White king e1, Black king e3; White to move, no rights. -/
def kingsPos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 2⟩ (some ⟨.black, .king⟩),
   .white, .none, none⟩

example : ¬ Legal kingsPos ⟨⟨4, 0⟩, ⟨4, 1⟩, none⟩ := by decide                  -- e1e2
example : Legal kingsPos ⟨⟨4, 0⟩, ⟨3, 0⟩, none⟩ := by decide                    -- e1d1

/-- White king e1 and pawn b7; Black king e8 and rooks a8 and h8; White to move, Black's two rights
only (White has no rooks). -/
def promoPos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨1, 6⟩ (some ⟨.white, .pawn⟩) |>.set ⟨0, 7⟩ (some ⟨.black, .rook⟩)
    |>.set ⟨7, 7⟩ (some ⟨.black, .rook⟩),
   .white, ⟨false, false, true, true⟩, none⟩

example : ¬ Legal promoPos ⟨⟨1, 6⟩, ⟨0, 7⟩, none⟩ := by decide                 -- b7a8
example : Legal promoPos ⟨⟨1, 6⟩, ⟨0, 7⟩, some .queen⟩ := by decide            -- b7a8=Q
example : Legal promoPos ⟨⟨1, 6⟩, ⟨1, 7⟩, some .knight⟩ := by decide           -- b7b8=N
example : (promoPos.play ⟨⟨1, 6⟩, ⟨0, 7⟩, some .queen⟩).board ⟨0, 7⟩ = some ⟨.white, .queen⟩ := by
  decide
-- Capturing the rook on a8 costs Black the queenside right only.
example : (promoPos.play ⟨⟨1, 6⟩, ⟨0, 7⟩, some .queen⟩).castling = ⟨false, false, true, false⟩ := by
  decide

/-- Black king e8 and pawn a2; White king h8; Black to move, no rights. -/
def blackPromoPos : Position :=
  ⟨Board.empty |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨0, 1⟩ (some ⟨.black, .pawn⟩)
    |>.set ⟨7, 7⟩ (some ⟨.white, .king⟩),
   .black, .none, none⟩

-- Black promotes on rank 1, and must name a choice.
example : Legal blackPromoPos ⟨⟨0, 1⟩, ⟨0, 0⟩, some .knight⟩ := by decide   -- a2a1=N
example : ¬ Legal blackPromoPos ⟨⟨0, 1⟩, ⟨0, 0⟩, none⟩ := by decide        -- a2a1

/-- White king e1 and bishop e2; Black king a8 and rook e8; White to move, no rights. -/
def pinPos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 1⟩ (some ⟨.white, .bishop⟩)
    |>.set ⟨0, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .rook⟩),
   .white, .none, none⟩

-- The bishop on e2 is pinned: Be2d3 is pseudo-legal but not legal.
example : PseudoLegal pinPos ⟨⟨4, 1⟩, ⟨3, 2⟩, none⟩ := by decide
example : ¬ Legal pinPos ⟨⟨4, 1⟩, ⟨3, 2⟩, none⟩ := by decide

/-- White king e1 and pawn e2; Black king e8 and pawn d4; White to move, no rights; then e2e4. -/
def blackEpPos : Position :=
  (⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨4, 1⟩ (some ⟨.white, .pawn⟩) |>.set ⟨3, 3⟩ (some ⟨.black, .pawn⟩),
   .white, .none, none⟩ : Position).play ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩

-- Black captures en passant on rank 3: d4e3 is legal and empties e4.
example : blackEpPos.epTarget = some ⟨4, 2⟩ := by decide
example : Legal blackEpPos ⟨⟨3, 3⟩, ⟨4, 2⟩, none⟩ := by decide                 -- d4e3
example : (blackEpPos.play ⟨⟨3, 3⟩, ⟨4, 2⟩, none⟩).board ⟨4, 3⟩ = none := by decide
-- With e4 emptied by hand, the target alone permits no capture.
example : ¬ Legal { blackEpPos with board := blackEpPos.board.set ⟨4, 3⟩ none }
    ⟨⟨3, 3⟩, ⟨4, 2⟩, none⟩ := by decide

/-- White king e1 and rook h1; Black king a8 and rook h8; White to move, White's kingside right
only. -/
def rookAttackedPos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨7, 0⟩ (some ⟨.white, .rook⟩)
    |>.set ⟨0, 7⟩ (some ⟨.black, .king⟩) |>.set ⟨7, 7⟩ (some ⟨.black, .rook⟩),
   .white, ⟨true, false, false, false⟩, none⟩

-- The rook may be attacked (h1, by the h8 rook): e1g1 is legal.
example : Legal rookAttackedPos ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide
-- A piece on g1 forbids it; so does an attack on g1 (a black rook on g8).
example : ¬ Legal { rookAttackedPos with
    board := rookAttackedPos.board.set ⟨6, 0⟩ (some ⟨.white, .knight⟩) }
    ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide
example : ¬ Legal { rookAttackedPos with
    board := rookAttackedPos.board.set ⟨6, 7⟩ (some ⟨.black, .rook⟩) }
    ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ := by decide

/-- White king e1; Black king e8, rook e2 and bishop h5; White to move, no rights. -/
def defendedPos : Position :=
  ⟨Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .king⟩)
    |>.set ⟨4, 1⟩ (some ⟨.black, .rook⟩) |>.set ⟨7, 4⟩ (some ⟨.black, .bishop⟩),
   .white, .none, none⟩

-- The king may not capture a defended piece (e1xe2; the h5 bishop defends e2); undefended, it may.
example : ¬ Legal defendedPos ⟨⟨4, 0⟩, ⟨4, 1⟩, none⟩ := by decide
example : Legal { defendedPos with board := defendedPos.board.set ⟨7, 4⟩ none }
    ⟨⟨4, 0⟩, ⟨4, 1⟩, none⟩ := by decide

-- Attack geometry.
example : Reaches .rook .white Board.empty ⟨0, 0⟩ ⟨0, 7⟩ := by decide
example : ¬ Reaches .rook .white (Board.empty.set ⟨0, 3⟩ (some ⟨.black, .pawn⟩)) ⟨0, 0⟩ ⟨0, 7⟩ := by
  decide
example : ¬ Reaches .knight .white Board.empty ⟨1, 0⟩ ⟨1, 2⟩ := by decide
-- A lone rook on e8 attacks the king on e1; a pawn on e4 blocks it.
example : (Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩)
    |>.set ⟨4, 7⟩ (some ⟨.black, .rook⟩)).KingAttacked .white := by decide
example : ¬ (Board.empty |>.set ⟨4, 0⟩ (some ⟨.white, .king⟩) |>.set ⟨4, 7⟩ (some ⟨.black, .rook⟩)
    |>.set ⟨4, 3⟩ (some ⟨.white, .pawn⟩)).KingAttacked .white := by decide

end Chess
