import Chess.Position

/-!
# Rules: definitions

The trusted part of `Chess.Rules`, and all of it: every definition of the module with its decision
procedure, in reading order, and nothing else. A chess player checks the rules against the FIDE
Laws by reading this file alone; the other files of `Chess.Rules` prove facts about these
definitions and are not trusted. Specification: `docs/spec/Rules.md` §1–§6 and §10; every
definition below carries the docstring given there.

## Main definitions

* `Slides` and `Reaches`: the squares a piece of a given kind and colour would reach from a square,
  reading only the squares strictly between.
* `Board.AttacksFrom`, `Board.AttackedBy`, `Board.KingAttacked`, `Board.HasKing`, `InCheck`.
  `b.AttackedBy c t` names the attacking colour `c`; `b.KingAttacked c` names the colour `c` of the
  king attacked, by the other colour.
* The shapes of moves: `Move.IsEnPassant`, `Move.IsCastle`, `Move.IsDoublePush`, shared by the rules
  and by `play`; `Move.PromotionRule`, `Move.IsCapture`.
* The six rules `PieceMove`, `PushMove`, `DoublePushMove`, `PawnCaptureMove`, `EnPassantMove`,
  `CastleMove`, joined by a disjunction into `PseudoLegal`. `Position.CanCastle` is the part of
  castling that does not depend on the move (FIDE 3.8.2.1–3.8.2.2).
* `Position.play`, total, as six named steps: `Move.pieceWrites`, `Move.enPassantWrites`,
  `Move.castleWrites` (the board, as lists of writes carried out by `Board.setMany`),
  `Move.castlingAfter`, `Move.epTargetAfter` and the turn.
* `Legal`, `Checkmate`, `Stalemate`.

## Implementation notes

* `Slides` is in index form: `t` is `i` steps away and every square `j < i` steps away is empty.
  "The square `j` steps away is empty" is `(s.shift d j).bind b = none`, which needs no quantifier
  over squares; in general `o.bind b` reads "what stands on the square `o`". Keep the binder order
  `∀ j < i, 0 < j → …`: it is the one core's bounded `Nat` instance decides.
* Relative ranks count from 0 (`Square.relRank`, `Chess.Basic`): `relRank c = 1` is `c`'s second
  rank, `5` its sixth, `7` its last. The docstrings give both.
* Every step of `play` reads only the position before the move. Steps 1–3 return lists of writes,
  and `Board.setMany` is the one place they are carried out, so R4's frame lemma is one list lemma
  (`Board.setMany_of_not_mem`) and `Move.touched` is the write list's squares by definition.
* Castling rights are revoked by squares (`Move.Revokes`): a move that leaves or lands on the home
  square of a king or of a rook costs the rights tied to that square, as in Stockfish. No board is
  read, so R8 is two lines. Step 4 builds the rights with `CastlingRights.ofGet` (`Chess.Position`).
* `CastleMove.decidable` is written by hand, guarded by the shape `Move.IsCastle`: the derived
  instance evaluated the attack tests for every candidate move in compiled code (measured 80 times
  slower). The guarded part is `Position.CanCastle`, so the instance restates nothing. Every other
  instance unfolds the definition and calls `infer_instance`, after `cases` or `split` where
  needed.
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
def Board.AttackedBy (b : Board) (c : Color) (t : Square) : Prop :=
  ∃ s, b.colorAt s = some c ∧ b.AttacksFrom s t

/-- Whether `t` is attacked is decided by looking at every square. -/
instance Board.AttackedBy.decidable (b : Board) (c : Color) (t : Square) :
    Decidable (b.AttackedBy c t) := by
  unfold Board.AttackedBy; infer_instance

/-- A king of colour `c` is attacked: some square holding a king of colour `c` is attacked by the
other colour. False on a board with no king of colour `c`. -/
def Board.KingAttacked (b : Board) (c : Color) : Prop :=
  ∃ s, b s = some ⟨c, .king⟩ ∧ b.AttackedBy c.other s

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
it ends on `c`'s last rank (`relRank c = 7`, counting from 0). A pawn reaching the last rank must
promote (FIDE 3.7.3.3). -/
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

/-! ## Movement rules -/

/-- A piece move is any non-pawn move other than castling: a knight, bishop, rook, queen or king of
the side to move goes from `m.src` to a square it reaches, which does not hold a piece of its own
colour; no promotion choice (FIDE 3.1, 3.2–3.6, 3.8.1). -/
def PieceMove (p : Position) (m : Move) : Prop :=
  ∃ k, k ≠ .pawn ∧ p.board m.src = some ⟨p.turn, k⟩ ∧ Reaches k p.turn p.board m.src m.dst ∧
    p.board.colorAt m.dst ≠ some p.turn ∧ m.promo = none

/-- Whether `m` is a piece move is decided by reading the position. -/
instance PieceMove.decidable (p : Position) (m : Move) : Decidable (PieceMove p m) := by
  unfold PieceMove; infer_instance

/-- A pawn of the side to move goes one square straight forward to an empty square, and promotes
exactly when that square is on the last rank (FIDE 3.7.1, 3.7.3.3). -/
def PushMove (p : Position) (m : Move) : Prop :=
  p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.src.offset 0 p.turn.forward = some m.dst ∧
    p.board m.dst = none ∧ m.PromotionRule p.turn

/-- Whether `m` is a push is decided by reading the position. -/
instance PushMove.decidable (p : Position) (m : Move) : Decidable (PushMove p m) := by
  unfold PushMove; infer_instance

/-- A pawn of the side to move on its second rank (`relRank p.turn = 1`, counting from 0) goes two
squares straight forward; the square it passes over and the square it lands on are both empty; no
promotion choice (FIDE 3.7.2). -/
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
target, which is empty and lies on its sixth rank (`relRank p.turn = 5`, counting from 0); a pawn
of the other colour stands on the square beside the capturing pawn on the target's file (the victim
square); the square that pawn would have come from, one square further forward than the target
from the capturer's side, is empty; no promotion choice (FIDE 3.7.3.1–3.7.3.2). -/
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
    ¬ InCheck p ∧ ¬ p.board.AttackedBy p.turn.other (rookCastleSquare p.turn w)

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
its own king is attacked afterwards: it is a piece move, a push, a double push, a pawn capture, an
en passant capture, or castling to some wing. -/
def PseudoLegal (p : Position) (m : Move) : Prop :=
  PieceMove p m ∨ PushMove p m ∨ DoublePushMove p m ∨ PawnCaptureMove p m ∨ EnPassantMove p m ∨
    ∃ w, CastleMove p w m

/-- Whether `m` is pseudo-legal is decided rule by rule. -/
instance PseudoLegal.decidable (p : Position) (m : Move) : Decidable (PseudoLegal p m) := by
  unfold PseudoLegal; infer_instance

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

/-- The side to move is checkmated: it is in check and has no legal move (FIDE 1.4 and 1.4.1;
FIDE 5.1.1 makes it a win for the other side). -/
def Checkmate (p : Position) : Prop := InCheck p ∧ ∀ m, ¬ Legal p m

/-- Checkmate is decided by checking every candidate move. -/
instance Checkmate.decidable (p : Position) : Decidable (Checkmate p) := by
  unfold Checkmate; infer_instance

/-- The side to move is stalemated: it is not in check and has no legal move (FIDE 5.2.1). -/
def Stalemate (p : Position) : Prop := ¬ InCheck p ∧ ∀ m, ¬ Legal p m

/-- Stalemate is decided by checking every candidate move. -/
instance Stalemate.decidable (p : Position) : Decidable (Stalemate p) := by
  unfold Stalemate; infer_instance

/-! ## Tests

The tests of this module, with its named test positions, are in `ChessTest/Rules.lean`
(`lake build ChessTest`). The checks below stay here as documentation; they are cheap. -/

-- The initial position: no check; e2e4 is legal, e2e5 is not; after e2e4 the target is e3.
#guard !decide (InCheck Position.initial)
#guard decide (Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩)   -- e2e4
#guard !decide (Legal Position.initial ⟨⟨4, 1⟩, ⟨4, 4⟩, none⟩)  -- e2e5
#guard (Position.initial.play ⟨⟨4, 1⟩, ⟨4, 3⟩, none⟩).epTarget == some ⟨4, 2⟩

end Chess
