import Chess.Rules

/-!
# Tests of `Chess.Rules`

The tests of `Chess.Rules`, moved out of the library module so that a library build does not pay
for them (`lake build ChessTest`). Specification: `docs/spec/Rules.md` §10; the named positions
carry the docstrings given there.

## Main definitions

* `foolsMate`, `castlePos`, `blackCastlePos`, `castleRookPos`, `epPos`, `epPinPos`, `kingsPos`,
  `promoPos`, `blackPromoPos`, `pinPos`, `blackEpPos`, `rookAttackedPos`, `defendedPos`: the named
  test positions, also used by the tests of `Chess.MoveGen` and `Chess.ChessGame`.

## Implementation notes

* Every check here is a `decide` or `decide +kernel` example or an interpreted `#guard`. No
  `native_decide`.
-/

namespace Chess

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
-- The same two answers through L4.11: FIDE's literal test, g1 attacked before the move or not.
example : Legal rookAttackedPos ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ :=
  (CastleMove.legal_iff (w := .kingside) (by decide)).mpr (by decide)
example : ¬ Legal { rookAttackedPos with
    board := rookAttackedPos.board.set ⟨6, 7⟩ (some ⟨.black, .rook⟩) }
    ⟨⟨4, 0⟩, ⟨6, 0⟩, none⟩ :=
  fun h => (CastleMove.legal_iff (w := .kingside) (by decide)).mp h (by decide)

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
