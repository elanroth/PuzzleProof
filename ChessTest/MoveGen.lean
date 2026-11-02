import Chess.MoveGen
import ChessTest.Rules

/-!
# Tests of `Chess.MoveGen`

The tests of `Chess.MoveGen`, moved out of the library module so that a library build does not pay
for them (`lake build ChessTest`). Specification: `docs/spec/MoveGen.md` §6; the two positions
carry the docstrings given there. The six standard perft positions are in `ChessTest.Perft`.

## Main definitions

* `epCheckPos`, `promoKnightPos`: the two bug-class positions of DESIGN §8.4 that are not already
  test positions of `Chess.Rules` (en passant out of check, and castling after a promotion capture
  on a rook's home square).

## Implementation notes

* Kernel checks are `decide +kernel`; the `#guard`s are interpreted. No `native_decide`.
-/

namespace Chess

/-- The position after d7d5 from: White king e4 and pawn e5, Black king a8 and pawn d7, Black to
move, no castling rights. So: White to move, in check from the pawn on d5, en passant target d6,
no rights. -/
def epCheckPos : Position :=
  (⟨Board.empty
      |>.set ⟨4, 3⟩ (some ⟨.white, .king⟩)  -- e4
      |>.set ⟨4, 4⟩ (some ⟨.white, .pawn⟩)  -- e5
      |>.set ⟨0, 7⟩ (some ⟨.black, .king⟩)  -- a8
      |>.set ⟨3, 6⟩ (some ⟨.black, .pawn⟩), -- d7
    .black, CastlingRights.none, none⟩ : Position).play
    ⟨⟨3, 6⟩, ⟨3, 4⟩, none⟩  -- d7d5

/-- `promoPos` after b7a8=N: White's pawn has captured Black's a8 rook and become a knight; Black
to move, Black's kingside right only. -/
def promoKnightPos : Position := promoPos.play ⟨⟨1, 6⟩, ⟨0, 7⟩, some .knight⟩  -- b7a8=N

-- The two positions are what their docstrings say ("So: …").
#guard epCheckPos.turn == .white && decide (InCheck epCheckPos) &&
  epCheckPos.epTarget == some ⟨3, 5⟩ &&  -- d6
  epCheckPos.castling.letters == "-"
#guard promoKnightPos.turn == .black && promoKnightPos.castling.letters == "k"

-- The initial position: 20 legal moves, 400 after two plies.
example : (legalMoves Position.initial).length = 20 := by decide +kernel
#guard perft 2 Position.initial == 400
#guard ((perftDivide 1 Position.initial).map (·.2)).sum == 400

-- Fool's mate, through the generator: no listed move, so checkmate (decided by `checkmate_iff`).
example : legalMoves foolsMate = [] := by decide +kernel
example : Checkmate foolsMate := by decide +kernel
example : ¬ Stalemate foolsMate := by decide +kernel

-- The empty board: the castling rights alone propose nothing.
#guard (candidates ⟨Board.empty, .white, CastlingRights.full, none⟩).isEmpty

-- Agreement with `Legal`: every legal move listed, none twice.
#guard agreesWithLegal Position.initial
#guard agreesWithLegal foolsMate
#guard agreesWithLegal castlePos
#guard agreesWithLegal blackCastlePos
#guard agreesWithLegal (castleRookPos 3)  -- Black rook d7
#guard agreesWithLegal (castleRookPos 4)  -- Black rook e7, White in check
#guard agreesWithLegal epPos
#guard agreesWithLegal epPinPos
#guard agreesWithLegal kingsPos
#guard agreesWithLegal promoPos
#guard agreesWithLegal blackPromoPos
#guard agreesWithLegal pinPos
#guard agreesWithLegal blackEpPos
#guard agreesWithLegal rookAttackedPos
#guard agreesWithLegal defendedPos
#guard agreesWithLegal epCheckPos
#guard agreesWithLegal promoKnightPos

-- Agreement as a theorem: on `kingsPos`, the generator lists exactly the legal moves (M4 there).
example : ∀ m, m ∈ legalMoves kingsPos ↔ Legal kingsPos m :=
  fun _ => mem_legalMoves_of_agreesWithLegal (by decide +kernel)

-- Regression counts, cross-checked by the agreement tests.
#guard [Position.initial, foolsMate, castlePos, blackCastlePos, castleRookPos 3, castleRookPos 4,
  epPos, epPinPos, kingsPos, promoPos, blackPromoPos, pinPos, blackEpPos, rookAttackedPos,
  defendedPos, epCheckPos, promoKnightPos].map (fun p => (legalMoves p).length) ==
  [20, 0, 23, 15, 23, 4, 7, 4, 2, 13, 9, 4, 7, 15, 2, 8, 15]

-- En passant out of check: e5d6 is legal only because it removes the checking pawn.
example : (⟨⟨4, 4⟩, ⟨3, 5⟩, none⟩ : Move) ∈ legalMoves epCheckPos := by decide +kernel
-- Castling after a rook capture with promotion: O-O, but no O-O-O.
example : Move.castle .black .kingside ∈ legalMoves promoKnightPos := by decide +kernel
example : Move.castle .black .queenside ∉ legalMoves promoKnightPos := by decide +kernel
-- Castling through an attacked square: O-O-O, but no O-O (f1 attacked).
example : Move.castle .white .queenside ∈ legalMoves castlePos := by decide +kernel
example : Move.castle .white .kingside ∉ legalMoves castlePos := by decide +kernel
-- A pin: Be2d3 is not listed.
example : (⟨⟨4, 1⟩, ⟨3, 2⟩, none⟩ : Move) ∉ legalMoves pinPos := by decide +kernel

end Chess
