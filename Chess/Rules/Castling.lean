import Chess.Rules.Laws

/-!
# Rules: the castling landing square

L4.11, FIDE 3.8.2.2 read literally: castling is legal exactly when the square the king lands on is
not attacked in the position before the move. `Legal` tests that square after the move; this file
proves that the two readings agree, on every board, with no one-king hypothesis. Not trusted.
Specification: `docs/spec/Rules.md` §7a.

## Main statements

* `CastleMove.legal_iff`: the statement above.
* `CastleMove.play_board_of_ne`, `CastleMove.play_board_kingHome`,
  `CastleMove.play_board_kingCastleSquare`, `CastleMove.play_board_rookCastleSquare`: what
  castling leaves on the board.

## Implementation notes

* Each direction is a `private` lemma (`CastleMove.play_attacked`,
  `CastleMove.attacked_of_play_attacked`): an attacker's line is clear on one board exactly when
  it is clear on the other (`reaches_of_clear`), by arithmetic on lines along the home rank
  (`Square.shift_one_of_between`, `Chess.Basic`).
-/

namespace Chess

/-! ## The castling landing square (L4.11) -/

section Castling

variable {p : Position} {m : Move} {w : Wing} {t : Square}

/-- Castling is pseudo-legal. -/
theorem CastleMove.pseudoLegal (h : CastleMove p w m) : PseudoLegal p m :=
  .inr (.inr (.inr (.inr (.inr ⟨w, h⟩))))

/-- A side that may castle is not in check. -/
theorem Position.CanCastle.not_inCheck (h : p.CanCastle w) : ¬ InCheck p :=
  h.2.2.2.1

/-- After castling to wing `w`, every square other than the king's and the rook's home squares
and the squares they land on holds what it held before. -/
theorem CastleMove.play_board_of_ne (h : CastleMove p w m) (hK : t ≠ kingHome p.turn)
    (hG : t ≠ kingCastleSquare p.turn w) (hR : t ≠ rookHome p.turn w)
    (hF : t ≠ rookCastleSquare p.turn w) : (p.play m).board t = p.board t := by
  refine play_board_of_not_mem fun ht => ?_
  rcases Move.mem_touched.mp ht with e | e | ⟨he, -⟩ | ⟨w', hw', e | e⟩
  · exact hK (e.trans h.1.1)
  · exact hG (e.trans h.1.2.2)
  · exact he.not_isCastle w h.1
  · exact hR (hw'.wing_eq h.1 ▸ e)
  · exact hF (hw'.wing_eq h.1 ▸ e)

/-- After castling the king's home square is empty. -/
theorem CastleMove.play_board_kingHome (h : CastleMove p w m) :
    (p.play m).board (kingHome p.turn) = none :=
  h.1.1 ▸ play_board_src h.pseudoLegal

/-- After castling to wing `w` the king stands on its castling square. -/
theorem CastleMove.play_board_kingCastleSquare (h : CastleMove p w m) :
    (p.play m).board (kingCastleSquare p.turn w) = some ⟨p.turn, .king⟩ := by
  have hpl := h.pseudoLegal
  obtain ⟨⟨-, hk, hdst⟩, -, hpromo⟩ := h
  rw [← hdst, play_board_dst hpl, hk, hpromo]
  rfl

/-- After castling to wing `w` the rook stands on the square the king crossed. -/
theorem CastleMove.play_board_rookCastleSquare (h : CastleMove p w m) :
    (p.play m).board (rookCastleSquare p.turn w) = some ⟨p.turn, .rook⟩ := by
  obtain ⟨hc, ⟨-, hrook, -⟩, -⟩ := h
  rw [Chess.play_board_rookCastleSquare hc, hrook]

/-- If after castling a square holds a king of the side that castled and is attacked by the other
colour, it was attacked by the other colour before the move. -/
private theorem CastleMove.attacked_of_play_attacked (h : CastleMove p w m)
    (ht : (p.play m).board t = some ⟨p.turn, .king⟩)
    (ha : (p.play m).board.AttackedBy p.turn.other t) : p.board.AttackedBy p.turn.other t := by
  have hK := h.play_board_kingHome
  have hG := h.play_board_kingCastleSquare
  have hR := play_board_rookHome h.1
  have hF := h.play_board_rookCastleSquare
  obtain ⟨s, k, hs, hr⟩ := Board.attackedBy_iff.mp ha
  -- The attacker has the other colour, so it stands on none of the four squares castling writes.
  have hsb : p.board s = (p.play m).board s := by
    refine (h.play_board_of_ne ?_ ?_ ?_ ?_).symm <;> rintro rfl <;> simp_all
  refine Board.attackedBy_iff.mpr ⟨s, k, hsb ▸ hs, reaches_of_clear ?_ hr⟩
  intro d i j u hj0 hj hst hsu hb
  have hu : (p.play m).board u = none := by simpa [hsu] using hb j hj hj0
  by_cases huK : u = kingHome p.turn
  · -- A line through the king's home square, strictly inside it, runs along the home rank; the
    -- crossed square, where the rook now stands, is then an end of the line or strictly inside.
    subst huK
    have hdr := Square.dr_eq_zero_of_between hj0 hj hsu hst p.turn.homeRank_eq_zero_or_seven
    have he := Direction.eq_or_eq_opposite_of_dr_eq_zero hdr
      (by cases w <;> rfl : w.direction.dr = 0)
    rcases Square.shift_one_of_between hj0 hj hsu hst he (shift_kingHome_one p.turn w) with
      e | e | ⟨j', hj'0, hj', e⟩
    · rw [← e, hF] at hs
      simp at hs
    · rw [← e, hF] at ht
      simp at ht
    · have := hb j' hj' hj'0
      simp [e, hF] at this
  by_cases huR : u = rookHome p.turn w
  · -- The rook's home square is a corner: no line runs through it.
    subst huR
    have hdr := Square.dr_eq_zero_of_between hj0 hj hsu hst p.turn.homeRank_eq_zero_or_seven
    have hdf := Square.df_eq_zero_of_between hj0 hj hsu hst
      (by cases w <;> simp [rookHome, Wing.rookFile])
    exact absurd hdr (d.df_ne_zero_or_dr_ne_zero.resolve_left (· hdf))
  have huG : u ≠ kingCastleSquare p.turn w := by rintro rfl; simp [hG] at hu
  have huF : u ≠ rookCastleSquare p.turn w := by rintro rfl; simp [hF] at hu
  rwa [h.play_board_of_ne huK huG huR huF] at hu

/-- If the king's castling square is attacked by the other colour before castling, it is attacked
after. -/
private theorem CastleMove.play_attacked (h : CastleMove p w m)
    (ha : p.board.AttackedBy p.turn.other (kingCastleSquare p.turn w)) :
    (p.play m).board.AttackedBy p.turn.other (kingCastleSquare p.turn w) := by
  -- Before the move the king and the rook are at home and the squares between them are empty.
  have hK : p.board (kingHome p.turn) = some ⟨p.turn, .king⟩ := h.1.1 ▸ h.1.2.1
  have hR : p.board (rookHome p.turn w) = some ⟨p.turn, .rook⟩ := h.2.1.2.1
  have hbetween : ∀ s ∈ betweenKingAndRook p.turn w, p.board s = none := h.2.1.2.2.1
  have hF := hbetween _ (rookCastleSquare_mem_between p.turn w)
  have hG := hbetween _ (kingCastleSquare_mem_between p.turn w)
  obtain ⟨s, k, hs, hr⟩ := Board.attackedBy_iff.mp ha
  -- The attacker has the other colour, so it stands on none of the four squares castling writes.
  have hsb : (p.play m).board s = p.board s := by
    refine h.play_board_of_ne ?_ ?_ ?_ ?_ <;> rintro rfl <;> simp_all
  refine Board.attackedBy_iff.mpr ⟨s, k, hsb ▸ hs, reaches_of_clear ?_ hr⟩
  intro d i j u hj0 hj hst hsu hb
  have hu : p.board u = none := by simpa [hsu] using hb j hj hj0
  by_cases huF : u = rookCastleSquare p.turn w
  · -- A line through the crossed square, strictly inside it, runs along the home rank; the king's
    -- home square, where the king stood, is then an end of the line or strictly inside.
    subst huF
    have hdr := Square.dr_eq_zero_of_between hj0 hj hsu hst p.turn.homeRank_eq_zero_or_seven
    have he := Direction.eq_or_eq_opposite_of_dr_eq_zero hdr
      (by cases w <;> rfl : w.direction.opposite.dr = 0)
    have hv := Square.shift_eq_some_iff_opposite.mp (shift_kingHome_one p.turn w)
    rcases Square.shift_one_of_between hj0 hj hsu hst he hv with e | e | ⟨j', hj'0, hj', e⟩
    · rw [← e, hK] at hs
      simp at hs
    · exact absurd e.symm (kingCastleSquare_ne_kingHome _ _ _)
    · have := hb j' hj' hj'0
      simp [e, hK] at this
  have huK : u ≠ kingHome p.turn := by rintro rfl; simp [hK] at hu
  have huR : u ≠ rookHome p.turn w := by rintro rfl; simp [hR] at hu
  have huG : u ≠ kingCastleSquare p.turn w := by
    rintro rfl
    exact Nat.ne_of_lt hj (Square.steps_eq_of_shift_eq hsu hst)
  rwa [h.play_board_of_ne huK huG huR huF]

/-- A castling move is legal exactly when the square the king lands on is not attacked by the
other colour in the position before the move (FIDE 3.8.2.2, read literally). -/
theorem CastleMove.legal_iff (h : CastleMove p w m) :
    Legal p m ↔ ¬ p.board.AttackedBy p.turn.other (kingCastleSquare p.turn w) := by
  refine ⟨fun hl ha => hl.2 ⟨_, h.play_board_kingCastleSquare, h.play_attacked ha⟩,
    fun ha => ⟨h.pseudoLegal, fun ⟨t, ht, hat⟩ => ?_⟩⟩
  have hb := h.attacked_of_play_attacked ht hat
  by_cases hG : t = kingCastleSquare p.turn w
  · exact ha (hG ▸ hb)
  · -- Any other king of the side that castled stood on its square before the move, and was
    -- attacked there: the side to move was in check, which castling excludes.
    refine h.2.1.not_inCheck ⟨t, ?_, hb⟩
    rw [← h.play_board_of_ne ?_ hG ?_ ?_, ht] <;> rintro rfl
    · simp [h.play_board_kingHome] at ht
    · simp [play_board_rookHome h.1] at ht
    · simp [h.play_board_rookCastleSquare] at ht

end Castling

end Chess
