import Chess.Rules.Defs

/-!
# Rules: laws

What follows from the definitions of `Chess.Rules.Defs`: what reaching reads, attack symmetry,
what each shape and rule implies, what a move changes on the board and in the castling rights,
the colour of a bishop's or knight's landing square, promotion, and the terminal positions. None of
it is trusted. Specification: `docs/spec/Rules.md`, the lemma tables of §1–§9.

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
  attack symmetry needs; `reaches_set_src`, `reaches_set_dst`, `slides_symm`; `reaches_of_clear`,
  its one-way form for boards that differ between the two squares.
* (R3) `reaches_symm`, `reaches_pawn_symm`: a piece on `s` reaches `t` exactly when one on `t`
  reaches `s` (for a pawn, one of the other colour); hence `Board.attackedBy_iff_superpiece`, the
  super-piece test, which looks from the attacked square outward.
* `Board.attackedBy_iff`: an attacked square is one some piece of that colour reaches, the form the
  attack theorems use.
* Bridges between `play` and the rules: `PseudoLegal.isEnPassant_iff`, `PseudoLegal.isCastle_iff`
  and `PseudoLegal.isDoublePush_iff` (among pseudo-legal moves each shape is exactly its rule);
  `PseudoLegal.attacksFrom_dst` (a move onto a piece is an attack on it);
  `PseudoLegal.touched_nodup` (no square is written twice).

## Implementation notes

* After `cases k` on a `Kind`, goals come in constructor order (pawn, knight, bishop, rook, queen,
  king); proofs name them with `case`.
* General facts about squares, colours and castling squares live in `Chess.Basic`, and facts
  about castling rights in `Chess.Position`; only `PseudoLegal.not_mem_rest`, which serves one
  proof here, is `private`.
-/

namespace Chess

/-! ## Board helpers -/

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

/-- Whatever reaches `t` from `s` on `b` reaches it on `b'`, provided that every line from `s` to
`t` that is clear on `b` is clear on `b'`: whenever `t` is `i` steps from `s` in some direction
`d` and every square strictly between is empty on `b`, every square strictly between is empty on
`b'`. -/
theorem reaches_of_clear
    (h : ∀ d i j u, 0 < j → j < i → s.shift d i = some t → s.shift d j = some u →
      (∀ j' < i, 0 < j' → (s.shift d j').bind b = none) → b' u = none) :
    Reaches k c b s t → Reaches k c b' s t := by
  cases k
  case pawn | knight | king => exact id
  all_goals
    rintro ⟨d, hd, i, hi8, hi, ht, hb⟩
    refine ⟨d, hd, i, hi8, hi, ht, fun j hj hj0 => ?_⟩
    cases hu : s.shift d j with
    | none => rfl
    | some u => exact h d i j u hj0 hj ht hu hb

/-- If `s` holds `pc`, the piece on `s` attacks `t` exactly when `pc` reaches `t` from `s`. -/
theorem attacksFrom_of_eq_some (h : b s = some pc) :
    b.AttacksFrom s t ↔ Reaches pc.kind pc.color b s t := by
  simp [Board.AttacksFrom, h]

/-- An empty square attacks nothing. -/
theorem not_attacksFrom_of_eq_none (h : b s = none) : ¬ b.AttacksFrom s t := by
  simp [Board.AttacksFrom, h]

/-- Square `t` is attacked by colour `c` exactly when some square holds a piece of colour `c` and
some kind `k` that reaches `t`. -/
theorem Board.attackedBy_iff :
    b.AttackedBy c t ↔ ∃ s k, b s = some ⟨c, k⟩ ∧ Reaches k c b s t := by
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

/-- **(R3.1) For every kind but the pawn, reaching is symmetric: a piece of kind `k` on `s` reaches
`t` exactly when one on `t` reaches `s`.** -/
theorem reaches_symm (hk : k ≠ .pawn) : Reaches k c b s t ↔ Reaches k c b t s := by
  -- One direction suffices: it holds for every pair of squares, so it also gives the converse.
  suffices h : ∀ {s t}, Reaches k c b s t → Reaches k c b t s from ⟨h, h⟩
  intro s t h
  cases k
  case pawn => exact absurd rfl hk
  case knight =>
    obtain ⟨j, hj, h⟩ := h
    exact ⟨(-j.1, -j.2), neg_mem_knightJumps hj, Square.offset_eq_some_iff_neg.mp h⟩
  case king =>
    obtain ⟨d, h⟩ := h
    exact ⟨d.opposite, Square.shift_eq_some_iff_opposite.mp h⟩
  all_goals
    obtain ⟨d, hd, h⟩ := h
    exact ⟨d.opposite, Kind.opposite_mem_slideDirections.mpr hd, h.symm⟩

/-- **(R3.2) A pawn of colour `c` on `s` reaches `t` exactly when a pawn of the other colour on
`t` reaches `s`.** -/
theorem reaches_pawn_symm : Reaches .pawn c b s t ↔ Reaches .pawn c.other b t s := by
  simp only [reaches_pawn, Color.forward_other, Square.offset_eq_some_iff_neg (s := s),
    Int.reduceNeg, Int.neg_neg]
  exact or_comm

/-- **(R3.3, the super-piece test) Square `t` is attacked by colour `c` exactly when, for some
kind `k`, a piece of kind `k` and colour `c.other` standing on `t` would reach a square holding a
piece of kind `k` and colour `c`.** -/
theorem Board.attackedBy_iff_superpiece :
    b.AttackedBy c t ↔ ∃ k s, b s = some ⟨c, k⟩ ∧ Reaches k c.other b t s := by
  rw [Board.attackedBy_iff, exists_comm]
  refine exists_congr fun k => exists_congr fun s => and_congr_right fun _ => ?_
  by_cases hk : k = .pawn
  · subst hk; exact reaches_pawn_symm
  · -- Only a pawn's reach depends on its colour.
    rw [reaches_symm hk]
    cases k <;> first | exact absurd rfl hk | exact Iff.rfl

end Reaching

/-! ## Shapes of moves -/

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

section Movement

variable {p : Position} {m : Move} {k : Kind} {w : Wing}

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

/-- A pseudo-legal move of a piece that is neither a pawn nor a king is a piece move. -/
theorem PseudoLegal.pieceMove_of_kindAt (h : PseudoLegal p m) (hk : p.board.kindAt m.src = some k)
    (hp : k ≠ .pawn) (hking : k ≠ .king) : PieceMove p m := by
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
  obtain ⟨k, -, hsrc, hr, -⟩ := h.pieceMove_of_kindAt hb (by decide) (by decide)
  obtain rfl : k = .bishop := by simpa [Board.kindAt, hsrc] using hb
  obtain ⟨d, hd, i, -, -, hi, -⟩ := hr
  exact Square.isLight_shift_of_mem_diagonals hd hi

/-- (R5) A pseudo-legal knight move lands on a square of the other shade. -/
theorem PseudoLegal.isLight_dst_iff_of_knight (h : PseudoLegal p m)
    (hn : p.board.kindAt m.src = some .knight) : m.dst.IsLight ↔ ¬ m.src.IsLight := by
  obtain ⟨k, -, hsrc, hr, -⟩ := h.pieceMove_of_kindAt hn (by decide) (by decide)
  obtain rfl : k = .knight := by simpa [Board.kindAt, hsrc] using hn
  obtain ⟨j, hj, hjt⟩ := hr
  exact Square.isLight_iff_of_mem_knightJumps hj hjt

/-- A pseudo-legal move names a promotion choice exactly when a pawn reaches the last rank. -/
theorem PseudoLegal.promo_ne_none_iff (h : PseudoLegal p m) :
    m.promo ≠ none ↔ p.board m.src = some ⟨p.turn, .pawn⟩ ∧ m.dst.relRank p.turn = 7 := by
  rcases h with ⟨k, hk, hs, -, -, hpr⟩ | ⟨hs, -, -, hpr⟩ | ⟨⟨hs, ho⟩, h1, -, -, hpr⟩ |
    ⟨hs, -, -, hpr⟩ | ⟨-, -, h5, -, -, hpr⟩ | ⟨w, ⟨-, hs, -⟩, -, hpr⟩
  · -- A piece move names no choice, and its piece is not a pawn.
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

end Chess
