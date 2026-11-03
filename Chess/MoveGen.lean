import Chess.Rules

/-!
# MoveGen

An executable move generator, built so that it can be read against the rules of `Chess.Rules`.
The generator **proposes and the rules dispose**: geometry alone proposes candidate moves for each
piece of the side to move, and the generator keeps the candidates that `PseudoLegal` allows and
after which no king of the mover's colour is attacked. Specification: `docs/spec/MoveGen.md`;
every definition below carries the docstring given there.

## Main definitions

* `slideTargets`, `reachTargets`: the list forms of `Slides` and `Reaches` (with the list operation
  `Board.upToBlocker`).
* `candidates`, built from `pawnTargets`, `pawnMovesTo`, `Move.castle`, `candidatesFrom` and
  `castleCandidates`: the moves proposed by geometry alone.
* `pseudoMoves`, `legalMoves`: the candidates filtered by `PseudoLegal`, then by king safety,
  tested by `kingSafeAfter` (with Position's `Board.squaresOf` and the super-piece test
  `Board.superpieceAttackedBy`).
* `perft`, `perftDivide`: the standard move-path counts, for comparison with other programs.
* `LegalLine`, `lines`: sequences of moves each legal where it is played, and the list of them.
* `legalMovesBySpec`, `agreesWithLegal`: the legal moves found from the specification alone, and a
  test that the generator agrees with them; since M4 and M5 a computed cross-check only.

## Main statements

* (M1) `mem_slideTargets`, `mem_reachTargets`: the target lists list exactly the squares that
  `Slides` and `Reaches` describe.
* (M4, soundness) `legalMoves_eq_filter`: `legalMoves p` is `candidates p` filtered by `Legal`;
  hence `legalMoves_sound`: every entry of `legalMoves p` is legal.
* `Board.superpieceAttackedBy_iff`, `kingSafeAfter_iff`: the king-safety test is `Legal`'s second
  conjunct on every pseudo-legal move (from Rules' R3 and M1).
* (the cover) `PseudoLegal.mem_candidates`: every pseudo-legal move is a candidate.
* (M2, M4) `mem_pseudoMoves`, `mem_legalMoves`: the generator lists exactly the pseudo-legal and
  the legal moves.
* (M6) `checkmate_iff`, `stalemate_iff`: checkmate and stalemate read off the generator; through
  them `Checkmate` and `Stalemate` get their cheap decisions.
* `candidates_ignores_epTarget`: the candidates do not read the en passant target.
* `perft_one`, `sum_perftDivide`: perft of depth 1 counts `legalMoves`, and the divide adds up to
  perft of one more ply.
* (M8) `mem_lines`, `lines_nodup`, `perft_eq_length_lines`: `lines n p` lists exactly the legal
  lines of `n` moves from `p` (`LegalLine`), none twice, and `perft n p` is their number;
  `perft_eq_length_of_mem_iff`: so is the length of any list of them without repeats.
* (M5) `legalMoves_nodup`: `legalMoves` lists no move twice, from `candidates_nodup` (moves from
  different squares differ; from one square the targets are distinct, by facts about the 64
  squares decided once by the kernel, such as `Square.not_mem_ray_of_mem_ray`).
* `nodup_legalMoves_of_agreesWithLegal`: M5 at one position from the test; superseded by
  `legalMoves_nodup`.

## Implementation notes

* Propose and dispose (spec design choice 1). The generator never decides a movement rule itself.
  Every other test it makes (the colour and kind of the piece on a square, empty squares and
  blockers, the edge of the board, the two guards of `castleCandidates`) only removes candidates,
  so none can add an illegal move: soundness is the one-line `legalMoves_sound`. Completeness needs
  only that no such test removes a pseudo-legal move: that is the cover.
* The castling candidates need a king of the side to move on its home square (design choice 5):
  without it a queen on e1 with a castling right held would propose e1g1 twice, and `legalMoves`
  would list it twice.
* Move order is deterministic but not part of any contract (design choice 6): every theorem meant
  for clients is about membership.
* `pseudoMoves` and `legalMoves` capture the `Decidable` instances of `Chess.Rules` when they are
  elaborated; a faster instance declared later does not change them. A speed-up goes either into
  Rules' instances or into this module as its own Boolean test proved equal to the Rules predicate
  (design choice 10). King safety took the second way: `kingSafeAfter` looks from the squares
  where the mover's king can stand outward, and lists the kings of the position before the move,
  which, by the timings, the kernel appears to evaluate once per position instead of once per move
  (the mechanism was not checked against the kernel's code).
* The candidates read the board, the side to move and the castling rights, never the en passant
  target (design choice 13, `candidates_ignores_epTarget`).
* Completeness (M4: every legal move is listed) goes through one geometric cover lemma,
  `PseudoLegal.mem_candidates`: a case split over the six rules with no reasoning about checks,
  pins or blockers. Nothing in this module is trusted: `legalMoves` lists exactly the legal moves.
  That it lists none twice is proved too (M5, `legalMoves_nodup`, 2026-11-03).
-/

namespace Chess

/-! ## Targets -/

/-- The squares of the list, in order, up to and including the first one that is occupied on `b`;
the whole list if every square of it is empty on `b`. -/
def Board.upToBlocker (b : Board) : List Square → List Square
  | [] => []
  | t :: ts =>
    match b t with
    | none   => t :: b.upToBlocker ts
    | some _ => [t]

/-- The squares a piece sliding from `s` in direction `d` reaches on `b`, nearest first: the
squares 1, 2, … steps from `s` in direction `d` as far as the edge of the board (`s` itself
excluded), up to and including the first occupied one, or all of them if none is occupied. Empty
if the step from `s` leaves the board. -/
def slideTargets (d : Direction) (b : Board) (s : Square) : List Square :=
  b.upToBlocker (s.ray d)

/-- The squares a piece of kind `k` and colour `c` would reach from `s` on `b`, whatever stands on
`s`, as a list (the list form of `Reaches`): for a pawn the squares diagonally forward, for a
knight the squares a knight's jump away, for a king the adjacent squares, and for a bishop, rook or
queen the squares along each of its directions up to and including the first occupied one. Jumps
and steps that would leave the board give no square. -/
def reachTargets (k : Kind) (c : Color) (b : Board) (s : Square) : List Square :=
  match k with
  | .pawn   => [s.offset (-1) c.forward, s.offset 1 c.forward].filterMap id
  | .knight => knightJumps.filterMap fun j => s.offset j.1 j.2
  | .king   => Direction.all.filterMap fun d => s.shift d 1
  | .bishop | .rook | .queen => k.slideDirections.flatMap fun d => slideTargets d b s

section Targets

variable {b : Board} {l : List Square} {s t : Square} {d : Direction} {k : Kind} {c : Color}

/-- `t` is listed by `b.upToBlocker l` exactly when, for some `i`, `t` is entry `i` of `l` and
every entry before `i` is empty on `b`. -/
theorem Board.mem_upToBlocker :
    t ∈ b.upToBlocker l ↔ ∃ i : Nat, l[i]? = some t ∧ ∀ j < i, l[j]?.bind b = none := by
  induction l with
  | nil => simp [Board.upToBlocker]
  | cons u l ih =>
    unfold Board.upToBlocker
    split
    · next hu =>
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, hi, hj⟩)
        · exact ⟨0, rfl, by simp⟩
        · refine ⟨i + 1, by simpa using hi, fun j hj' => ?_⟩
          cases j with
          | zero => simpa using hu
          | succ j => simpa using hj j (by omega)
      · rintro ⟨i, hi, hj⟩
        cases i with
        | zero => left; simpa using hi.symm
        | succ i =>
          right
          exact ⟨i, by simpa using hi, fun j hj' => by simpa using hj (j + 1) (by omega)⟩
    · next pc hu =>
      rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨0, rfl, by simp⟩
      · rintro ⟨i, hi, hj⟩
        cases i with
        | zero => simpa using hi.symm
        | succ i => simpa [hu] using hj 0 (by omega)

/-- **The squares listed by `slideTargets d b s` are exactly those a piece sliding from `s` in
direction `d` reaches on `b`.** -/
theorem mem_slideTargets : t ∈ slideTargets d b s ↔ Slides d b s t := by
  rw [slideTargets, Board.mem_upToBlocker, slides_iff]
  simp only [Square.getElem?_ray]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨i + 1, by omega, hi, fun j hj1 hj0 => ?_⟩
    cases j with
    | zero => omega
    | succ j => exact hj j (by omega)
  · rintro ⟨_ | i, hi0, hi, hj⟩
    · omega
    · exact ⟨i, hi, fun j hj' => hj (j + 1) (by omega) (by omega)⟩

/-- **The squares listed by `reachTargets k c b s` are exactly those a piece of kind `k` and colour
`c` reaches from `s` on `b`.** -/
theorem mem_reachTargets : t ∈ reachTargets k c b s ↔ Reaches k c b s t := by
  cases k
  case pawn =>
    simp only [reachTargets, Reaches, List.mem_filterMap, List.mem_cons, List.not_mem_nil, id]
    constructor
    · rintro ⟨o, (rfl | rfl | h), ho⟩ <;> simp_all
    · rintro (h | h) <;> exact ⟨_, by simp, h⟩
  case knight => simp [reachTargets, Reaches]
  case king => simp [reachTargets, Reaches, Direction.mem_all]
  all_goals simp [reachTargets, Reaches, mem_slideTargets]

end Targets

/-! ## Candidates -/

/-- The squares a pawn of colour `c` on `s` might move to, in this order: one square straight
forward, two squares straight forward, and the two squares diagonally forward, towards the a-file
first. Squares that would be off the board are left out. Which of them it may move to now is for
the pawn rules to say. -/
def pawnTargets (c : Color) (s : Square) : List Square :=
  [s.offset 0 c.forward, s.offset 0 (2 * c.forward), s.offset (-1) c.forward,
    s.offset 1 c.forward].filterMap id

/-- The moves of a pawn of colour `c` from `s` to `t`: one for each promotion choice (knight,
bishop, rook, queen) if `t` is on `c`'s last rank, otherwise the one move with no promotion
choice. -/
def pawnMovesTo (c : Color) (s t : Square) : List Move :=
  if t.relRank c = 7 then PromoKind.all.map fun pk => ⟨s, t, some pk⟩ else [⟨s, t, none⟩]

/-- The castling move of colour `c` to wing `w`, as data: the king from its home square to its
castling square on wing `w`, with no promotion choice (e1g1, e1c1, e8g8, e8c8). -/
def Move.castle (c : Color) (w : Wing) : Move := ⟨kingHome c, kingCastleSquare c w, none⟩

/-- The candidate moves from `s` in `p`, proposed by geometry alone. For a pawn of the side to
move on `s`: a move to each of its pawn targets, with every promotion choice when the target is on
the last rank. For any other piece of the side to move on `s`: a move with no promotion choice to
each square it reaches. None if `s` is empty or holds a piece of the side not to move. Castling
moves are not proposed here (`castleCandidates`). -/
def candidatesFrom (p : Position) (s : Square) : List Move :=
  match p.board s with
  | some ⟨c, k⟩ =>
    if c = p.turn then
      if k = .pawn then (pawnTargets p.turn s).flatMap (pawnMovesTo p.turn s)
      else (reachTargets k p.turn p.board s).map fun t => ⟨s, t, none⟩
    else []
  | none => []

/-- The candidate castling moves of `p`. If a king of the side to move stands on that colour's king
home square (e1 or e8): the move `Move.castle p.turn w` for each wing `w` on which the side to move
still holds the castling right, kingside first. Otherwise none. -/
def castleCandidates (p : Position) : List Move :=
  if p.board (kingHome p.turn) = some ⟨p.turn, .king⟩ then
    (Wing.all.filter (p.castling.get p.turn)).map (Move.castle p.turn)
  else []

/-- The candidate moves of `p`: the candidate moves from every square, in square order (a1, b1, …,
h8), then the candidate castling moves. Every pseudo-legal move of `p` is a candidate (the cover,
`PseudoLegal.mem_candidates`); in general some candidates are not pseudo-legal. -/
def candidates (p : Position) : List Move :=
  Square.all.flatMap (candidatesFrom p) ++ castleCandidates p

section Candidates

variable {c : Color} {s t : Square} {m : Move} {p : Position} {w : Wing}

/-- **A pawn move list holds exactly the moves from `s` to `t` that obey the promotion rule for
colour `c`.** -/
theorem mem_pawnMovesTo :
    m ∈ pawnMovesTo c s t ↔ m.src = s ∧ m.dst = t ∧ m.PromotionRule c := by
  rcases m with ⟨s', t', o⟩
  unfold pawnMovesTo Move.PromotionRule
  by_cases h : t.relRank c = 7 <;> cases o <;> simp [h, PromoKind.mem_all, eq_comm] <;>
    rintro rfl rfl <;> omega

/-- A castling to wing `w` is the castling move of the side to move to `w`. -/
theorem CastleMove.eq_castle (h : CastleMove p w m) : m = Move.castle p.turn w := by
  obtain ⟨⟨hs, -, hd⟩, -, hp⟩ := h
  cases m
  simp_all [Move.castle]

/-- The candidates do not read the en passant target: changing it leaves them unchanged. -/
theorem candidates_ignores_epTarget (e : Option Square) :
    candidates { p with epTarget := e } = candidates p := rfl

end Candidates

/-! ## The generator -/

/-- The pseudo-legal moves of `p`: the candidate moves that obey the movement rules
(`PseudoLegal`). -/
def pseudoMoves (p : Position) : List Move :=
  (candidates p).filter fun m => decide (PseudoLegal p m)

/-- Whether colour `c` attacks `t` on `b`, tested from `t` outward (the super-piece method): for
some kind `k`, one of the squares that a piece of kind `k` and colour `c.other` standing on `t`
would reach holds a piece of kind `k` and colour `c`. -/
def Board.superpieceAttackedBy (b : Board) (c : Color) (t : Square) : Bool :=
  Kind.all.any fun k => (reachTargets k c.other b t).any fun s => decide (b s = some ⟨c, k⟩)

/-- After move `m` in `p`, no king of the mover's colour is attacked. Only the squares where such a
king can stand after a pseudo-legal move are tested: the destination of `m`, and the squares that
held one in `p`. Each is tested by the super-piece method. -/
def kingSafeAfter (p : Position) (m : Move) : Bool :=
  !(m.dst :: p.board.squaresOf ⟨p.turn, .king⟩).any fun s =>
    decide ((p.play m).board s = some ⟨p.turn, .king⟩) &&
      (p.play m).board.superpieceAttackedBy p.turn.other s

/-- The legal moves of `p`: the entries of `pseudoMoves p` after which no king of the mover's
colour is attacked (FIDE 3.9.2). -/
def legalMoves (p : Position) : List Move :=
  (pseudoMoves p).filter (kingSafeAfter p)

section Generator

variable {p : Position} {m : Move}

/-- `m` is in `pseudoMoves p` exactly when it is a candidate of `p` and pseudo-legal in `p`. -/
theorem mem_pseudoMoves_iff_candidate :
    m ∈ pseudoMoves p ↔ m ∈ candidates p ∧ PseudoLegal p m := by
  simp [pseudoMoves]

/-- Every entry of `pseudoMoves p` is pseudo-legal in `p`. -/
theorem pseudoMoves_sound (h : m ∈ pseudoMoves p) : PseudoLegal p m :=
  (mem_pseudoMoves_iff_candidate.mp h).2

/-- **The super-piece test decides attack: `b.superpieceAttackedBy c t` is true exactly when `t` is
attacked by colour `c`.** -/
theorem Board.superpieceAttackedBy_iff {b : Board} {c : Color} {t : Square} :
    b.superpieceAttackedBy c t = true ↔ b.AttackedBy c t := by
  simp only [Board.superpieceAttackedBy, List.any_eq_true, decide_eq_true_eq, mem_reachTargets,
    Board.attackedBy_iff_superpiece]
  exact ⟨fun ⟨k, _, s, hr, hs⟩ => ⟨k, s, hs, hr⟩,
    fun ⟨k, s, hs, hr⟩ => ⟨k, Kind.mem_all k, s, hr, hs⟩⟩

/-- After a pseudo-legal move, a king of the mover's colour stands only on the move's destination
or on a square that held one before the move. -/
theorem PseudoLegal.eq_dst_or_of_play_board_eq_king {s : Square} (h : PseudoLegal p m)
    (hs : (p.play m).board s = some ⟨p.turn, .king⟩) :
    s = m.dst ∨ p.board s = some ⟨p.turn, .king⟩ := by
  rcases Board.setMany_eq_or_mem p.board (m.boardWrites p) s with e | hw
  · exact .inr (hs ▸ e.symm)
  rw [← play_board, hs] at hw
  simp only [Move.boardWrites, List.mem_append] at hw
  rcases hw with (hw | hw) | hw
  · -- The piece moves: the source is emptied, so a king can only arrive on the destination.
    simp only [Move.pieceWrites, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hw
    rcases hw with ⟨-, h0⟩ | ⟨rfl, -⟩
    · cases h0
    · exact .inl rfl
  · -- En passant writes only an empty square.
    by_cases he : m.IsEnPassant p
    · simp [Move.enPassantWrites_of_isEnPassant he] at hw
    · simp [Move.enPassantWrites_of_not_isEnPassant he] at hw
  · -- Castling writes an empty square and the rook that stood at home.
    by_cases hc : ∃ w, m.IsCastle p w
    · obtain ⟨w, hw'⟩ := hc
      obtain ⟨-, ⟨-, hr, -⟩, -⟩ := (h.isCastle_iff (w := w)).mp hw'
      rw [Move.castleWrites_of_isCastle hw'] at hw
      simp [hr] at hw
    · simp [Move.castleWrites_of_forall_not_isCastle (not_exists.mp hc)] at hw

/-- **For a pseudo-legal move, `kingSafeAfter` decides king safety: it is true exactly when no
king of the mover's colour is attacked after the move.** -/
theorem kingSafeAfter_iff (h : PseudoLegal p m) :
    kingSafeAfter p m = true ↔ ¬ (p.play m).board.KingAttacked p.turn := by
  simp only [kingSafeAfter, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, Board.superpieceAttackedBy_iff, not_and, Board.KingAttacked, not_exists]
  refine ⟨fun hl s hs => hl s ?_ hs, fun hk s _ => hk s⟩
  rcases h.eq_dst_or_of_play_board_eq_king hs with rfl | hb
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (Board.mem_squaresOf.mpr hb)

/-- **`legalMoves p` is `candidates p` filtered by `Legal`, in the same order.** -/
theorem legalMoves_eq_filter (p : Position) :
    legalMoves p = (candidates p).filter fun m => decide (Legal p m) := by
  rw [legalMoves, pseudoMoves, List.filter_filter]
  -- `List.filter_filter` puts the outer test (king safety) first; `Legal` puts it second.
  congr 1; funext m
  by_cases h : PseudoLegal p m
  · have hk : kingSafeAfter p m = !decide ((p.play m).board.KingAttacked p.turn) := by
      rw [Bool.eq_iff_iff, kingSafeAfter_iff h]; simp
    simp [Legal, h, hk]
  · simp [Legal, h]

/-- `m` is in `legalMoves p` exactly when it is a candidate of `p` and legal in `p`. -/
theorem mem_legalMoves_iff_candidate : m ∈ legalMoves p ↔ m ∈ candidates p ∧ Legal p m := by
  simp [legalMoves_eq_filter]

/-- **Every entry of `legalMoves p` is legal in `p` (M4, soundness).** -/
theorem legalMoves_sound (h : m ∈ legalMoves p) : Legal p m :=
  (mem_legalMoves_iff_candidate.mp h).2

end Generator

/-! ## Completeness -/

section Completeness

variable {p : Position} {m : Move}

/-- A pawn move of the side to move whose target is one of its pawn targets, and which obeys the
promotion rule, is a candidate from its source square. -/
theorem mem_candidatesFrom_pawn (hs : p.board m.src = some ⟨p.turn, .pawn⟩)
    (ht : m.dst ∈ pawnTargets p.turn m.src) (hp : m.PromotionRule p.turn) :
    m ∈ candidatesFrom p m.src := by
  simp only [candidatesFrom, hs, ↓reduceIte, List.mem_flatMap]
  exact ⟨m.dst, ht, mem_pawnMovesTo.mpr ⟨rfl, rfl, hp⟩⟩

/-- A candidate from a move's own source square is a candidate. -/
theorem mem_candidates_of_mem_candidatesFrom (h : m ∈ candidatesFrom p m.src) :
    m ∈ candidates p :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨m.src, Square.mem_all _, h⟩)

/-- A move with no promotion choice to a square short of the last rank obeys the promotion
rule. -/
theorem promotionRule_of_none (hp : m.promo = none) (h : m.dst.relRank p.turn ≠ 7) :
    m.PromotionRule p.turn := by
  simp [Move.PromotionRule, hp, h]

/-- **Every pseudo-legal move of `p` is a candidate of `p` (the cover).** -/
theorem PseudoLegal.mem_candidates (h : PseudoLegal p m) : m ∈ candidates p := by
  rcases h with ⟨k, hk, hs, hr, -, hp⟩ | ⟨hs, hd, -, hpr⟩ | ⟨⟨hs, hd⟩, hr1, -, -, hp⟩ |
    ⟨hs, hr, -, hpr⟩ | ⟨⟨hs, -⟩, hr, hr5, -, -, hp⟩ | ⟨w, hc⟩
  · apply mem_candidates_of_mem_candidatesFrom
    simp only [candidatesFrom, hs, hk, ↓reduceIte, List.mem_map]
    exact ⟨m.dst, mem_reachTargets.mpr hr, by cases m; simp_all⟩
  · exact mem_candidates_of_mem_candidatesFrom
      (mem_candidatesFrom_pawn hs (by simp [pawnTargets, hd]) hpr)
  · refine mem_candidates_of_mem_candidatesFrom
      (mem_candidatesFrom_pawn hs (by simp [pawnTargets, hd]) (promotionRule_of_none hp ?_))
    have := Square.relRank_of_offset_forward (dr := 2) (by simpa using hd)
    omega
  · refine mem_candidates_of_mem_candidatesFrom (mem_candidatesFrom_pawn hs ?_ hpr)
    rcases hr with h | h <;> simp [pawnTargets, h]
  · refine mem_candidates_of_mem_candidatesFrom (mem_candidatesFrom_pawn hs ?_
      (promotionRule_of_none hp (by rw [hr5]; decide)))
    rcases hr with h | h <;> simp [pawnTargets, h]
  · refine List.mem_append_right _ ?_
    have hm := hc.eq_castle
    obtain ⟨⟨hsrc, hk, -⟩, ⟨hright, -⟩, -⟩ := hc
    simp only [castleCandidates, ← hsrc, hk, ↓reduceIte, List.mem_map, List.mem_filter]
    exact ⟨w, ⟨Wing.mem_all w, hright⟩, hm.symm⟩

/-- **`pseudoMoves p` lists exactly the pseudo-legal moves of `p` (M2).** -/
theorem mem_pseudoMoves : m ∈ pseudoMoves p ↔ PseudoLegal p m :=
  mem_pseudoMoves_iff_candidate.trans ⟨And.right, fun h => ⟨h.mem_candidates, h⟩⟩

/-- Every legal move of `p` is listed by `legalMoves p` (M4, completeness). -/
theorem legalMoves_complete (h : Legal p m) : m ∈ legalMoves p :=
  mem_legalMoves_iff_candidate.mpr ⟨h.1.mem_candidates, h⟩

/-- **`legalMoves p` lists exactly the legal moves of `p` (M4).** -/
theorem mem_legalMoves : m ∈ legalMoves p ↔ Legal p m :=
  ⟨legalMoves_sound, legalMoves_complete⟩

/-- **Checkmate is check with no listed move (M6).** -/
theorem checkmate_iff : Checkmate p ↔ InCheck p ∧ legalMoves p = [] := by
  simp only [Checkmate, List.eq_nil_iff_forall_not_mem, mem_legalMoves]

/-- Stalemate is no check and no listed move (M6). -/
theorem stalemate_iff : Stalemate p ↔ ¬ InCheck p ∧ legalMoves p = [] := by
  simp only [Stalemate, List.eq_nil_iff_forall_not_mem, mem_legalMoves]

/-- Checkmate is decided through the generator: check, and no listed move. This replaces the
instance of `Chess.Rules`, which tests every move. -/
instance (priority := high) Checkmate.decidableByGen (p : Position) : Decidable (Checkmate p) :=
  decidable_of_iff _ checkmate_iff.symm

/-- Stalemate is decided through the generator: no check, and no listed move. This replaces the
instance of `Chess.Rules`, which tests every move. -/
instance (priority := high) Stalemate.decidableByGen (p : Position) : Decidable (Stalemate p) :=
  decidable_of_iff _ stalemate_iff.symm

end Completeness

/-! ## No duplicates -/

section NoDuplicates

/-! The generator lists no move twice (M5). Moves from different source squares differ, and from
one square the targets are distinct: knight jumps, king steps and a pawn's targets land on distinct
squares, and the rays of different directions share no square. These facts about the 64 squares
are decided once, by the kernel; the rest is about lists. -/

/-- Filtering keeps a list free of duplicates. -/
private theorem nodup_filter {α : Type} {l : List α} (f : α → Bool) (h : l.Nodup) :
    (l.filter f).Nodup :=
  h.sublist List.filter_sublist

/-- An injective map keeps a list free of duplicates. -/
private theorem nodup_map {α β : Type} {l : List α} {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (h : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  exact h.imp fun hab e => hab (hf _ _ e)

/-- A `flatMap` has no duplicates when each part has none and parts of different entries share no
element. -/
private theorem nodup_flatMap {α β : Type} {l : List α} {f : α → List β}
    (h1 : ∀ a ∈ l, (f a).Nodup) (h2 : l.Pairwise fun a b => ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h2
    refine ⟨h1 a (List.mem_cons_self ..), ih (fun b hb => h1 b (List.mem_cons_of_mem a hb)) hl, ?_⟩
    rintro x hx y hy rfl
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.1 hy
    exact ha b hb x hx hyb

/-- `upToBlocker` keeps a sublist of the squares it is given. -/
theorem Board.upToBlocker_sublist (b : Board) : ∀ l : List Square, (b.upToBlocker l).Sublist l
  | [] => List.Sublist.slnil
  | t :: ts => by
    unfold Board.upToBlocker
    split
    · exact (Board.upToBlocker_sublist b ts).cons₂ t
    · exact (List.nil_sublist ts).cons₂ t

/-- Rays from one square in different directions share no square. -/
theorem Square.not_mem_ray_of_mem_ray {s t : Square} {d d' : Direction} (h : d ≠ d')
    (ht : t ∈ s.ray d) : t ∉ s.ray d' :=
  (by decide +kernel : ∀ s ∈ Square.all, ∀ d ∈ Direction.all, ∀ d' ∈ Direction.all, d ≠ d' →
      ∀ t ∈ s.ray d, t ∉ s.ray d')
    s (Square.mem_all s) d (Direction.mem_all d) d' (Direction.mem_all d') h t ht

/-- The squares a slider reaches from `s`, over all its directions, are distinct; so are a pawn's
diagonal targets, a knight's jumps and a king's steps. -/
theorem reachTargets_nodup (k : Kind) (c : Color) (b : Board) (s : Square) :
    (reachTargets k c b s).Nodup := by
  cases k
  case pawn =>
    exact (by decide +kernel : ∀ c ∈ Color.all, ∀ s ∈ Square.all,
      ([s.offset (-1) c.forward, s.offset 1 c.forward].filterMap id).Nodup)
      c (Color.mem_all c) s (Square.mem_all s)
  case knight =>
    exact (by decide +kernel : ∀ s ∈ Square.all,
      (knightJumps.filterMap fun j => s.offset j.1 j.2).Nodup) s (Square.mem_all s)
  case king =>
    exact (by decide +kernel : ∀ s ∈ Square.all,
      (Direction.all.filterMap fun d => s.shift d 1).Nodup) s (Square.mem_all s)
  all_goals
    refine nodup_flatMap (fun d _ => (b.upToBlocker_sublist _).nodup Square.ray_nodup) ?_
    refine List.Pairwise.imp (fun hne x hx hx' => Square.not_mem_ray_of_mem_ray hne
      ((b.upToBlocker_sublist _).subset hx) ((b.upToBlocker_sublist _).subset hx')) ?_
    decide

variable {p : Position} {m : Move}

/-- A pawn move list has no duplicates. -/
theorem pawnMovesTo_nodup (c : Color) (s t : Square) : (pawnMovesTo c s t).Nodup := by
  unfold pawnMovesTo
  split
  · exact nodup_map (fun _ _ h => by cases h; rfl) PromoKind.all_nodup
  · exact List.pairwise_singleton _ _

/-- Every candidate from `s` starts on `s`. -/
theorem src_of_mem_candidatesFrom {s : Square} (h : m ∈ candidatesFrom p s) : m.src = s := by
  unfold candidatesFrom at h
  split at h
  · split at h
    · split at h
      · obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 h
        exact (mem_pawnMovesTo.1 ht).1
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
        rfl
    · simp at h
  · simp at h

/-- The candidates from one square are distinct. -/
theorem candidatesFrom_nodup (p : Position) (s : Square) : (candidatesFrom p s).Nodup := by
  unfold candidatesFrom
  split
  · split
    · split
      · refine nodup_flatMap (fun t _ => pawnMovesTo_nodup _ _ t) ?_
        refine List.Pairwise.imp (fun hne m hm hm' => hne ?_) ((by decide +kernel :
          ∀ c ∈ Color.all, ∀ s ∈ Square.all, (pawnTargets c s).Nodup)
          p.turn (Color.mem_all _) s (Square.mem_all s))
        exact (mem_pawnMovesTo.1 hm).2.1.symm.trans (mem_pawnMovesTo.1 hm').2.1
      · exact nodup_map (fun _ _ h => by cases h; rfl) (reachTargets_nodup ..)
    · exact List.nodup_nil
  · exact List.nodup_nil

/-- The castling candidates are distinct, and none of them is the move of a king from its home
square to an adjacent square, so none is also a candidate from a square. -/
theorem castleCandidates_nodup (p : Position) : (castleCandidates p).Nodup := by
  unfold castleCandidates
  split
  · exact nodup_map (fun w w' h => (by decide : ∀ c ∈ Color.all, ∀ w ∈ Wing.all, ∀ w' ∈ Wing.all,
      Move.castle c w = Move.castle c w' → w = w') p.turn (Color.mem_all _) w (Wing.mem_all w) w'
      (Wing.mem_all w') h) (nodup_filter _ Wing.all_nodup)
  · exact List.nodup_nil

/-- A castling candidate is not a candidate from any square. -/
theorem not_mem_candidatesFrom_of_mem_castleCandidates {s : Square}
    (h : m ∈ castleCandidates p) : m ∉ candidatesFrom p s := by
  intro h'
  unfold castleCandidates at h
  split at h
  · next hk =>
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    have hs := src_of_mem_candidatesFrom h'
    simp only [Move.castle] at hs
    subst hs
    simp only [candidatesFrom, hk, ↓reduceIte, List.mem_map, reduceCtorEq] at h'
    obtain ⟨t, ht, he⟩ := h'
    simp only [Move.castle, Move.mk.injEq] at he
    rw [he.2.1] at ht
    exact (by decide +kernel : ∀ c ∈ Color.all, ∀ w ∈ Wing.all, kingCastleSquare c w ∉
      (Direction.all.filterMap fun d => (kingHome c).shift d 1)) p.turn (Color.mem_all _) w
      (Wing.mem_all w) ht
  · simp at h

/-- The candidates of a position are distinct. -/
theorem candidates_nodup (p : Position) : (candidates p).Nodup := by
  unfold candidates
  rw [List.nodup_append]
  refine ⟨nodup_flatMap (fun s _ => candidatesFrom_nodup p s) ?_, castleCandidates_nodup p, ?_⟩
  · exact Square.all_nodup.imp fun hne m hm hm' =>
      hne ((src_of_mem_candidatesFrom hm).symm.trans (src_of_mem_candidatesFrom hm'))
  · rintro m hm m' hm' rfl
    obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 hm
    exact not_mem_candidatesFrom_of_mem_castleCandidates hm' hs

/-- **The pseudo-legal moves of `p` are listed without duplicates.** -/
theorem pseudoMoves_nodup (p : Position) : (pseudoMoves p).Nodup :=
  nodup_filter _ (candidates_nodup p)

/-- **The legal moves of `p` are listed without duplicates (M5).** -/
theorem legalMoves_nodup (p : Position) : (legalMoves p).Nodup :=
  nodup_filter _ (pseudoMoves_nodup p)

end NoDuplicates

/-! ## Perft -/

/-- The number of ways to choose `n` moves one after another from `p`, each an entry of
`legalMoves` of the position reached so far; a move counts as often as `legalMoves` lists it (perft
of depth `n`). Depth 0 counts the empty choice, so it is 1 for every position. A line that reaches a
position where `legalMoves` is empty before its `n`-th move adds nothing. No move clock and no
history are read, so the counts can be compared with the published ones (chessprogramming.org,
*Perft Results*). -/
def perft : Nat → Position → Nat
  | 0, _ => 1
  | n + 1, p => ((legalMoves p).map fun m => perft n (p.play m)).sum

/-- For each entry of `legalMoves p`, in order, the move and the perft of depth `n` after it: the
'divide' that localizes a disagreement with another program's perft. -/
def perftDivide (n : Nat) (p : Position) : List (Move × Nat) :=
  (legalMoves p).map fun m => (m, perft n (p.play m))

/-- Perft of depth 0 is 1: the empty choice. -/
@[simp] theorem perft_zero (p : Position) : perft 0 p = 1 := rfl

/-- Perft of depth `n + 1` adds up, over the entries of `legalMoves p`, perft of depth `n` after
each. -/
theorem perft_succ (n : Nat) (p : Position) :
    perft (n + 1) p = ((legalMoves p).map fun m => perft n (p.play m)).sum := rfl

/-- Perft of depth 1 is the number of entries of `legalMoves p`. -/
theorem perft_one (p : Position) : perft 1 p = (legalMoves p).length := by
  simp [perft, List.map_const']

/-- The divide's counts add up to perft of one more ply. -/
theorem sum_perftDivide (n : Nat) (p : Position) :
    ((perftDivide n p).map (·.2)).sum = perft (n + 1) p := by
  simp [perftDivide, perft_succ, Function.comp_def]

/-! ## Legal lines (M8) -/

/-- `LegalLine p ms`: `ms` is a sequence of moves, each legal in the position reached so far from
`p`. -/
inductive LegalLine : Position → List Move → Prop
  /-- The empty sequence is a legal line from any position. -/
  | nil {p : Position} : LegalLine p []
  /-- A legal move followed by a legal line from the position after it is a legal line. -/
  | cons {p : Position} {m : Move} {ms : List Move} :
      Legal p m → LegalLine (p.play m) ms → LegalLine p (m :: ms)

/-- The legal lines of `n` moves from `p`, in the generator's order: for each entry `m` of
`legalMoves p`, the lines of `n - 1` moves after it, each preceded by `m`. -/
def lines : Nat → Position → List (List Move)
  | 0, _ => [[]]
  | n + 1, p => (legalMoves p).flatMap fun m => (lines n (p.play m)).map (m :: ·)

section Lines


/-- **`lines n p` lists exactly the legal lines of `n` moves from `p`.** -/
theorem mem_lines {n : Nat} {p : Position} {ms : List Move} :
    ms ∈ lines n p ↔ LegalLine p ms ∧ ms.length = n := by
  induction n generalizing p ms with
  | zero =>
    simp only [lines, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨.nil, rfl⟩
    · exact fun h => h.2
  | succ n ih =>
    simp only [lines, List.mem_flatMap, List.mem_map, mem_legalMoves]
    constructor
    · rintro ⟨m, hm, ms', hms', rfl⟩
      obtain ⟨hl, hlen⟩ := ih.1 hms'
      exact ⟨.cons hm hl, by simp [hlen]⟩
    · rintro ⟨hl, hlen⟩
      cases hl with
      | nil => simp at hlen
      | cons hm hl' =>
        exact ⟨_, hm, _, ih.2 ⟨hl', by simpa using hlen⟩, rfl⟩

/-- **`lines n p` lists no line twice.** -/
theorem lines_nodup (n : Nat) (p : Position) : (lines n p).Nodup := by
  induction n generalizing p with
  | zero => simp [lines]
  | succ n ih =>
    simp only [lines]
    refine nodup_flatMap (fun m _ => nodup_map (fun _ _ h => (List.cons.inj h).2) (ih _)) ?_
    refine (legalMoves_nodup p).imp fun hne x hx hx' => hne ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hx'
    exact (List.cons.inj hb).1.symm

/-- **Perft counts legal lines (M8).** `perft n p` is the number of sequences of `n` moves from `p`,
each legal in the position reached so far. -/
theorem perft_eq_length_lines (n : Nat) (p : Position) : perft n p = (lines n p).length := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [perft, lines, List.length_flatMap, List.length_map, ih]

/-- **Perft is the number of legal lines, whichever list counts them.** Any list of move sequences
that holds exactly the legal lines of `n` moves from `p`, each once, has `perft n p` entries. -/
theorem perft_eq_length_of_mem_iff {n : Nat} {p : Position} {L : List (List Move)} (hL : L.Nodup)
    (h : ∀ ms, ms ∈ L ↔ LegalLine p ms ∧ ms.length = n) : L.length = perft n p := by
  have count_one : ∀ {l : List (List Move)} {a : List Move}, l.Nodup → a ∈ l → l.count a = 1 :=
    fun hl ha => Nat.le_antisymm (List.nodup_iff_count.1 hl _) (List.count_pos_iff.2 ha)
  rw [perft_eq_length_lines]
  refine (List.perm_iff_count.mpr fun a => ?_).length_eq
  by_cases ha : a ∈ L
  · rw [count_one hL ha, count_one (lines_nodup n p) (mem_lines.2 ((h a).1 ha))]
  · rw [List.count_eq_zero.2 ha, List.count_eq_zero.2 fun h' => ha ((h a).2 (mem_lines.1 h'))]

end Lines

/-! ## Testing against the specification -/

/-- The legal moves of `p` found from the specification alone, for tests: every move from a square
holding a piece of the side to move, to any square, with no promotion choice or with each of the
four in turn, that `Legal` allows. Slow: 320 moves are tested per piece of the side to move. -/
def legalMovesBySpec (p : Position) : List Move :=
  let sources := Square.all.filter fun s => p.board.colorAt s = some p.turn
  let moves := sources.flatMap fun s =>
    Square.all.flatMap fun t => (none :: PromoKind.all.map some).map fun o => ⟨s, t, o⟩
  moves.filter fun m => decide (Legal p m)

/-- The generator agrees with the specification on `p`: every move `legalMovesBySpec` finds is
listed by `legalMoves`, and `legalMoves` lists no move twice. (That every listed move is legal is a
theorem, `legalMoves_sound`. Since M4, `mem_legalMoves`, and M5, `legalMoves_nodup`, both halves
hold at every position, so the test now only cross-checks the generator against the specification
by computation.) -/
def agreesWithLegal (p : Position) : Bool :=
  (legalMovesBySpec p).all (· ∈ legalMoves p) && decide (legalMoves p).Nodup

section Testing

variable {p : Position} {m : Move}

/-- `m` is in `legalMovesBySpec p` exactly when it is legal in `p`. -/
theorem mem_legalMovesBySpec : m ∈ legalMovesBySpec p ↔ Legal p m := by
  simp only [legalMovesBySpec, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine ⟨m.src, ⟨Square.mem_all _, by simpa using h.1.colorAt_src⟩, m.dst, Square.mem_all _,
    m.promo, ?_, rfl⟩
  cases m.promo <;> simp [PromoKind.mem_all]

/-- If the generator agrees with the specification on `p`, then `legalMoves p` lists exactly the
legal moves of `p` (M4 at `p`). Superseded by `mem_legalMoves`, which needs no hypothesis. -/
theorem mem_legalMoves_of_agreesWithLegal (h : agreesWithLegal p = true) :
    m ∈ legalMoves p ↔ Legal p m := by
  refine ⟨legalMoves_sound, fun hl => ?_⟩
  simp only [agreesWithLegal, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1 m (mem_legalMovesBySpec.mpr hl)

/-- If the generator agrees with the specification on `p`, then `legalMoves p` lists no move twice
(M5 at `p`). -/
theorem nodup_legalMoves_of_agreesWithLegal (h : agreesWithLegal p = true) :
    (legalMoves p).Nodup := by
  simp only [agreesWithLegal, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

end Testing

/-! ## Tests

The tests of this module are in `ChessTest/MoveGen.lean`, and the six standard perft positions in
`ChessTest/Perft.lean` (`lake build ChessTest`). The checks below stay here as documentation; they
are cheap. -/

-- The initial position: 20 legal moves, 400 after two plies, and agreement with `Legal`.
#guard (legalMoves Position.initial).length == 20
#guard perft 2 Position.initial == 400
#guard agreesWithLegal Position.initial
-- The empty board: the castling rights alone propose nothing.
#guard (candidates ⟨Board.empty, .white, CastlingRights.full, none⟩).isEmpty

end Chess
