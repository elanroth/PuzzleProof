import Chess.Basic

/-!
# Position

Boards, moves, castling rights and positions: the data of the move layer. Specification:
`docs/spec/Position.md`; every definition below carries the docstring given there.

## Main definitions

* `Board`: a function from squares to `Option Piece`. `Board.set` is the only way to write to it.
* `Piece.code` and `Piece.ofCode`: the one table of piece codes, and its inverse found by search.
* `Board.pack` and `Board.unpack`: a board written as one natural number, one hexadecimal digit
  per square, for generated checkpoint literals.
* `Move`: a source square, a destination square and an optional promotion choice, as in UCI.
* `CastlingRights`: four FEN flags, by convention read with `get` and changed only by `revoke` and
  `revokeAll`; `CastlingRights.none`, `CastlingRights.full`, and the pointwise order `≤`.
* `Position`: board, side to move, castling rights and en passant target; `Position.initial`.

## Main statements

* `Board.set_same`, `Board.set_ne`, `Board.set_comm`: the frame lemmas every move proof uses.
* `Board.unpack_pack`: a packed literal unpacks to the board it was packed from.
* (R8) `CastlingRights.revoke_le`, `CastlingRights.revokeAll_le`: revoking never adds a right.
  `CastlingRights.get_revoke`, `CastlingRights.get_revokeAll`: what a revocation leaves held.
* `Board.initial_kingHome`, `Board.initial_rookHome`, `Board.initial_flip` and the other sanity
  theorems about the initial board.

## Implementation notes

* A board is a function, and `set` is its only writer, so it is faithful by construction (one
  thing per square, no padding, no sentinel) and every frame lemma is a `set_ne` rewrite. State
  disequalities as `t ≠ s`, read square first: with `h : s ≠ t`, `simp [h]` makes no progress.
* `ext s` on boards overshoots into `Option.ext`; write `ext s : 1` or
  `refine Board.ext fun s => ?_`.
* `Piece.code` is the only table of codes; `Piece.ofCode` searches `Piece.all` for a code, so the
  inverse cannot disagree with it. If board reads ever dominate certificate checking, a `match`
  can replace its body, proved equal by `decide`, with no other change.
* Packed digits are read by division, `n / 16 ^ i % 16`, which core's `Nat` lemmas speak about and
  the kernel accelerates. Digit `i` belongs to the square with index `i`.
* Castling rights are four `Bool`s behind `get`, so equality is structural and statements are
  indexed by colour and wing. The type has 16 values, so its whole-type quantifier makes every
  lemma about rights a `decide`.
-/

namespace Chess

/-! ## Boards -/

/-- A board: for each square, the piece standing on it, or `none` if the square is empty. -/
def Board : Type := Square → Option Piece

/-- Two boards are equal when they hold the same thing on every square. -/
@[ext] theorem Board.ext {b b' : Board} (h : ∀ s, b s = b' s) : b = b' := funext h

/-- Two boards are compared square by square, through the decidable quantifier over squares: at
most 64 comparisons. -/
instance Board.decEq : DecidableEq Board := fun b b' =>
  decidable_of_iff (∀ s, b s = b' s) ⟨Board.ext, fun h _ => h ▸ rfl⟩

/-- The board with nothing on it. -/
def Board.empty : Board := fun _ => none

/-- The default board is the empty board. -/
instance : Inhabited Board := ⟨Board.empty⟩

/-- The board `b` with square `s` made to hold `x`: `x` on `s`, and on every other square what `b`
has there. -/
def Board.set (b : Board) (s : Square) (x : Option Piece) : Board :=
  fun t => if t = s then x else b t

namespace Board

variable {b : Board} {s s' t : Square} {x y : Option Piece}

/-- Reading a square of the empty board gives nothing. -/
@[simp] theorem empty_apply (s : Square) : Board.empty s = none := rfl

/-- What `b.set s x` holds on `t` is `x` if `t` is `s`, and what `b` holds on `t` otherwise. -/
theorem set_apply (b : Board) (s : Square) (x : Option Piece) (t : Square) :
    b.set s x t = if t = s then x else b t := rfl

/-- After setting `s` to `x`, square `s` holds `x`. -/
@[simp] theorem set_same (b : Board) (s : Square) (x : Option Piece) : b.set s x s = x :=
  if_pos rfl

/-- Setting `s` does not change any other square. -/
@[simp] theorem set_ne (h : t ≠ s) : b.set s x t = b t := if_neg h

/-- Setting two different squares can be done in either order. -/
theorem set_comm (h : s ≠ s') : (b.set s x).set s' y = (b.set s' y).set s x := by
  refine Board.ext fun t => ?_
  simp only [set]
  split <;> split <;> simp_all

/-- Setting the same square twice keeps only the second value. -/
@[simp] theorem set_set : (b.set s x).set s y = b.set s y := by
  refine Board.ext fun t => ?_
  simp only [set]
  split <;> simp_all

/-- Setting a square to what it already holds changes nothing. -/
@[simp] theorem set_eq_self : b.set s (b s) = b := by
  refine Board.ext fun t => ?_
  simp only [set]
  split <;> simp_all

end Board

/-! ## Piece codes and packed boards -/

/-- The code of piece `pc` in packed boards: 1 to 6 for the white pawn, knight, bishop, rook,
queen and king, and 7 to 12 for the black ones in the same order. Code 0 means an empty square, and
codes 13 to 15 are unused. -/
def Piece.code (pc : Piece) : Fin 16 :=
  match pc.color, pc.kind with
  | .white, .pawn => 1  | .white, .knight => 2  | .white, .bishop => 3
  | .white, .rook => 4  | .white, .queen  => 5  | .white, .king   => 6
  | .black, .pawn => 7  | .black, .knight => 8  | .black, .bishop => 9
  | .black, .rook => 10 | .black, .queen  => 11 | .black, .king   => 12

/-- The piece whose code is `v`, or `none` if no piece has code `v` (code 0, which marks an empty
square, and the unused codes 13 to 15). -/
def Piece.ofCode (v : Fin 16) : Option Piece :=
  Piece.all.find? fun pc => pc.code = v

/-- The code of what stands on a square: 0 if it is empty, and the piece's code otherwise. -/
def contentsCode (x : Option Piece) : Fin 16 :=
  match x with
  | none    => 0
  | some pc => pc.code

/-- The `i`-th hexadecimal digit of `n`, the least significant being the 0th (0 beyond the most
significant digit). -/
def hexDigit (n i : Nat) : Fin 16 := ⟨n / 16 ^ i % 16, Nat.mod_lt _ (by decide)⟩

/-- The number whose hexadecimal digits, from the least significant one up, are the entries of
`l`, followed by zeros. -/
def ofHexDigits (l : List (Fin 16)) : Nat := l.foldr (fun v acc => v.val + 16 * acc) 0

/-- The board written as the number `n`: square `s` holds the piece whose code is the
`s.index`-th hexadecimal digit of `n`, and is empty if that digit is 0 or an unused code (13 to
15). Digits beyond the 63rd are ignored. -/
def Board.unpack (n : Nat) : Board := fun s => Piece.ofCode (hexDigit n s.index.val)

/-- The packed form of board `b`: the number below 16 ^ 64 whose `s.index`-th hexadecimal digit is
the code of what stands on `s`. -/
def Board.pack (b : Board) : Nat := ofHexDigits (Square.all.map fun s => contentsCode (b s))

section PackedBoards

variable {pc pc' : Piece} {v : Fin 16}

/-- Reading back the code of a piece gives the piece. -/
@[simp] theorem Piece.ofCode_code (pc : Piece) : Piece.ofCode pc.code = some pc := by
  revert pc; decide

/-- Code 0 is no piece. -/
@[simp] theorem Piece.ofCode_zero : Piece.ofCode 0 = none := by decide

/-- Reading back the code of a square's contents gives the contents. -/
@[simp] theorem Piece.ofCode_contentsCode (x : Option Piece) :
    Piece.ofCode (contentsCode x) = x := by
  cases x with
  | none    => exact Piece.ofCode_zero
  | some pc => exact Piece.ofCode_code pc

/-- Different pieces have different codes. -/
@[simp] theorem Piece.code_inj : pc.code = pc'.code ↔ pc = pc' := by
  revert pc pc'; decide

/-- No piece has code 0. -/
theorem Piece.code_ne_zero (pc : Piece) : pc.code ≠ 0 := by
  revert pc; decide

/-- A code is read as empty exactly when it is 0 or one of the unused codes 13 to 15. -/
theorem Piece.ofCode_eq_none_iff : Piece.ofCode v = none ↔ v = 0 ∨ 13 ≤ v.val := by
  revert v; decide

/-- The `i`-th hexadecimal digit of the number with digit list `l` is entry `i` of `l`, or 0
beyond its end. -/
theorem hexDigit_ofHexDigits (l : List (Fin 16)) (i : Nat) :
    hexDigit (ofHexDigits l) i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [hexDigit, ofHexDigits]
  | cons v l ih =>
    cases i with
    | zero => apply Fin.ext; simp [hexDigit, ofHexDigits]
    | succ i =>
      -- Dividing by `16 ^ (i + 1)` divides by 16 first, which drops the low digit `v`.
      rw [List.getD_cons_succ, ← ih i]
      apply Fin.ext
      have hv : v.val / 16 = 0 := Nat.div_eq_of_lt v.isLt
      simp only [hexDigit, ofHexDigits, List.foldr_cons, Nat.pow_succ, Nat.mul_comm (16 ^ i),
        ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide : 0 < 16), hv,
        Nat.zero_add]

/-- The number with digit list `l` is below `16 ^ l.length`. -/
theorem ofHexDigits_lt (l : List (Fin 16)) : ofHexDigits l < 16 ^ l.length := by
  induction l with
  | nil => simp [ofHexDigits]
  | cons v l ih =>
    simp only [ofHexDigits, List.foldr_cons, List.length_cons, Nat.pow_succ] at ih ⊢
    have := v.isLt
    omega

/-- Entry `s.index` of the list of all squares is `s`. -/
theorem Square.getElem?_all_index (s : Square) : Square.all[s.index.val]? = some s := by
  rw [List.getElem?_eq_getElem (by rw [Square.length_all]; exact s.index.isLt)]
  simp only [Square.all, List.getElem_map, List.getElem_finRange]
  exact congrArg some (Square.ofIndex_index s)

/-- The `s.index`-th hexadecimal digit of a packed board is the code of what stands on `s`. -/
theorem Board.hexDigit_pack (b : Board) (s : Square) :
    hexDigit b.pack s.index.val = contentsCode (b s) := by
  rw [Board.pack, hexDigit_ofHexDigits, List.getD_eq_getElem?_getD, List.getElem?_map,
    Square.getElem?_all_index]
  rfl

/-- A packed board is below `16 ^ 64`: it has at most 64 hexadecimal digits. -/
theorem Board.pack_lt (b : Board) : b.pack < 16 ^ 64 := by
  have h := ofHexDigits_lt (Square.all.map fun s => contentsCode (b s))
  rwa [List.length_map, Square.length_all] at h

/-- Square `s` of an unpacked board is read from the `s.index`-th hexadecimal digit. -/
theorem Board.unpack_apply (n : Nat) (s : Square) :
    Board.unpack n s = Piece.ofCode (hexDigit n s.index.val) := rfl

/-- Unpacking the packing of a board gives the board back. -/
@[simp] theorem Board.unpack_pack (b : Board) : Board.unpack b.pack = b := by
  refine Board.ext fun s => ?_
  rw [Board.unpack_apply, Board.hexDigit_pack, Piece.ofCode_contentsCode]

end PackedBoards

/-! ## Moves -/

/-- A move as data, as in UCI notation: a source square, a destination square, and an optional
promotion choice. Castling is written as the king's two-square move (e1g1, e1c1, e8g8, e8c8),
never as king-takes-rook; this library has no Chess960. -/
@[ext] structure Move where
  /-- The source square. -/
  src : Square
  /-- The destination square. -/
  dst : Square
  /-- The promotion choice, meaningful only when a pawn reaches its last rank: `some pk` promotes
  it to kind `pk.toKind`. A move whose `promo` does not match the position is not legal
  (`Chess.Rules`). -/
  promo : Option PromoKind
  deriving DecidableEq, Inhabited

/-- `∀` over moves is decided through the two squares and the five promotion choices (`none` and
the four `PromoKind`s): 64 × 64 × 5 candidates. -/
instance (priority := low) Move.decidableForall (P : Move → Prop) [DecidablePred P] :
    Decidable (∀ m, P m) :=
  decidable_of_iff (∀ s t : Square, P ⟨s, t, none⟩ ∧ ∀ pk : PromoKind, P ⟨s, t, some pk⟩)
    ⟨fun h m => match m with
      | ⟨s, t, none⟩    => (h s t).1
      | ⟨s, t, some pk⟩ => (h s t).2 pk,
     fun h _ _ => ⟨h _, fun _ => h _⟩⟩

/-- `∃` over moves is decided through the two squares and the five promotion choices. -/
instance (priority := low) Move.decidableExists (P : Move → Prop) [DecidablePred P] :
    Decidable (∃ m, P m) :=
  decidable_of_iff (∃ s t : Square, P ⟨s, t, none⟩ ∨ ∃ pk : PromoKind, P ⟨s, t, some pk⟩)
    ⟨fun ⟨_, _, h⟩ => h.elim (fun h => ⟨_, h⟩) (fun ⟨_, h⟩ => ⟨_, h⟩),
     fun ⟨⟨s, t, o⟩, h⟩ => ⟨s, t, match o, h with
       | none, h    => .inl h
       | some pk, h => .inr ⟨pk, h⟩⟩⟩

/-! ## Castling rights -/

/-- The castling rights: for each colour and wing, the FEN flag saying whether that colour still
holds the right to castle on that wing. The four flags are in FEN order (K, Q, k, q). By
convention they are read with `get` and changed only with `revoke` and `revokeAll`; the fields stay
public for literals, so it is `Chess.Rules` (R8) that proves a move adds no right. -/
structure CastlingRights where
  /-- White's kingside castling flag (FEN `K`). -/
  whiteKingside : Bool
  /-- White's queenside castling flag (FEN `Q`). -/
  whiteQueenside : Bool
  /-- Black's kingside castling flag (FEN `k`). -/
  blackKingside : Bool
  /-- Black's queenside castling flag (FEN `q`). -/
  blackQueenside : Bool
  deriving DecidableEq, Repr, Inhabited

namespace CastlingRights

/-- Whether `cr` holds colour `c`'s right to castle on wing `w`: the FEN flag, which is lost when
the king or that wing's rook moves, or that rook is captured on its home square (FIDE 3.8.2.1 and
the FEN convention). It does not say that castling is possible now. -/
def get (cr : CastlingRights) (c : Color) (w : Wing) : Bool :=
  match c, w with
  | .white, .kingside  => cr.whiteKingside
  | .white, .queenside => cr.whiteQueenside
  | .black, .kingside  => cr.blackKingside
  | .black, .queenside => cr.blackQueenside

/-- The rights `cr` with colour `c`'s right on wing `w` set to not held (whether or not it was
held), and every other right unchanged. -/
def revoke (cr : CastlingRights) (c : Color) (w : Wing) : CastlingRights :=
  match c, w with
  | .white, .kingside  => { cr with whiteKingside := false }
  | .white, .queenside => { cr with whiteQueenside := false }
  | .black, .kingside  => { cr with blackKingside := false }
  | .black, .queenside => { cr with blackQueenside := false }

/-- The rights `cr` with both of colour `c`'s rights set to not held, as after a move of `c`'s
king (FIDE 3.8.2.1). -/
def revokeAll (cr : CastlingRights) (c : Color) : CastlingRights :=
  (cr.revoke c .kingside).revoke c .queenside

/-- No castling rights: neither colour holds a right on either wing. -/
def none : CastlingRights := ⟨false, false, false, false⟩

/-- All four castling rights, as at the start of a game. -/
def full : CastlingRights := ⟨true, true, true, true⟩

/-- `∀` over castling rights is decided through the four flags: 16 cases. -/
instance (priority := low) decidableForall (P : CastlingRights → Prop) [DecidablePred P] :
    Decidable (∀ cr, P cr) :=
  decidable_of_iff (∀ a b c d : Bool, P ⟨a, b, c, d⟩)
    ⟨fun h cr => h cr.1 cr.2 cr.3 cr.4, fun h a b c d => h ⟨a, b, c, d⟩⟩

/-- `∃` over castling rights is decided through the four flags: 16 cases. -/
instance (priority := low) decidableExists (P : CastlingRights → Prop) [DecidablePred P] :
    Decidable (∃ cr, P cr) :=
  decidable_of_iff (∃ a b c d : Bool, P ⟨a, b, c, d⟩)
    ⟨fun ⟨_, _, _, _, h⟩ => ⟨_, h⟩, fun ⟨cr, h⟩ => ⟨cr.1, cr.2, cr.3, cr.4, h⟩⟩

/-- `cr ≤ cr'` when every right held in `cr` is also held in `cr'`. -/
instance : LE CastlingRights :=
  ⟨fun cr cr' => ∀ c w, cr.get c w = true → cr'.get c w = true⟩

/-- Whether `cr ≤ cr'` is decided by checking both colours and both wings. -/
instance decidableLE (cr cr' : CastlingRights) : Decidable (cr ≤ cr') :=
  inferInstanceAs (Decidable (∀ c w, cr.get c w = true → cr'.get c w = true))

variable {cr cr' cr'' : CastlingRights} {c c' : Color} {w w' : Wing}

/-- Two castling rights are equal when they agree for every colour and wing. -/
@[ext] theorem ext_get (h : ∀ c w, cr.get c w = cr'.get c w) : cr = cr' := by
  revert cr cr'; decide

/-- `CastlingRights.none` holds no right. -/
@[simp] theorem get_none (c : Color) (w : Wing) : CastlingRights.none.get c w = false := by
  revert c w; decide

/-- `CastlingRights.full` holds every right. -/
@[simp] theorem get_full (c : Color) (w : Wing) : CastlingRights.full.get c w = true := by
  revert c w; decide

/-- A revoked right is not held. -/
@[simp] theorem get_revoke_self (cr : CastlingRights) (c : Color) (w : Wing) :
    (cr.revoke c w).get c w = false := by
  revert cr c w; decide

/-- Revoking one right leaves every other right as it was. -/
theorem get_revoke_of_ne (h : c' ≠ c ∨ w' ≠ w) : (cr.revoke c w).get c' w' = cr.get c' w' := by
  revert cr c c' w w'; decide

/-- After `revokeAll c`, colour `c` holds no right. -/
@[simp] theorem get_revokeAll_self (cr : CastlingRights) (c : Color) (w : Wing) :
    (cr.revokeAll c).get c w = false := by
  revert cr c w; decide

/-- `revokeAll c` leaves the other colour's rights as they were. -/
theorem get_revokeAll_of_ne (h : c' ≠ c) : (cr.revokeAll c).get c' w = cr.get c' w := by
  revert cr c c' w; decide

/-- After revoking colour `c`'s right on wing `w`, a right is held exactly when it was held before
and is not that one. -/
theorem get_revoke (cr : CastlingRights) (c c' : Color) (w w' : Wing) :
    (cr.revoke c w).get c' w' = (cr.get c' w' && !(c' == c && w' == w)) := by
  revert cr c c' w w'; decide

/-- After revoking all of colour `c`'s rights, a right is held exactly when it was held before and
is not one of `c`'s. -/
theorem get_revokeAll (cr : CastlingRights) (c c' : Color) (w : Wing) :
    (cr.revokeAll c).get c' w = (cr.get c' w && !(c' == c)) := by
  revert cr c c' w; decide

/-- `cr ≤ cr'` means every right of `cr` is a right of `cr'`. -/
theorem le_def : cr ≤ cr' ↔ ∀ c w, cr.get c w = true → cr'.get c w = true := Iff.rfl

/-- The order is reflexive. -/
@[simp] theorem le_refl (cr : CastlingRights) : cr ≤ cr := fun _ _ h => h

/-- The order is transitive. -/
theorem le_trans (h : cr ≤ cr') (h' : cr' ≤ cr'') : cr ≤ cr'' := fun c w hc => h' c w (h c w hc)

/-- The order is antisymmetric. -/
theorem le_antisymm (h : cr ≤ cr') (h' : cr' ≤ cr) : cr = cr' := by
  revert cr cr'; decide

/-- Inequalities between castling rights chain in `calc`. -/
instance : Trans (α := CastlingRights) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans⟩

/-- (R8) Revoking never adds a right. -/
theorem revoke_le (cr : CastlingRights) (c : Color) (w : Wing) : cr.revoke c w ≤ cr := by
  revert cr c w; decide

/-- (R8) Revoking all of a colour's rights never adds a right. -/
theorem revokeAll_le (cr : CastlingRights) (c : Color) : cr.revokeAll c ≤ cr :=
  le_trans (revoke_le _ c .queenside) (revoke_le cr c .kingside)

/-- No rights is below everything. -/
@[simp] theorem none_le (cr : CastlingRights) : CastlingRights.none ≤ cr := by
  revert cr; decide

/-- All rights are above everything. -/
@[simp] theorem le_full (cr : CastlingRights) : cr ≤ CastlingRights.full := by
  revert cr; decide

/-- Revocations can be made in any order. -/
theorem revoke_comm (cr : CastlingRights) (c c' : Color) (w w' : Wing) :
    (cr.revoke c w).revoke c' w' = (cr.revoke c' w').revoke c w := by
  revert cr c c' w w'; decide

/-- Revoking twice is revoking once. -/
@[simp] theorem revoke_revoke_self (cr : CastlingRights) (c : Color) (w : Wing) :
    (cr.revoke c w).revoke c w = cr.revoke c w := by
  revert cr c w; decide

end CastlingRights

/-! ## Positions -/

/-- A position of the move layer: the board, the side to move, the castling rights and the en
passant target. It holds what decides which moves are legal and what they do; no move clocks and
no history (DESIGN §4.6). -/
@[ext] structure Position where
  /-- What stands on each square. -/
  board : Board
  /-- The side to move. -/
  turn : Color
  /-- The castling rights: for each colour and wing, the FEN flag saying whether that right is
  still held (FIDE 3.8.2.1). Whether castling is possible on this move is decided by the rules. -/
  castling : CastlingRights
  /-- The en passant target: `some t` means the previous move was a pawn's two-square advance over
  `t`, so a capture onto `t` may be considered this move (FIDE 3.7.3.2); `none` means it was not.
  Set after every two-square advance, whether or not any pawn can capture (the PGN-standard
  convention, not Stockfish's). -/
  epTarget : Option Square

/-- Two positions are compared field by field, the three small fields first and the board (at
most 64 comparisons) last. -/
instance Position.decEq : DecidableEq Position := fun p q =>
  decidable_of_iff
    (p.turn = q.turn ∧ p.castling = q.castling ∧ p.epTarget = q.epTarget ∧ p.board = q.board)
    ⟨fun ⟨h1, h2, h3, h4⟩ => Position.ext h4 h1 h2 h3, fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The kind of piece that starts on file `f` of either colour's home rank (the same for both):
rook, knight, bishop, queen, king, bishop, knight, rook from the a-file to the h-file (FIDE 2.3). -/
def backRankKind (f : Fin 8) : Kind :=
  match f with
  | 0 => .rook | 1 => .knight | 2 => .bishop | 3 => .queen
  | 4 => .king | 5 => .bishop | 6 => .knight | 7 => .rook

/-- The piece of colour `c` that stands on `s` at the start of a game, if any: on `c`'s home rank
(`relRank` 0) the piece of kind `backRankKind s.file`, on the next rank (`relRank` 1) a pawn, and
elsewhere nothing. -/
def startingPiece (c : Color) (s : Square) : Option Piece :=
  if s.relRank c = 0 then some ⟨c, backRankKind s.file⟩
  else if s.relRank c = 1 then some ⟨c, .pawn⟩
  else none

/-- The board at the start of a game (FIDE 2.3): each square holds the starting piece of whichever
colour has one there; no square has both (`startingPiece_white_or_black`). -/
def Board.initial : Board := fun s => (startingPiece .white s).or (startingPiece .black s)

/-- The position at the start of a game: the initial board, White to move, all four castling
rights, and no en passant target. -/
def Position.initial : Position :=
  { board := Board.initial, turn := .white, castling := .full, epTarget := none }

/-- The default position is the initial position. -/
instance : Inhabited Position := ⟨Position.initial⟩

section InitialPosition

variable {s : Square} {c : Color}

/-- The initial position has the initial board. -/
@[simp] theorem Position.initial_board : Position.initial.board = Board.initial := rfl

/-- The initial position has White to move. -/
@[simp] theorem Position.initial_turn : Position.initial.turn = .white := rfl

/-- The initial position has all four castling rights. -/
@[simp] theorem Position.initial_castling : Position.initial.castling = .full := rfl

/-- The initial position has no en passant target. -/
@[simp] theorem Position.initial_epTarget : Position.initial.epTarget = none := rfl

/-- Each king starts on its home square. -/
theorem Board.initial_kingHome (c : Color) : Board.initial (kingHome c) = some ⟨c, .king⟩ := by
  cases c <;> rfl

/-- Each rook starts on its home square. -/
theorem Board.initial_rookHome (c : Color) (w : Wing) :
    Board.initial (rookHome c w) = some ⟨c, .rook⟩ := by
  cases c <;> cases w <;> rfl

/-- Each queen starts on the d-file of its home rank. -/
theorem Board.initial_queen (c : Color) : Board.initial ⟨3, c.homeRank⟩ = some ⟨c, .queen⟩ := by
  cases c <;> rfl

/-- A colour's pawns fill its second rank (`relRank c = 1`). -/
theorem Board.initial_of_relRank_one (h : s.relRank c = 1) :
    Board.initial s = some ⟨c, .pawn⟩ := by
  revert s; cases c <;> decide

/-- The squares on ranks 3 to 6 (`rank` 2 to 5) are empty, and no others. -/
theorem Board.initial_eq_none_iff : Board.initial s = none ↔ 2 ≤ s.rank.val ∧ s.rank.val ≤ 5 := by
  revert s; decide

/-- A queen starts on a square of its own colour: the white queen on a light square, the black
queen on a dark one. -/
theorem Board.isLight_of_initial_queen (h : Board.initial s = some ⟨c, .queen⟩) :
    s.IsLight ↔ c = .white := by
  revert s c; decide

/-- There are 32 pieces at the start, pawns included. -/
theorem Board.count_initial :
    (Square.all.filter fun s => (Board.initial s).isSome).length = 32 := by
  decide

/-- There are 16 pieces of each colour at the start, pawns included. -/
theorem Board.count_initial_color (c : Color) :
    (Square.all.filter fun s => (Board.initial s).map (·.color) = some c).length = 16 := by
  cases c <;> decide

/-- No square has both a white and a black starting piece. -/
theorem startingPiece_white_or_black (s : Square) :
    startingPiece .white s = none ∨ startingPiece .black s = none := by
  revert s; decide

/-- Mirroring the initial board top to bottom swaps the colours of its pieces. -/
theorem Board.initial_flip (s : Square) :
    Board.initial ⟨s.file, s.rank.rev⟩ =
      (Board.initial s).map fun pc => ⟨pc.color.other, pc.kind⟩ := by
  revert s; decide

end InitialPosition

/-! ## Notation (trusted: the FEN and UCI guards of `Chess.ChessGame` compare against these) -/

/-- The upper-case FEN letter of kind `k`: P, N, B, R, Q or K. Algebraic notation uses the same
letters but omits P. -/
def Kind.letter (k : Kind) : Char :=
  match k with
  | .pawn => 'P' | .knight => 'N' | .bishop => 'B' | .rook => 'R' | .queen => 'Q' | .king => 'K'

/-- The FEN letter of piece `pc`: its kind's letter, upper case for White and lower case for
Black. -/
def Piece.letter (pc : Piece) : Char :=
  match pc.color with
  | .white => pc.kind.letter
  | .black => pc.kind.letter.toLower

/-- The UCI letter of promotion choice `pk`: n, b, r or q. -/
def PromoKind.letter (pk : PromoKind) : Char := pk.toKind.letter.toLower

/-- Move `m` in UCI notation, such as `e2e4`, or `e7e8q` for a promotion to a queen. -/
def Move.toUCI (m : Move) : String :=
  m.src.name ++ m.dst.name ++
    match m.promo with
    | none    => ""
    | some pk => pk.letter.toString

/-- Moves print in UCI notation. -/
instance : Repr Move := ⟨fun m _ => Std.Format.text m.toUCI⟩

/-- Moves print in UCI notation. -/
instance : ToString Move := ⟨Move.toUCI⟩

/-- The castling rights `cr` as in FEN: the letters K, Q, k, q of the rights held, in that order,
or `-` if none is held. -/
def CastlingRights.letters (cr : CastlingRights) : String :=
  let table := [('K', Color.white, Wing.kingside), ('Q', .white, .queenside),
    ('k', .black, .kingside), ('q', .black, .queenside)]
  let held := (table.filter fun (_, c, w) => cr.get c w).map (·.1)
  if held.isEmpty then "-" else String.ofList held

/-! ## Display (untrusted: nothing in the specification reads it) -/

/-- The name of colour `c`: White or Black. -/
def Color.name (c : Color) : String :=
  match c with
  | .white => "White"
  | .black => "Black"

/-- Rank `r` of board `b` as one line of a diagram: the rank's number, then the eight squares from
the a-file to the h-file, each shown as its piece's letter or `.` if empty, separated by spaces. -/
def Board.rankLine (b : Board) (r : Fin 8) : String :=
  String.intercalate " " (toString (r.val + 1) ::
    (List.finRange 8).map fun f => ((b ⟨f, r⟩).map (·.letter.toString)).getD ".")

/-- Board `b` as a text diagram: one line per rank from rank 8 down to rank 1, then a line of file
letters. -/
def Board.diagram (b : Board) : String :=
  String.intercalate "\n" ((List.finRange 8).reverse.map b.rankLine ++ ["  a b c d e f g h"])

/-- Boards print as diagrams. -/
instance : Repr Board := ⟨fun b _ => Std.Format.text b.diagram⟩

/-- Position `p` as a text diagram: the board's diagram, then a line giving the side to move, the
castling rights and the en passant target. -/
def Position.diagram (p : Position) : String :=
  p.board.diagram ++ "\n" ++ p.turn.name ++ " to move, castling " ++ p.castling.letters ++
    ", en passant " ++ (p.epTarget.map Square.name).getD "-"

/-- Positions print as diagrams. -/
instance : Repr Position := ⟨fun p _ => Std.Format.text p.diagram⟩

/-- Positions print as diagrams. -/
instance : ToString Position := ⟨Position.diagram⟩

/-! ## Tests -/

-- `Board.set` on a literal: the queen is on e4 (`⟨4, 3⟩`) and nothing is on e5 (`⟨4, 4⟩`).
example : (Board.empty.set ⟨4, 3⟩ (some ⟨.white, .queen⟩)) ⟨4, 3⟩ = some ⟨.white, .queen⟩ := rfl
example : (Board.empty.set ⟨4, 3⟩ (some ⟨.white, .queen⟩)) ⟨4, 4⟩ = none := rfl

-- The packed initial board. Read right to left: a1–h1 are 4 2 3 5 6 3 2 4 (R N B Q K B N R),
-- then eight white pawns, 32 empty squares, eight black pawns, and a8–h8 A 8 9 B C 9 8 A.
example : Board.pack Board.initial =
    0xA89CB98A77777777000000000000000000000000000000001111111142365324 := by
  decide

-- The literal round trip, kernel-checked.
example : Position.initial =
    ⟨Board.unpack 0xA89CB98A77777777000000000000000000000000000000001111111142365324,
      .white, .full, none⟩ := by
  decide +kernel

-- A `set` chain against a literal, kernel-checked: the board after 1. e4 (e2 is `⟨4, 1⟩`, e4 is
-- `⟨4, 3⟩`), the checkpoint pattern of DESIGN §7.4.
example : (Board.initial.set ⟨4, 1⟩ none).set ⟨4, 3⟩ (some ⟨.white, .pawn⟩) =
    Board.unpack 0xA89CB98A77777777000000000000000000010000000000001110111142365324 := by
  decide +kernel

example : Piece.ofCode 13 = none := by decide

-- Positions that differ only in the side to move are different.
example : Position.initial ≠ { Position.initial with turn := .black } := by decide

-- Castling rights.
example : CastlingRights.full.revokeAll .white = ⟨false, false, true, true⟩ := by decide
#guard CastlingRights.full.letters == "KQkq"
#guard (CastlingRights.full.revoke .black .queenside).letters == "KQk"
#guard CastlingRights.none.letters == "-"

-- Moves: e7e8q (`⟨4, 6⟩` to `⟨4, 7⟩`), e2e4, and an `∃` decided through `Move.decidableExists`.
#guard (Move.mk ⟨4, 6⟩ ⟨4, 7⟩ (some .queen)).toUCI == "e7e8q"
#guard toString (Move.mk ⟨4, 1⟩ ⟨4, 3⟩ none) == "e2e4"
example : ∃ m : Move, m.src = ⟨0, 0⟩ ∧ m.dst = ⟨0, 1⟩ ∧ m.promo = some .rook := by decide

-- The diagram.
#guard Position.initial.diagram == "8 r n b q k b n r\n7 p p p p p p p p\n\
  6 . . . . . . . .\n5 . . . . . . . .\n4 . . . . . . . .\n3 . . . . . . . .\n\
  2 P P P P P P P P\n1 R N B Q K B N R\n  a b c d e f g h\n\
  White to move, castling KQkq, en passant -"
#guard ({ Position.initial with turn := .black, castling := .none, epTarget := some ⟨4, 2⟩ }
  ).diagram.endsWith "Black to move, castling -, en passant e3"

-- Bounded quantifiers are decided by the list, not by the low-priority whole-type instances.
example (l : List Move) (P : Move → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∀ m ∈ l, P m)) = List.decidableBAll P l := rfl
example (l : List Move) (P : Move → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∃ m ∈ l, P m)) = List.decidableBEx P l := rfl
example (l : List CastlingRights) (P : CastlingRights → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∀ cr ∈ l, P cr)) = List.decidableBAll P l := rfl
example (l : List CastlingRights) (P : CastlingRights → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∃ cr ∈ l, P cr)) = List.decidableBEx P l := rfl

end Chess
