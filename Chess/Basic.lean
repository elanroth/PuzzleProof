/-!
# Basic

The finite vocabulary of chess and the geometry of the board. Specification:
`docs/spec/Basic.md`; every definition below carries the docstring given there.

## Main definitions

* `Color`, `Kind`, `PromoKind`, `Piece`, `Direction`, `Wing`: the finite types, each with a list
  `all` of its values and decidable `∀`/`∃`.
* `Square`: a file and a rank, each a `Fin 8`; `Square.index` and `Square.ofIndex` number the
  squares 0 (a1) to 63 (h8).
* `Square.offset`: the square a given number of files and ranks away, if on the board. Every
  other geometric notion is built from it.
* `Square.shift` (the square `i` steps away in a direction) and `Square.ray` (the list of squares
  in a direction up to the edge).
* `knightJumps`, `Color.forward`, `Color.homeRank`, `Square.relRank`.
* `kingHome`, `rookHome`, `kingCastleSquare`, `rookCastleSquare`, `betweenKingAndRook`.

## Main statements

* (R1) `Square.ofIndex_index`, `Square.index_ofIndex`: numbering squares is a bijection with
  `Fin 64`.
* (R2) `mem_all` and `all_nodup` for every finite type: each list names every value once.
* `Square.offset_eq_some_iff`: the characterization through which every proof about offsets goes.
* `Square.mem_ray_iff`: the generator's rays agree with the specification's shifts.
* `shift_kingHome_two`, `shift_kingHome_one`: the castling squares are the ones FIDE 3.8.2
  describes.

## Implementation notes

* Two `Fin 8` coordinates, not `Fin 64`: "on the board" is a type, and `Fin 64` survives only as
  the proved bijection `index`.
* One primitive, `Square.offset`, with `Int` steps and an `Option` result, characterized by one
  lemma, `Square.offset_eq_some_iff`. Proofs rewrite with it and finish with `omega`.
* Sliders have two forms: `Square.shift` (index form, used by the specification) and
  `Square.ray` (list form, used by the generator), joined by `Square.getElem?_ray`.
* The small enumerations get their decidable quantifiers from one pair of helpers,
  `decidableForallOfMemAll` and `decidableExistsOfMemAll`, applied to their `all` and `mem_all`.
* Every whole-type quantifier instance (`∀ s, P s` over `Square`, `Piece`, …) has
  `priority := low`. Otherwise it would also match a bounded quantifier `∀ s ∈ l, P s` (which is
  `∀ s, s ∈ l → P s`) and decide it by sweeping the whole type instead of the list `l`; with low
  priority core's `List.decidableBAll` and `List.decidableBEx` win (`docs/reviews/Basic.md`, C1).
-/

namespace Chess

/-! ## Decidable quantifiers from a complete list -/

/-- `∀ a, P a` is decided by checking `P` on every entry of `all`, a list that contains every
value (`mem_all`). -/
def decidableForallOfMemAll {α : Type} (all : List α) (mem_all : ∀ a, a ∈ all)
    (P : α → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a ∈ all, P a) ⟨fun h a => h a (mem_all a), fun h a _ => h a⟩

/-- `∃ a, P a` is decided by searching the entries of `all`, a list that contains every value
(`mem_all`). -/
def decidableExistsOfMemAll {α : Type} (all : List α) (mem_all : ∀ a, a ∈ all)
    (P : α → Prop) [DecidablePred P] : Decidable (∃ a, P a) :=
  decidable_of_iff (∃ a ∈ all, P a) ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, mem_all a, h⟩⟩

/-! ## Colours -/

/-- The colour of a player and of that player's pieces: White or Black (FIDE 2.2). -/
inductive Color
  | white
  | black
  deriving DecidableEq, Repr, Inhabited

/-- The opponent of colour `c`. -/
def Color.other (c : Color) : Color :=
  match c with
  | .white => .black
  | .black => .white

/-- Both colours, White first. -/
def Color.all : List Color := [.white, .black]

namespace Color

variable {c c' : Color}

/-- (R2) Every colour is listed. -/
theorem mem_all (c : Color) : c ∈ Color.all := by
  cases c <;> decide

/-- (R2) No colour is listed twice. -/
theorem all_nodup : Color.all.Nodup := by decide

/-- `∀` over colours is decided by checking both colours in `Color.all`. -/
instance (priority := low) decidableForall (P : Color → Prop) [DecidablePred P] :
    Decidable (∀ c, P c) :=
  decidableForallOfMemAll Color.all mem_all P

/-- `∃` over colours is decided by searching both colours in `Color.all`. -/
instance (priority := low) decidableExists (P : Color → Prop) [DecidablePred P] :
    Decidable (∃ c, P c) :=
  decidableExistsOfMemAll Color.all mem_all P

/-- The opponent of White is Black. -/
@[simp] theorem other_white : Color.white.other = .black := rfl
/-- The opponent of Black is White. -/
@[simp] theorem other_black : Color.black.other = .white := rfl

/-- The opponent's opponent is the colour itself. -/
@[simp] theorem other_other (c : Color) : c.other.other = c := by
  cases c <;> rfl

/-- No colour is its own opponent. -/
@[simp] theorem other_ne_self (c : Color) : c.other ≠ c := by
  cases c <;> decide

/-- No colour is its own opponent. -/
@[simp] theorem self_ne_other (c : Color) : c ≠ c.other := by
  cases c <;> decide

/-- Two colours with the same opponent are equal. -/
@[simp] theorem other_inj : c.other = c'.other ↔ c = c' := by
  cases c <;> cases c' <;> decide

/-- `c` is the opponent of `c'` exactly when it differs from `c'`, since there are only two
colours. -/
theorem eq_other_iff_ne : c = c'.other ↔ c ≠ c' := by
  cases c <;> cases c' <;> decide

end Color

/-! ## Kinds, promotion choices, pieces -/

/-- The kind of a piece, without its colour (FIDE 2.2). -/
inductive Kind
  | pawn
  | knight
  | bishop
  | rook
  | queen
  | king
  deriving DecidableEq, Repr, Inhabited

/-- All six kinds, in the order pawn, knight, bishop, rook, queen, king. -/
def Kind.all : List Kind := [.pawn, .knight, .bishop, .rook, .queen, .king]

namespace Kind

/-- (R2) Every kind is listed. -/
theorem mem_all (k : Kind) : k ∈ Kind.all := by
  cases k <;> decide

/-- (R2) No kind is listed twice. -/
theorem all_nodup : Kind.all.Nodup := by decide

/-- `∀` over kinds is decided by checking the six kinds in `Kind.all`. -/
instance (priority := low) decidableForall (P : Kind → Prop) [DecidablePred P] :
    Decidable (∀ k, P k) :=
  decidableForallOfMemAll Kind.all mem_all P

/-- `∃` over kinds is decided by searching the six kinds in `Kind.all`. -/
instance (priority := low) decidableExists (P : Kind → Prop) [DecidablePred P] :
    Decidable (∃ k, P k) :=
  decidableExistsOfMemAll Kind.all mem_all P

end Kind

/-- What a pawn may be promoted to: a knight, bishop, rook or queen (FIDE 3.7.3.3). -/
inductive PromoKind
  | knight
  | bishop
  | rook
  | queen
  deriving DecidableEq, Repr, Inhabited

/-- The kind of piece that promotion choice `pk` produces. -/
def PromoKind.toKind (pk : PromoKind) : Kind :=
  match pk with
  | .knight => .knight
  | .bishop => .bishop
  | .rook   => .rook
  | .queen  => .queen

/-- All four promotion choices. -/
def PromoKind.all : List PromoKind := [.knight, .bishop, .rook, .queen]

namespace PromoKind

variable {pk pk' : PromoKind}

/-- (R2) Every promotion choice is listed. -/
theorem mem_all (pk : PromoKind) : pk ∈ PromoKind.all := by
  cases pk <;> decide

/-- (R2) No promotion choice is listed twice. -/
theorem all_nodup : PromoKind.all.Nodup := by decide

/-- `∀` over promotion choices is decided by checking the four choices in `PromoKind.all`. -/
instance (priority := low) decidableForall (P : PromoKind → Prop) [DecidablePred P] :
    Decidable (∀ pk, P pk) :=
  decidableForallOfMemAll PromoKind.all mem_all P

/-- `∃` over promotion choices is decided by searching the four choices in `PromoKind.all`. -/
instance (priority := low) decidableExists (P : PromoKind → Prop) [DecidablePred P] :
    Decidable (∃ pk, P pk) :=
  decidableExistsOfMemAll PromoKind.all mem_all P

/-- Different promotion choices give different kinds. -/
@[simp] theorem toKind_inj : pk.toKind = pk'.toKind ↔ pk = pk' := by
  cases pk <;> cases pk' <;> decide

/-- A promotion never produces a pawn (FIDE 3.7.3.3). -/
@[simp] theorem toKind_ne_pawn (pk : PromoKind) : pk.toKind ≠ .pawn := by
  cases pk <;> decide

/-- A promotion never produces a king (FIDE 3.7.3.3). -/
@[simp] theorem toKind_ne_king (pk : PromoKind) : pk.toKind ≠ .king := by
  cases pk <;> decide

end PromoKind

/-- A piece: a colour and a kind, for example a white knight. -/
structure Piece where
  /-- The colour of the piece. -/
  color : Color
  /-- The kind of the piece. -/
  kind : Kind
  deriving DecidableEq, Repr, Inhabited

/-- All twelve pieces, the white ones first. -/
def Piece.all : List Piece := Color.all.flatMap fun c => Kind.all.map (Piece.mk c)

/-- The piece that `pc` becomes after a move with promotion choice `o`: `pc` itself if `o` is
`none`, and the piece of `pc`'s colour and of kind `pk.toKind` if `o` is `some pk`. -/
def Piece.promote (pc : Piece) (o : Option PromoKind) : Piece :=
  match o with
  | none    => pc
  | some pk => ⟨pc.color, pk.toKind⟩

namespace Piece

/-- (R2) Every piece is listed. -/
theorem mem_all (pc : Piece) : pc ∈ Piece.all :=
  List.mem_flatMap.mpr
    ⟨pc.color, pc.color.mem_all, List.mem_map.mpr ⟨pc.kind, pc.kind.mem_all, rfl⟩⟩

/-- (R2) No piece is listed twice. -/
theorem all_nodup : Piece.all.Nodup := by decide

/-- `∀` over pieces is decided through the colour and kind quantifiers, not a list. -/
instance (priority := low) decidableForall (P : Piece → Prop) [DecidablePred P] :
    Decidable (∀ pc, P pc) :=
  decidable_of_iff (∀ c k, P ⟨c, k⟩) ⟨fun h pc => h pc.color pc.kind, fun h c k => h ⟨c, k⟩⟩

/-- `∃` over pieces is decided through the colour and kind quantifiers, not a list. -/
instance (priority := low) decidableExists (P : Piece → Prop) [DecidablePred P] :
    Decidable (∃ pc, P pc) :=
  decidable_of_iff (∃ c k, P ⟨c, k⟩)
    ⟨fun ⟨c, k, h⟩ => ⟨⟨c, k⟩, h⟩, fun ⟨pc, h⟩ => ⟨pc.color, pc.kind, h⟩⟩

/-- Without a promotion choice the piece is unchanged. -/
@[simp] theorem promote_none (pc : Piece) : pc.promote none = pc := rfl

/-- With choice `pk` the piece keeps its colour and takes kind `pk.toKind`. -/
@[simp] theorem promote_some (pc : Piece) (pk : PromoKind) :
    pc.promote (some pk) = ⟨pc.color, pk.toKind⟩ := rfl

/-- Promotion never changes colour. -/
@[simp] theorem color_promote (pc : Piece) (o : Option PromoKind) :
    (pc.promote o).color = pc.color := by
  cases o <;> rfl

end Piece

/-! ## Squares -/

/-- A square of the board, given by its file (0 is the a-file, 7 the h-file) and its rank (0 is
rank 1, White's back rank; 7 is rank 8). -/
@[ext] structure Square where
  /-- The file: 0 is the a-file, 7 the h-file. -/
  file : Fin 8
  /-- The rank: 0 is rank 1, 7 is rank 8. -/
  rank : Fin 8
  deriving DecidableEq, Repr, Inhabited

/-- The number of square `s`, from 0 for a1 to 63 for h8: `8 · rank + file`. -/
def Square.index (s : Square) : Fin 64 :=
  ⟨8 * s.rank.val + s.file.val, by omega⟩

/-- The square with number `i`: file `i % 8`, rank `i / 8`. -/
def Square.ofIndex (i : Fin 64) : Square :=
  ⟨⟨i.val % 8, by omega⟩, ⟨i.val / 8, by omega⟩⟩

/-- All 64 squares in index order: a1, b1, …, h1, a2, …, h8. -/
def Square.all : List Square := (List.finRange 64).map Square.ofIndex

/-- The square `s` is light: its file and rank add up to an odd number. (a1 is dark.) -/
def Square.IsLight (s : Square) : Prop := (s.file.val + s.rank.val) % 2 = 1

namespace Square

variable {s t : Square}

/-- Whether a square is light is decided by computing the parity of file plus rank. -/
instance : DecidablePred Square.IsLight :=
  fun s => inferInstanceAs (Decidable ((s.file.val + s.rank.val) % 2 = 1))

/-- `∀` over squares is decided through the core quantifiers over the two `Fin 8`
coordinates, not through the 64-element list (which exceeds `maxRecDepth` under `decide`). -/
instance (priority := low) decidableForall (P : Square → Prop) [DecidablePred P] :
    Decidable (∀ s, P s) :=
  decidable_of_iff (∀ f r : Fin 8, P ⟨f, r⟩) ⟨fun h s => h s.file s.rank, fun h f r => h ⟨f, r⟩⟩

/-- `∃` over squares is decided through the core quantifiers over the two `Fin 8`
coordinates. -/
instance (priority := low) decidableExists (P : Square → Prop) [DecidablePred P] :
    Decidable (∃ s, P s) :=
  decidable_of_iff (∃ f r : Fin 8, P ⟨f, r⟩)
    ⟨fun ⟨f, r, h⟩ => ⟨⟨f, r⟩, h⟩, fun ⟨s, h⟩ => ⟨s.file, s.rank, h⟩⟩

/-- The index is `8 · rank + file`. -/
@[simp] theorem val_index (s : Square) : s.index.val = 8 * s.rank.val + s.file.val := rfl

/-- The file of square number `i` is `i % 8`. -/
@[simp] theorem val_file_ofIndex (i : Fin 64) : (ofIndex i).file.val = i.val % 8 := rfl

/-- The rank of square number `i` is `i / 8`. -/
@[simp] theorem val_rank_ofIndex (i : Fin 64) : (ofIndex i).rank.val = i.val / 8 := rfl

/-- (R1) Numbering a square and taking the square of that number gives the square back. -/
@[simp] theorem ofIndex_index (s : Square) : ofIndex s.index = s := by
  ext <;> simp only [val_file_ofIndex, val_rank_ofIndex, val_index] <;> omega

/-- (R1) Taking the square of a number and numbering it gives the number back. -/
@[simp] theorem index_ofIndex (i : Fin 64) : (ofIndex i).index = i := by
  ext; simp only [val_index, val_file_ofIndex, val_rank_ofIndex]; omega

/-- Two squares with the same number are equal. -/
@[simp] theorem index_inj : s.index = t.index ↔ s = t :=
  ⟨fun h => by rw [← ofIndex_index s, h, ofIndex_index], congrArg index⟩

/-- (R2) Every square is listed. -/
theorem mem_all (s : Square) : s ∈ Square.all :=
  List.mem_map.mpr ⟨s.index, List.mem_finRange _, ofIndex_index s⟩

/-- (R2) No square is listed twice. -/
theorem all_nodup : Square.all.Nodup := by decide +kernel

/-- The list of all squares has 64 entries. -/
@[simp] theorem length_all : Square.all.length = 64 := by
  simp only [Square.all, List.length_map, List.length_finRange]

/-- The near right-hand corner is light (FIDE 2.1): h1 is light. -/
theorem isLight_h1 : (Square.mk 7 0).IsLight := by decide

/-- a8, the near right-hand corner for Black, is light. -/
theorem isLight_a8 : (Square.mk 0 7).IsLight := by decide

/-- a1 is dark. -/
theorem not_isLight_a1 : ¬ (Square.mk 0 0).IsLight := by decide

/-- Exactly 32 squares are light. -/
theorem count_isLight : (Square.all.filter fun s => decide s.IsLight).length = 32 := by
  decide +kernel

end Square

/-! ## Offsets: the one geometric primitive -/

/-- The coordinate `δ` steps from the coordinate `x`, if it is still between 0 and 7. -/
private def Square.addCoord? (x : Fin 8) (δ : Int) : Option (Fin 8) :=
  if h : 0 ≤ (x : Int) + δ ∧ (x : Int) + δ < 8 then some ⟨((x : Int) + δ).toNat, by omega⟩
  else none

/-- The square `df` files and `dr` ranks away from `s`, or `none` if that is off the board.
Positive `df` is towards the h-file, positive `dr` towards rank 8. -/
def Square.offset (s : Square) (df dr : Int) : Option Square :=
  match Square.addCoord? s.file df, Square.addCoord? s.rank dr with
  | some f, some r => some ⟨f, r⟩
  | _, _ => none

namespace Square

variable {s t u : Square} {df dr df' dr' : Int}

/-- Adding `δ` to `x` gives `y` exactly when `y = x + δ` as integers. -/
private theorem addCoord?_eq_some_iff {x y : Fin 8} {δ : Int} :
    addCoord? x δ = some y ↔ (y : Int) = x + δ := by
  unfold addCoord?
  split <;> simp [Fin.ext_iff] <;> omega

/-- Adding `δ` to `x` leaves the board exactly when `x + δ` is not in 0..7. -/
private theorem addCoord?_eq_none_iff {x : Fin 8} {δ : Int} :
    addCoord? x δ = none ↔ ¬ (0 ≤ (x : Int) + δ ∧ (x : Int) + δ < 8) := by
  unfold addCoord?
  split <;> simp_all

/-- **The offset of `s` by `(df, dr)` is `t` exactly when `t`'s file is `s`'s file plus `df`
and `t`'s rank is `s`'s rank plus `dr`.** Other proofs use this lemma instead of unfolding
`offset`. -/
theorem offset_eq_some_iff :
    s.offset df dr = some t ↔ (t.file : Int) = s.file + df ∧ (t.rank : Int) = s.rank + dr := by
  unfold offset
  cases hf : addCoord? s.file df <;> cases hr : addCoord? s.rank dr <;>
    simp_all [addCoord?_eq_some_iff, addCoord?_eq_none_iff, Square.ext_iff, Fin.ext_iff] <;> omega

/-- The offset is on the board exactly when both new coordinates lie in 0..7. -/
theorem isSome_offset_iff :
    (s.offset df dr).isSome ↔
      0 ≤ (s.file : Int) + df ∧ (s.file : Int) + df < 8 ∧
      0 ≤ (s.rank : Int) + dr ∧ (s.rank : Int) + dr < 8 := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    have := offset_eq_some_iff.mp ht
    omega
  · intro ⟨h0, h1, h2, h3⟩
    refine Option.isSome_iff_exists.mpr
      ⟨⟨⟨(s.file + df).toNat, by omega⟩, ⟨(s.rank + dr).toNat, by omega⟩⟩, ?_⟩
    rw [offset_eq_some_iff]
    dsimp only
    omega

/-- Offsetting by nothing stays put. -/
@[simp] theorem offset_zero (s : Square) : s.offset 0 0 = some s := by
  rw [offset_eq_some_iff]; omega

/-- Two offsets in a row are one offset by the sum, provided the first stays on the board. -/
theorem offset_offset (h : s.offset df dr = some t) :
    t.offset df' dr' = s.offset (df + df') (dr + dr') := by
  rw [offset_eq_some_iff] at h
  exact Option.ext fun u => by rw [offset_eq_some_iff, offset_eq_some_iff]; omega

/-- Offsets can be undone: `t` is `(df, dr)` from `s` exactly when `s` is `(−df, −dr)` from
`t`. -/
theorem offset_eq_some_iff_neg : s.offset df dr = some t ↔ t.offset (-df) (-dr) = some s := by
  rw [offset_eq_some_iff, offset_eq_some_iff]; omega

/-- A nonzero offset never returns the same square. -/
theorem offset_ne_self (hd : df ≠ 0 ∨ dr ≠ 0) (h : s.offset df dr = some t) : t ≠ s := by
  rintro rfl
  rw [offset_eq_some_iff] at h
  omega

/-- Two offsets from the same square that reach the same target have the same steps. -/
theorem steps_eq_of_offset_eq (h : s.offset df dr = some t) (h' : s.offset df' dr' = some t) :
    df = df' ∧ dr = dr' := by
  rw [offset_eq_some_iff] at h h'
  omega

/-- Two squares that reach the same target by the same offset are equal. -/
theorem eq_of_offset_eq (h : s.offset df dr = some t) (h' : u.offset df dr = some t) :
    s = u := by
  rw [offset_eq_some_iff] at h h'
  ext <;> omega

/-- An offset with no file step stays on the file. -/
theorem file_eq_of_offset_zero (h : s.offset 0 dr = some t) : s.file = t.file := by
  rw [offset_eq_some_iff] at h
  exact Fin.ext (by omega)

/-- An offset by `(df, dr)` keeps the square's colour exactly when `df + dr` is even. (Here `%`
is `Int.emod`, so `(-1) % 2 = 1`.) -/
theorem isLight_offset_iff (h : s.offset df dr = some t) :
    (t.IsLight ↔ s.IsLight) ↔ (df + dr) % 2 = 0 := by
  rw [offset_eq_some_iff] at h
  simp only [IsLight]
  omega

end Square

/-! ## Directions, shifts, rays, knight jumps -/

/-- One of the eight compass directions on the board. North is towards rank 8 (up the board from
White's side), east is towards the h-file. -/
inductive Direction
  | north
  | east
  | south
  | west
  | northEast
  | southEast
  | southWest
  | northWest
  deriving DecidableEq, Repr, Inhabited

/-- The file step of direction `d`: +1 for the three directions with an eastward component (east,
northEast, southEast), −1 for the three with a westward one, 0 for north and south. -/
def Direction.df (d : Direction) : Int :=
  match d with
  | .north => 0 | .east => 1 | .south => 0 | .west => -1
  | .northEast => 1 | .southEast => 1 | .southWest => -1 | .northWest => -1

/-- The rank step of direction `d`: +1 for the three directions with a northward component
(north, northEast, northWest), −1 for the three with a southward one, 0 for east and west. -/
def Direction.dr (d : Direction) : Int :=
  match d with
  | .north => 1 | .east => 0 | .south => -1 | .west => 0
  | .northEast => 1 | .southEast => -1 | .southWest => -1 | .northWest => 1

/-- The direction pointing the opposite way to `d`. -/
def Direction.opposite (d : Direction) : Direction :=
  match d with
  | .north => .south | .east => .west | .south => .north | .west => .east
  | .northEast => .southWest | .southEast => .northWest
  | .southWest => .northEast | .northWest => .southEast

/-- The four directions along a file or a rank: those a rook moves in (FIDE 3.3). -/
def Direction.orthogonals : List Direction := [.north, .east, .south, .west]

/-- The four diagonal directions: those a bishop moves in (FIDE 3.2). -/
def Direction.diagonals : List Direction := [.northEast, .southEast, .southWest, .northWest]

/-- All eight directions: those a queen moves in, and those a king steps in (FIDE 3.4, 3.8.1). -/
def Direction.all : List Direction := Direction.orthogonals ++ Direction.diagonals

namespace Direction

variable {d d' : Direction}

/-- (R2) Every direction is listed. -/
theorem mem_all (d : Direction) : d ∈ Direction.all := by
  cases d <;> decide

/-- (R2) No direction is listed twice. -/
theorem all_nodup : Direction.all.Nodup := by decide

/-- `∀` over directions is decided by checking the eight directions in `Direction.all`. -/
instance (priority := low) decidableForall (P : Direction → Prop) [DecidablePred P] :
    Decidable (∀ d, P d) :=
  decidableForallOfMemAll Direction.all mem_all P

/-- `∃` over directions is decided by searching the eight directions in `Direction.all`. -/
instance (priority := low) decidableExists (P : Direction → Prop) [DecidablePred P] :
    Decidable (∃ d, P d) :=
  decidableExistsOfMemAll Direction.all mem_all P

/-- The opposite of the opposite is the direction itself. -/
@[simp] theorem opposite_opposite (d : Direction) : d.opposite.opposite = d := by
  cases d <;> rfl

/-- The opposite direction negates the file step. -/
@[simp] theorem df_opposite (d : Direction) : d.opposite.df = -d.df := by
  cases d <;> rfl

/-- The opposite direction negates the rank step. -/
@[simp] theorem dr_opposite (d : Direction) : d.opposite.dr = -d.dr := by
  cases d <;> rfl

/-- A direction is determined by its two steps. -/
theorem ext_iff_steps : d = d' ↔ d.df = d'.df ∧ d.dr = d'.dr := by
  cases d <;> cases d' <;> decide

/-- The file step is −1, 0 or 1. -/
theorem natAbs_df_le_one (d : Direction) : d.df.natAbs ≤ 1 := by
  cases d <;> decide

/-- The rank step is −1, 0 or 1. -/
theorem natAbs_dr_le_one (d : Direction) : d.dr.natAbs ≤ 1 := by
  cases d <;> decide

/-- At least one step of a direction is nonzero. -/
theorem df_ne_zero_or_dr_ne_zero (d : Direction) : d.df ≠ 0 ∨ d.dr ≠ 0 := by
  cases d <;> decide

/-- Orthogonal directions are those with a zero step. -/
theorem mem_orthogonals_iff : d ∈ Direction.orthogonals ↔ d.df = 0 ∨ d.dr = 0 := by
  cases d <;> decide

/-- Diagonal directions are those with two nonzero steps. -/
theorem mem_diagonals_iff : d ∈ Direction.diagonals ↔ d.df ≠ 0 ∧ d.dr ≠ 0 := by
  cases d <;> decide

/-- A direction's opposite is orthogonal exactly when the direction is. -/
theorem opposite_mem_orthogonals : d.opposite ∈ orthogonals ↔ d ∈ orthogonals := by
  cases d <;> decide

/-- A direction's opposite is diagonal exactly when the direction is. -/
theorem opposite_mem_diagonals : d.opposite ∈ diagonals ↔ d ∈ diagonals := by
  cases d <;> decide

/-- Two directions along a rank (neither changes rank) are equal or opposite. -/
theorem eq_or_eq_opposite_of_dr_eq_zero (hd : d.dr = 0) (hd' : d'.dr = 0) :
    d' = d ∨ d' = d.opposite := by
  revert hd hd'; cases d <;> cases d' <;> decide

end Direction

/-- The directions along which a piece of kind `k` moves any number of squares without passing
over another piece (FIDE 3.2–3.4): none for pawns, knights and kings. -/
def Kind.slideDirections (k : Kind) : List Direction :=
  match k with
  | .bishop => Direction.diagonals
  | .rook   => Direction.orthogonals
  | .queen  => Direction.all
  | .pawn | .knight | .king => []

/-- A queen slides in exactly the directions of a rook and of a bishop (FIDE 3.4). -/
theorem Kind.mem_slideDirections_queen {d : Direction} :
    d ∈ Kind.queen.slideDirections ↔
      d ∈ Kind.rook.slideDirections ∨ d ∈ Kind.bishop.slideDirections := by
  cases d <;> decide

/-- A piece slides in a direction exactly when it slides in the opposite one. -/
theorem Kind.opposite_mem_slideDirections {k : Kind} {d : Direction} :
    d.opposite ∈ k.slideDirections ↔ d ∈ k.slideDirections := by
  cases k <;> cases d <;> decide

/-- The square `i` steps from `s` in direction `d`, or `none` if that is off the board. -/
def Square.shift (s : Square) (d : Direction) (i : Nat) : Option Square :=
  s.offset ((i : Int) * d.df) ((i : Int) * d.dr)

/-- The squares met by stepping from `s` in direction `d` at most `n` times, nearest first,
stopping at the edge of the board; `s` itself is not included. -/
def Square.walk (s : Square) (d : Direction) (n : Nat) : List Square :=
  match n with
  | 0 => []
  | m + 1 =>
    match s.shift d 1 with
    | none   => []
    | some t => t :: t.walk d m

/-- The squares met stepping from `s` in direction `d`, up to and including the last square on
the board, nearest first, `s` excluded; empty if `s` is on that edge. -/
def Square.ray (s : Square) (d : Direction) : List Square := s.walk d 7

/-- The eight (file, rank) offsets of a knight's move: two squares along a file or rank and one
across (FIDE 3.6). -/
def knightJumps : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

namespace Square

variable {s t : Square} {d d' : Direction} {i j : Nat}

/-- Zero steps stay put. -/
@[simp] theorem shift_zero : s.shift d 0 = some s := by
  simp [shift]

/-- One step is the offset by the direction's steps. -/
theorem shift_one : s.shift d 1 = s.offset d.df d.dr := by
  simp [shift]

/-- `t` is `i` steps from `s` in direction `d` exactly when the coordinates differ by `i` times
the steps. -/
theorem shift_eq_some_iff :
    s.shift d i = some t ↔
      (t.file : Int) = s.file + i * d.df ∧ (t.rank : Int) = s.rank + i * d.dr :=
  offset_eq_some_iff

/-- The shift is on the board exactly when both new coordinates lie in 0..7. -/
theorem isSome_shift_iff :
    (s.shift d i).isSome ↔
      0 ≤ (s.file : Int) + i * d.df ∧ (s.file : Int) + i * d.df < 8 ∧
      0 ≤ (s.rank : Int) + i * d.dr ∧ (s.rank : Int) + i * d.dr < 8 :=
  isSome_offset_iff

/-- Eight or more steps in any direction leave the board. -/
theorem shift_eq_none_of_eight_le (h : 8 ≤ i) : s.shift d i = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_shift_iff]
  cases d <;> simp [Direction.df, Direction.dr] <;> omega

/-- Shifts compose: if `t` is `i` steps from `s`, then `j` steps from `t` is `i + j` steps from
`s`. -/
theorem shift_add (h : s.shift d i = some t) : t.shift d j = s.shift d (i + j) := by
  simp only [shift] at h ⊢
  rw [offset_offset h, Int.natCast_add, Int.add_mul, Int.add_mul]

/-- If the square `i` steps away is on the board, so is every square `j ≤ i` steps away (DESIGN
§5.2: a square between two on-board squares is on the board). -/
theorem isSome_shift_of_le (hji : j ≤ i) (h : (s.shift d i).isSome) : (s.shift d j).isSome := by
  rw [isSome_shift_iff] at h ⊢
  cases d <;> simp [Direction.df, Direction.dr] at h ⊢ <;> omega

/-- Once off the board, further steps stay off. -/
theorem shift_eq_none_of_le (hji : j ≤ i) (h : s.shift d j = none) : s.shift d i = none := by
  rw [← Option.not_isSome_iff_eq_none] at h ⊢
  exact fun h' => h (isSome_shift_of_le hji h')

/-- One more step is the next step from where `i` steps led. -/
theorem shift_succ : s.shift d (i + 1) = (s.shift d i).bind (·.shift d 1) := by
  cases h : s.shift d i with
  | some t => exact (shift_add h).symm
  | none => exact shift_eq_none_of_le (Nat.le_succ i) h

/-- **Symmetry:** `t` is `i` steps from `s` in direction `d` exactly when `s` is `i` steps from
`t` in the opposite direction. -/
theorem shift_eq_some_iff_opposite : s.shift d i = some t ↔ t.shift d.opposite i = some s := by
  rw [shift_eq_some_iff, shift_eq_some_iff, Direction.df_opposite, Direction.dr_opposite,
    Int.mul_neg, Int.mul_neg]
  omega

/-- **The in-between squares match up:** if `t` is `i` steps from `s`, then for `j ≤ i` the
square `j` steps from `s` is the square `i − j` steps back from `t`. -/
theorem shift_eq_shift_opposite (h : s.shift d i = some t) (hji : j ≤ i) :
    s.shift d j = t.shift d.opposite (i - j) := by
  have hj : (s.shift d j).isSome := isSome_shift_of_le hji (by simp [h])
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hj
  rw [hu, eq_comm, ← shift_eq_some_iff_opposite, shift_add hu, Nat.add_sub_cancel' hji, h]

/-- A positive number of steps never returns to the start. -/
theorem shift_ne_self (hi : 0 < i) : s.shift d i ≠ some s := by
  rw [Ne, shift_eq_some_iff]
  cases d <;> simp [Direction.df, Direction.dr] <;> omega

/-- A square reached from `s` in direction `d` is reached by one number of steps only. -/
theorem steps_eq_of_shift_eq (h : s.shift d i = some t) (h' : s.shift d j = some t) : i = j := by
  rw [shift_eq_some_iff] at h h'
  cases d <;> simp [Direction.df, Direction.dr] at h h' <;> omega

/-- A square reached from `s` by a positive number of steps is reached in one direction only,
and by one number of steps only. -/
theorem dir_eq_of_shift_eq (hi : 0 < i) (h : s.shift d i = some t) (h' : s.shift d' j = some t) :
    d = d' ∧ i = j := by
  rw [shift_eq_some_iff] at h h'
  cases d <;> cases d' <;> simp [Direction.df, Direction.dr] at h h' ⊢ <;> omega

/-- If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, and `u`
is on the first or the last rank, then `d` does not change rank. -/
theorem dr_eq_zero_of_between {u : Square} (hj0 : 0 < j) (hj : j < i) (hu : s.shift d j = some u)
    (ht : s.shift d i = some t) (hr : u.rank = 0 ∨ u.rank = 7) : d.dr = 0 := by
  replace hr : u.rank.val = 0 ∨ u.rank.val = 7 := by rcases hr with h | h <;> simp [h] <;> decide
  rw [shift_eq_some_iff] at hu ht
  have := t.rank.isLt
  cases d <;> simp [Direction.df, Direction.dr] at hu ht ⊢ <;> omega

/-- If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, and `u`
is on the a-file or the h-file, then `d` does not change file. -/
theorem df_eq_zero_of_between {u : Square} (hj0 : 0 < j) (hj : j < i) (hu : s.shift d j = some u)
    (ht : s.shift d i = some t) (hf : u.file = 0 ∨ u.file = 7) : d.df = 0 := by
  replace hf : u.file.val = 0 ∨ u.file.val = 7 := by rcases hf with h | h <;> simp [h] <;> decide
  rw [shift_eq_some_iff] at hu ht
  have := t.file.isLt
  cases d <;> simp [Direction.df, Direction.dr] at hu ht ⊢ <;> omega

/-- If `u` is `j` steps and `t` is `i` steps from `s` in direction `d`, with `0 < j < i`, then the
square `v` one step from `u` in direction `d'`, which is `d` or its opposite, is `s`, `t`, or `j'`
steps from `s` for some `j'` with `0 < j' < i`. -/
theorem shift_one_of_between {u v : Square} (hj0 : 0 < j) (hj : j < i)
    (hu : s.shift d j = some u) (ht : s.shift d i = some t) (hd' : d' = d ∨ d' = d.opposite)
    (hv : u.shift d' 1 = some v) :
    v = s ∨ v = t ∨ ∃ j', 0 < j' ∧ j' < i ∧ s.shift d j' = some v := by
  rcases hd' with rfl | rfl
  · -- One step along the line: `j + 1` steps from `s`, which is `t` when `j + 1 = i`.
    rw [shift_add hu] at hv
    by_cases e : j + 1 = i
    · subst e
      exact .inr (.inl (Option.some.inj (hv.symm.trans ht)))
    · exact .inr (.inr ⟨j + 1, by omega, by omega, hv⟩)
  · -- One step back: `j - 1` steps from `s`, which is `s` when `j = 1`.
    have h := shift_eq_shift_opposite hu (Nat.sub_le j 1)
    rw [show j - (j - 1) = 1 by omega, hv] at h
    by_cases e : j = 1
    · subst e
      exact .inl (Option.some.inj (h.symm.trans shift_zero))
    · exact .inr (.inr ⟨j - 1, by omega, by omega, h⟩)

/-- A diagonal shift keeps the square's colour. -/
theorem isLight_shift_of_mem_diagonals (hd : d ∈ Direction.diagonals)
    (h : s.shift d i = some t) : t.IsLight ↔ s.IsLight := by
  refine (isLight_offset_iff h).mpr ?_
  simp only [Direction.diagonals, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [Direction.df, Direction.dr] <;> omega

/-- Entry `i` of `s.walk d n` (counting from 0) is the square `i + 1` steps away, if `i < n`. -/
theorem getElem?_walk (s : Square) (d : Direction) (n i : Nat) :
    (s.walk d n)[i]? = if i < n then s.shift d (i + 1) else none := by
  induction n generalizing s i with
  | zero => simp [walk]
  | succ m ih =>
    cases h : s.shift d 1 with
    | none =>
      simp [walk, h, shift_eq_none_of_le (Nat.le_add_left 1 i) h]
    | some t =>
      cases i with
      | zero => simp [walk, h]
      | succ i => simp [walk, h, ih, shift_add h, Nat.add_comm 1]

/-- Entry `i` of the ray (counting from 0) is the square `i + 1` steps away. -/
theorem getElem?_ray (s : Square) (d : Direction) (i : Nat) :
    (s.ray d)[i]? = s.shift d (i + 1) := by
  rw [ray, getElem?_walk]
  split
  · rfl
  · exact (shift_eq_none_of_eight_le (by omega)).symm

/-- `t` is on the ray from `s` in direction `d` exactly when it is a positive number of steps
from `s` in that direction (the geometric half of M1). -/
theorem mem_ray_iff : t ∈ s.ray d ↔ ∃ i, 0 < i ∧ s.shift d i = some t := by
  rw [List.mem_iff_getElem?]
  simp only [getElem?_ray]
  constructor
  · rintro ⟨i, h⟩; exact ⟨i + 1, Nat.succ_pos i, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i - 1, by rwa [Nat.sub_add_cancel hi]⟩

/-- A ray does not contain its start. -/
theorem not_mem_ray_self : s ∉ s.ray d := by
  rw [mem_ray_iff]
  rintro ⟨i, hi, h⟩
  exact shift_ne_self hi h

/-- A ray has no repeats. -/
theorem ray_nodup : (s.ray d).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have hi' := getElem?_ray s d i
  have hj' := getElem?_ray s d j
  rw [List.getElem?_eq_getElem hi, heq] at hi'
  rw [List.getElem?_eq_getElem hj] at hj'
  have := steps_eq_of_shift_eq hi'.symm hj'.symm
  omega

end Square

/-- The knight jumps are exactly the offsets whose absolute values are 1 and 2 in some order. -/
theorem mem_knightJumps_iff {df dr : Int} :
    (df, dr) ∈ knightJumps ↔
      (df.natAbs = 1 ∧ dr.natAbs = 2) ∨ (df.natAbs = 2 ∧ dr.natAbs = 1) := by
  simp only [knightJumps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

/-- The jumps are closed under reversal: a knight can jump back. -/
theorem neg_mem_knightJumps {df dr : Int} (h : (df, dr) ∈ knightJumps) :
    (-df, -dr) ∈ knightJumps := by
  rw [mem_knightJumps_iff] at h ⊢
  omega

/-- There are eight distinct jumps. -/
theorem knightJumps_nodup : knightJumps.Nodup := by decide

/-- A knight jump always changes the square's colour. -/
theorem Square.isLight_iff_of_mem_knightJumps {s t : Square} {df dr : Int}
    (hj : (df, dr) ∈ knightJumps) (h : s.offset df dr = some t) : t.IsLight ↔ ¬ s.IsLight := by
  rw [mem_knightJumps_iff] at hj
  rw [offset_eq_some_iff] at h
  simp only [IsLight]
  omega

/-! ## Colour geometry -/

/-- The rank step of a pawn of colour `c`: +1 (towards rank 8) for White, −1 for Black
(FIDE 3.7.1). -/
def Color.forward (c : Color) : Int :=
  match c with
  | .white => 1
  | .black => -1

/-- The rank on which the king and rooks of colour `c` start: rank 1 for White, rank 8 for
Black. -/
def Color.homeRank (c : Color) : Fin 8 :=
  match c with
  | .white => 0
  | .black => 7

/-- The rank of `s` counted from colour `c`'s side of the board, 0 being `c`'s home rank. -/
def Square.relRank (s : Square) (c : Color) : Fin 8 :=
  match c with
  | .white => s.rank
  | .black => s.rank.rev

namespace Color

/-- White's pawns go up the board. -/
@[simp] theorem forward_white : Color.white.forward = 1 := rfl
/-- Black's pawns go down the board. -/
@[simp] theorem forward_black : Color.black.forward = -1 := rfl

/-- The two colours' pawn directions are opposite. -/
@[simp] theorem forward_other (c : Color) : c.other.forward = -c.forward := by
  cases c <;> rfl

/-- The pawn direction is a unit: it squares to 1. -/
@[simp] theorem forward_mul_forward (c : Color) : c.forward * c.forward = 1 := by
  cases c <;> rfl

/-- A pawn's rank step is not zero. -/
theorem forward_ne_zero (c : Color) : c.forward ≠ 0 := by
  cases c <;> decide

/-- A pawn's two-square rank step is not zero. -/
theorem two_mul_forward_ne_zero (c : Color) : 2 * c.forward ≠ 0 := by
  cases c <;> decide

/-- White's home rank is rank 1. -/
@[simp] theorem homeRank_white : Color.white.homeRank = 0 := rfl
/-- Black's home rank is rank 8. -/
@[simp] theorem homeRank_black : Color.black.homeRank = 7 := rfl

/-- The two home ranks are mirror images. -/
@[simp] theorem homeRank_other (c : Color) : c.other.homeRank = c.homeRank.rev := by
  cases c <;> rfl

/-- A home rank is the first or the last rank. -/
theorem homeRank_eq_zero_or_seven (c : Color) : c.homeRank = 0 ∨ c.homeRank = 7 := by
  cases c <;> simp

end Color

namespace Square

variable {s t : Square} {c : Color} {df dr : Int}

/-- For White, the relative rank is the rank. -/
@[simp] theorem relRank_white (s : Square) : s.relRank .white = s.rank := rfl
/-- For Black, the relative rank is the mirrored rank. -/
@[simp] theorem relRank_black (s : Square) : s.relRank .black = s.rank.rev := rfl

/-- Counted from the other side, the relative rank is mirrored. -/
@[simp] theorem relRank_other (s : Square) (c : Color) : s.relRank c.other = (s.relRank c).rev := by
  cases c <;> simp

/-- Relative rank 0 is the colour's home rank. -/
theorem relRank_eq_zero_iff : s.relRank c = 0 ↔ s.rank = c.homeRank := by
  revert s; cases c <;> decide

/-- Relative rank 7 is the opponent's home rank, where pawns promote. -/
theorem relRank_eq_seven_iff : s.relRank c = 7 ↔ s.rank = c.other.homeRank := by
  revert s; cases c <;> decide

/-- Any offset by `(df, dr)` changes `c`'s relative rank by `dr · c.forward`. -/
theorem relRank_of_offset (h : s.offset df dr = some t) (c : Color) :
    ((t.relRank c).val : Int) = (s.relRank c).val + dr * c.forward := by
  rw [offset_eq_some_iff] at h
  cases c <;> simp [Fin.val_rev] <;> omega

/-- An offset by `dr` ranks forward, as `c` sees the board, raises `c`'s relative rank by `dr`. -/
theorem relRank_of_offset_forward (h : s.offset df (dr * c.forward) = some t) :
    ((t.relRank c).val : Int) = (s.relRank c).val + dr := by
  rw [relRank_of_offset h c, Int.mul_assoc, Color.forward_mul_forward, Int.mul_one]

end Square

/-! ## Wings and castling squares -/

/-- The side of the board a castling goes to: kingside (towards the h-file) or queenside (towards
the a-file). -/
inductive Wing
  | kingside
  | queenside
  deriving DecidableEq, Repr, Inhabited

/-- Both wings, kingside first. -/
def Wing.all : List Wing := [.kingside, .queenside]

namespace Wing

/-- (R2) Every wing is listed. -/
theorem mem_all (w : Wing) : w ∈ Wing.all := by
  cases w <;> decide

/-- (R2) No wing is listed twice. -/
theorem all_nodup : Wing.all.Nodup := by decide

/-- `∀` over wings is decided by checking both wings in `Wing.all`. -/
instance (priority := low) decidableForall (P : Wing → Prop) [DecidablePred P] :
    Decidable (∀ w, P w) :=
  decidableForallOfMemAll Wing.all mem_all P

/-- `∃` over wings is decided by searching both wings in `Wing.all`. -/
instance (priority := low) decidableExists (P : Wing → Prop) [DecidablePred P] :
    Decidable (∃ w, P w) :=
  decidableExistsOfMemAll Wing.all mem_all P

end Wing

/-- The direction from the king's home square towards the rook's home square on wing `w`: east
for kingside, west for queenside. -/
def Wing.direction (w : Wing) : Direction :=
  match w with
  | .kingside  => .east
  | .queenside => .west

/-- The file on which the rook of wing `w` starts: h (7) for kingside, a (0) for queenside. -/
def Wing.rookFile (w : Wing) : Fin 8 :=
  match w with
  | .kingside  => 7
  | .queenside => 0

/-- The file on which the king lands when castling to wing `w`: g (6) for kingside, c (2) for
queenside. -/
def Wing.kingCastleFile (w : Wing) : Fin 8 :=
  match w with
  | .kingside  => 6
  | .queenside => 2

/-- The file on which the rook lands when castling to wing `w`: f (5) for kingside, d (3) for
queenside. -/
def Wing.rookCastleFile (w : Wing) : Fin 8 :=
  match w with
  | .kingside  => 5
  | .queenside => 3

/-- The files strictly between the king's and the rook's home files on wing `w`, nearest the king
first: f, g for kingside; d, c, b for queenside. -/
def Wing.betweenFiles (w : Wing) : List (Fin 8) :=
  match w with
  | .kingside  => [5, 6]
  | .queenside => [3, 2, 1]

/-- The square on which the king of colour `c` starts: e1 for White, e8 for Black. -/
def kingHome (c : Color) : Square := ⟨4, c.homeRank⟩

/-- The square on which the rook of colour `c` on wing `w` starts: the h-file (kingside) or
a-file (queenside) square of `c`'s home rank. -/
def rookHome (c : Color) (w : Wing) : Square := ⟨w.rookFile, c.homeRank⟩

/-- The square the king of colour `c` lands on when castling to wing `w`: g1 or c1 for White, g8
or c8 for Black. -/
def kingCastleSquare (c : Color) (w : Wing) : Square := ⟨w.kingCastleFile, c.homeRank⟩

/-- The square the king of colour `c` crosses when castling to wing `w`, which is where the rook
lands: the square next to `kingHome c` towards wing `w`; f1 or d1 for White, f8 or d8 for
Black. -/
def rookCastleSquare (c : Color) (w : Wing) : Square := ⟨w.rookCastleFile, c.homeRank⟩

/-- The squares strictly between the king's and the rook's home squares of colour `c` on wing
`w`, nearest the king first. Castling needs them all empty (FIDE 3.8.2.2). -/
def betweenKingAndRook (c : Color) (w : Wing) : List Square :=
  w.betweenFiles.map fun f => ⟨f, c.homeRank⟩

section Castling

/-- The king's home square is on the colour's home rank. -/
@[simp] theorem rank_kingHome (c : Color) : (kingHome c).rank = c.homeRank := rfl
/-- The rook's home square is on the colour's home rank. -/
@[simp] theorem rank_rookHome (c : Color) (w : Wing) : (rookHome c w).rank = c.homeRank := rfl
/-- The king's castling square is on the colour's home rank. -/
@[simp] theorem rank_kingCastleSquare (c : Color) (w : Wing) :
    (kingCastleSquare c w).rank = c.homeRank := rfl
/-- The rook's castling square is on the colour's home rank. -/
@[simp] theorem rank_rookCastleSquare (c : Color) (w : Wing) :
    (rookCastleSquare c w).rank = c.homeRank := rfl

/-- The king starts on the e-file. -/
@[simp] theorem file_kingHome (c : Color) : (kingHome c).file = 4 := rfl

/-- **FIDE 3.8.2, the king's move:** castling moves the king two squares from its home towards
the rook. -/
theorem shift_kingHome_two (c : Color) (w : Wing) :
    (kingHome c).shift w.direction 2 = some (kingCastleSquare c w) := by
  cases c <;> cases w <;> decide

/-- **FIDE 3.8.2, the rook's move:** the rook lands on the square the king crosses, one square
from the king's home towards the rook. -/
theorem shift_kingHome_one (c : Color) (w : Wing) :
    (kingHome c).shift w.direction 1 = some (rookCastleSquare c w) := by
  cases c <;> cases w <;> decide

/-- The king's castling square is not one king step from its home square. -/
theorem shift_kingHome_one_ne (c : Color) (w : Wing) (d : Direction) :
    (kingHome c).shift d 1 ≠ some (kingCastleSquare c w) := by
  revert d; cases c <;> cases w <;> decide

/-- The rook's home is the last square on the king's ray towards it. -/
theorem getLast?_ray_kingHome (c : Color) (w : Wing) :
    ((kingHome c).ray w.direction).getLast? = some (rookHome c w) := by
  cases c <;> cases w <;> decide

/-- The squares between king and rook are the rest of the king's ray towards the rook. -/
theorem betweenKingAndRook_eq (c : Color) (w : Wing) :
    betweenKingAndRook c w = ((kingHome c).ray w.direction).dropLast := by
  cases c <;> cases w <;> decide

/-- The square the king crosses lies between king and rook. -/
theorem rookCastleSquare_mem_between (c : Color) (w : Wing) :
    rookCastleSquare c w ∈ betweenKingAndRook c w := by
  cases c <;> cases w <;> decide

/-- The square the king lands on lies between king and rook. -/
theorem kingCastleSquare_mem_between (c : Color) (w : Wing) :
    kingCastleSquare c w ∈ betweenKingAndRook c w := by
  cases c <;> cases w <;> decide

/-- The four rook home squares are distinct. -/
@[simp] theorem rookHome_inj {c c' : Color} {w w' : Wing} :
    rookHome c w = rookHome c' w' ↔ c = c' ∧ w = w' := by
  cases c <;> cases c' <;> cases w <;> cases w' <;> decide

/-- No king's home square is a rook's home square. -/
theorem kingHome_ne_rookHome (c c' : Color) (w : Wing) : kingHome c ≠ rookHome c' w := by
  cases c <;> cases c' <;> cases w <;> decide

/-- No square a king lands on by castling is a rook's home square. -/
theorem kingCastleSquare_ne_rookHome (c c' : Color) (w w' : Wing) :
    kingCastleSquare c w ≠ rookHome c' w' := by
  cases c <;> cases c' <;> cases w <;> cases w' <;> decide

/-- No square a king lands on by castling is a king's home square. -/
theorem kingCastleSquare_ne_kingHome (c c' : Color) (w : Wing) :
    kingCastleSquare c w ≠ kingHome c' := by
  cases c <;> cases c' <;> cases w <;> decide

/-- The rook's landing square is never the king's landing square. -/
theorem rookCastleSquare_ne_kingCastleSquare (c c' : Color) (w w' : Wing) :
    rookCastleSquare c w ≠ kingCastleSquare c' w' := by
  cases c <;> cases c' <;> cases w <;> cases w' <;> decide

/-- No square a rook lands on by castling is a rook's home square. -/
theorem rookCastleSquare_ne_rookHome (c c' : Color) (w w' : Wing) :
    rookCastleSquare c w ≠ rookHome c' w' := by
  cases c <;> cases c' <;> cases w <;> cases w' <;> decide

/-- The square a castling rook lands on is not a king's home square. -/
theorem rookCastleSquare_ne_kingHome (c c' : Color) (w : Wing) :
    rookCastleSquare c w ≠ kingHome c' := by
  cases c <;> cases c' <;> cases w <;> decide

/-- The king's home square is on its own relative rank 0. -/
@[simp] theorem relRank_kingHome (c : Color) : (kingHome c).relRank c = 0 := by
  cases c <;> rfl

end Castling

/-! ## Notation (trusted: the FEN and UCI guards of `Chess.ChessGame` compare against these) -/

/-- The letter of the file of `s`, from `a` to `h`. -/
def Square.fileChar (s : Square) : Char := Char.ofNat ('a'.toNat + s.file.val)

/-- The digit of the rank of `s`, from `1` to `8`. -/
def Square.rankChar (s : Square) : Char := Char.ofNat ('1'.toNat + s.rank.val)

/-- The algebraic name of `s`, such as `e4`. -/
def Square.name (s : Square) : String := s!"{s.fileChar}{s.rankChar}"

/-- Squares print as their algebraic names. -/
instance : ToString Square := ⟨Square.name⟩

/-! ## Tests -/

example : (Square.mk 4 3).index = 28 := rfl
example : Square.ofIndex 63 = ⟨7, 7⟩ := rfl
example : (Square.mk 4 0).ray .east = [⟨5, 0⟩, ⟨6, 0⟩, ⟨7, 0⟩] := by decide
example : (Square.mk 0 0).ray .southWest = [] := by decide
example : ((Square.mk 3 3).ray .northEast).length = 4 := by decide
example : (Square.mk 4 6).relRank .black = 1 := by decide
example : (Square.mk 0 0).offset (-1) 0 = none := by decide
example : knightJumps.length = 8 := rfl
-- Plain `decide` reaches all 64 squares through the `Fin 8` quantifiers (D3.6).
example : ∀ s : Square, s.shift .north 8 = none := by decide
-- An en passant target square of a White double push (e3, on the third rank) has White's relative
-- rank index 2 and Black's relative rank index 5 (counting from 0), where Black's capturing pawn
-- lands.
example : (Square.mk 4 2).relRank .white = 2 ∧ (Square.mk 4 2).relRank .black = 5 := by decide
example : (∀ c : Color, ∀ w : Wing, (kingHome c).shift w.direction 2 = some (kingCastleSquare c w))
  := by decide
-- A bounded quantifier over a list is decided by the list, not by the whole-type instances
-- (which have low priority; see the implementation notes).
example (l : List Square) (P : Square → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∀ s ∈ l, P s)) = List.decidableBAll P l := rfl
example (l : List Square) (P : Square → Prop) [DecidablePred P] :
    (inferInstance : Decidable (∃ s ∈ l, P s)) = List.decidableBEx P l := rfl
#guard (Square.mk 4 3).name == "e4"
#guard toString (Square.mk 0 7) == "a8"

end Chess
