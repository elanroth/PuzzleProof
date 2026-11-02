/-
A small chess model built for *kernel* evaluation.

The whole board is one natural number: 64 four-bit nibbles, square `s = rank*8 + file`
(a1 = 0, h8 = 63). The kernel has GMP-accelerated `>>>`, `&&&`, `+`, `-`, so reading or
writing a square costs a couple of bignum operations instead of walking a list.

Nibble codes: 0 empty; 1..6 = white P N B R Q K; 9..14 = black P N B R Q K.
-/
namespace ChessProof

inductive Side where
  | white
  | black
deriving DecidableEq, Repr, Inhabited

def Side.other : Side → Side
  | .white => .black
  | .black => .white

@[simp] theorem Side.other_other (s : Side) : s.other.other = s := by cases s <;> rfl
@[simp] theorem Side.other_ne (s : Side) : s.other ≠ s := by cases s <;> decide
@[simp] theorem Side.ne_other (s : Side) : s ≠ s.other := by cases s <;> decide

structure Pos where
  /-- 64 nibbles, see the module docstring. -/
  bd : Nat
  turn : Side
  /-- bit 0 = K, bit 1 = Q, bit 2 = k, bit 3 = q. -/
  castle : Nat
  /-- En-passant target square, or 64 for none. -/
  ep : Nat
deriving DecidableEq, Repr, Inhabited

/-- `promo` is 0 for none, else the piece kind 2..5 (N B R Q). -/
structure Move where
  src : Nat
  dst : Nat
  promo : Nat := 0
deriving DecidableEq, Repr, Inhabited

def get (bd s : Nat) : Nat := (bd >>> (4 * s)) &&& 15
def put (bd s v : Nat) : Nat := bd - (get bd s <<< (4 * s)) + (v <<< (4 * s))

def kind (c : Nat) : Nat := c &&& 7
def code : Side → Nat → Nat
  | .white, k => k
  | .black, k => k + 8
def isSide (c : Nat) : Side → Bool
  | .white => c != 0 && c < 8
  | .black => c > 8

/-- Step from `s` by `(df, dr)`, each biased by +2 (so 0..4 stands for -2..2). -/
def shift (s df dr : Nat) : Option Nat :=
  let f := s % 8 + df
  let r := s / 8 + dr
  if 2 ≤ f ∧ f < 10 ∧ 2 ≤ r ∧ r < 10 then some ((r - 2) * 8 + (f - 2)) else none

def knightD : List (Nat × Nat) := [(3,4), (1,4), (4,3), (0,3), (4,1), (0,1), (3,0), (1,0)]
def kingD   : List (Nat × Nat) := [(1,1), (2,1), (3,1), (1,2), (3,2), (1,3), (2,3), (3,3)]
def rookD   : List (Nat × Nat) := [(2,3), (2,1), (1,2), (3,2)]
def bishopD : List (Nat × Nat) := [(1,1), (1,3), (3,1), (3,3)]

/-- Code of the first occupied square along a ray (0 if the ray leaves the board). -/
def rayHit (bd df dr : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, s => match shift s df dr with
    | none => 0
    | some t => if get bd t == 0 then rayHit bd df dr n t else get bd t

def jumpHits (bd s target : Nat) (ds : List (Nat × Nat)) : Bool :=
  ds.any fun (df, dr) => match shift s df dr with
    | some t => get bd t == target
    | none => false

/-- Is square `s` attacked by side `att`? -/
def attacked (bd s : Nat) (att : Side) : Bool :=
  jumpHits bd s (code att 2) knightD ||
  jumpHits bd s (code att 6) kingD ||
  jumpHits bd s (code att 1) (match att with | .white => [(1,1), (3,1)] | .black => [(1,3), (3,3)]) ||
  rookD.any (fun (df, dr) => let c := rayHit bd df dr 7 s; c == code att 4 || c == code att 5) ||
  bishopD.any (fun (df, dr) => let c := rayHit bd df dr 7 s; c == code att 3 || c == code att 5)

def findKing (bd : Nat) (sd : Side) : Nat :=
  ((List.range 64).find? fun s => get bd s == code sd 6).getD 64

def kingSafe (bd : Nat) (sd : Side) : Bool :=
  let k := findKing bd sd
  k < 64 && !attacked bd k sd.other

/-- Squares a slider reaches along one ray (empty squares, then a capture). -/
def slide (bd df dr : Nat) (me : Side) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, s => match shift s df dr with
    | none => []
    | some t =>
      if get bd t == 0 then t :: slide bd df dr me n t
      else if isSide (get bd t) me then [] else [t]

def pawnMoves (p : Pos) (s : Nat) : List Move :=
  let w := p.turn == .white
  let dr := if w then 3 else 1
  let last := if w then 7 else 0
  let start := if w then 1 else 6
  let mk (t : Nat) : List Move :=
    if t / 8 == last then [2, 3, 4, 5].map fun k => ⟨s, t, k⟩ else [⟨s, t, 0⟩]
  let pushes := match shift s 2 dr with
    | some t =>
      if get p.bd t == 0 then
        mk t ++ (if s / 8 == start then
          (match shift t 2 dr with
            | some u => if get p.bd u == 0 then [⟨s, u, 0⟩] else []
            | none => [])
        else [])
      else []
    | none => []
  let caps := [1, 3].foldr (fun df acc => match shift s df dr with
    | some t => if isSide (get p.bd t) p.turn.other || t == p.ep then mk t ++ acc else acc
    | none => acc) []
  pushes ++ caps

def castleMoves (p : Pos) : List Move :=
  let bd := p.bd
  let empty (s : Nat) := get bd s == 0
  let safe (s : Nat) := !attacked bd s p.turn.other
  let has (bit : Nat) := (p.castle >>> bit) &&& 1 == 1
  match p.turn with
  | .white =>
    (if has 0 && get bd 4 == 6 && get bd 7 == 4 && empty 5 && empty 6 && safe 4 && safe 5 && safe 6
      then [⟨4, 6, 0⟩] else []) ++
    (if has 1 && get bd 4 == 6 && get bd 0 == 4 && empty 3 && empty 2 && empty 1 && safe 4 && safe 3 && safe 2
      then [⟨4, 2, 0⟩] else [])
  | .black =>
    (if has 2 && get bd 60 == 14 && get bd 63 == 12 && empty 61 && empty 62 && safe 60 && safe 61 && safe 62
      then [⟨60, 62, 0⟩] else []) ++
    (if has 3 && get bd 60 == 14 && get bd 56 == 12 && empty 59 && empty 58 && empty 57 && safe 60 && safe 59 && safe 58
      then [⟨60, 58, 0⟩] else [])

def pieceMoves (p : Pos) (s : Nat) : List Move :=
  let k := kind (get p.bd s)
  let jumps (ds : List (Nat × Nat)) : List Move := ds.filterMap fun (df, dr) =>
    match shift s df dr with
    | some t => if isSide (get p.bd t) p.turn then none else some ⟨s, t, 0⟩
    | none => none
  let rays (ds : List (Nat × Nat)) : List Move :=
    ds.foldr (fun (df, dr) acc => (slide p.bd df dr p.turn 7 s).map (fun t => ⟨s, t, 0⟩) ++ acc) []
  if k == 1 then pawnMoves p s
  else if k == 2 then jumps knightD
  else if k == 3 then rays bishopD
  else if k == 4 then rays rookD
  else if k == 5 then rays rookD ++ rays bishopD
  else jumps kingD

/-- Pseudo-legal moves (may leave the mover's king in check). -/
def pseudo (p : Pos) : List Move :=
  (List.range 64).foldr (fun s acc =>
    if isSide (get p.bd s) p.turn then pieceMoves p s ++ acc else acc) (castleMoves p)

def rightsMask (s : Nat) : Nat :=
  if s == 4 then 12 else if s == 0 then 13 else if s == 7 then 14
  else if s == 60 then 3 else if s == 56 then 7 else if s == 63 then 11 else 15

def play (p : Pos) (m : Move) : Pos :=
  let c := get p.bd m.src
  let k := kind c
  let w := p.turn == .white
  let placed := if m.promo == 0 then c else code p.turn m.promo
  let bd1 := put (put p.bd m.src 0) m.dst placed
  let bd2 := if k == 1 && m.dst == p.ep then
      put bd1 (if w then m.dst - 8 else m.dst + 8) 0 else bd1
  let bd3 :=
    if k == 6 && w && m.src == 4 && m.dst == 6 then put (put bd2 7 0) 5 4
    else if k == 6 && w && m.src == 4 && m.dst == 2 then put (put bd2 0 0) 3 4
    else if k == 6 && !w && m.src == 60 && m.dst == 62 then put (put bd2 63 0) 61 12
    else if k == 6 && !w && m.src == 60 && m.dst == 58 then put (put bd2 56 0) 59 12
    else bd2
  let ep := if k == 1 && (m.dst == m.src + 16 || m.src == m.dst + 16) then (m.src + m.dst) / 2 else 64
  { bd := bd3, turn := p.turn.other,
    castle := p.castle &&& rightsMask m.src &&& rightsMask m.dst, ep := ep }

def legal (p : Pos) : List Move :=
  (pseudo p).filter fun m => kingSafe (play p m).bd p.turn

def inCheck (p : Pos) : Bool :=
  let k := findKing p.bd p.turn
  k < 64 && attacked p.bd k p.turn.other

/-- The side to move is checkmated. (Stalemate is *not* mate.) -/
def mated (p : Pos) : Bool := inCheck p && (legal p).isEmpty

def perft : Nat → Pos → Nat
  | 0, _ => 1
  | n+1, p => (legal p).foldl (fun acc m => acc + perft n (play p m)) 0

end ChessProof
