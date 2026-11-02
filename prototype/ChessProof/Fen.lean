import ChessProof.Basic

/-! FEN parsing over `List Char`, so the kernel can evaluate `fen "..."` inside statements. -/
namespace ChessProof

def pieceCode : Char → Nat
  | 'P' => 1 | 'N' => 2 | 'B' => 3 | 'R' => 4 | 'Q' => 5 | 'K' => 6
  | 'p' => 9 | 'n' => 10 | 'b' => 11 | 'r' => 12 | 'q' => 13 | 'k' => 14
  | _ => 0

/-- Board field; rank starts at 7 and file at 0. -/
def parseBoard : List Char → Nat → Nat → Nat → Nat
  | [], _, _, acc => acc
  | '/' :: cs, r, _, acc => parseBoard cs (r - 1) 0 acc
  | c :: cs, r, f, acc =>
    if c.isDigit then parseBoard cs r (f + (c.toNat - 48)) acc
    else parseBoard cs r (f + 1) (put acc (r * 8 + f) (pieceCode c))

def castleBits : List Char → Nat
  | [] => 0
  | 'K' :: cs => 1 ||| castleBits cs
  | 'Q' :: cs => 2 ||| castleBits cs
  | 'k' :: cs => 4 ||| castleBits cs
  | 'q' :: cs => 8 ||| castleBits cs
  | _ :: cs => castleBits cs

def epSquare : List Char → Nat
  | [f, r] => (r.toNat - 49) * 8 + (f.toNat - 97)
  | _ => 64

def splitSpaces : List Char → List (List Char)
  | [] => [[]]
  | ' ' :: cs => [] :: splitSpaces cs
  | c :: cs => match splitSpaces cs with
    | w :: ws => (c :: w) :: ws
    | [] => [[c]]

def fenChars (cs : List Char) : Pos :=
  match splitSpaces cs with
  | b :: t :: c :: e :: _ =>
    { bd := parseBoard b 7 0 0, turn := if t == ['b'] then .black else .white,
      castle := castleBits c, ep := epSquare e }
  | b :: t :: _ =>
    { bd := parseBoard b 7 0 0, turn := if t == ['b'] then .black else .white,
      castle := 0, ep := 64 }
  | _ => default

def fen (s : String) : Pos := fenChars s.toList

/-- `uci "e2e4"`, `uci "e7e8q"`. -/
def uci (s : String) : Move :=
  match s.toList with
  | [f1, r1, f2, r2] => ⟨(r1.toNat - 49) * 8 + (f1.toNat - 97), (r2.toNat - 49) * 8 + (f2.toNat - 97), 0⟩
  | [f1, r1, f2, r2, pr] =>
    ⟨(r1.toNat - 49) * 8 + (f1.toNat - 97), (r2.toNat - 49) * 8 + (f2.toNat - 97),
      kind (pieceCode pr)⟩
  | _ => default

def sqName (s : Nat) : String :=
  String.ofList [Char.ofNat (97 + s % 8), Char.ofNat (49 + s / 8)]

def Move.toUci (m : Move) : String :=
  sqName m.src ++ sqName m.dst ++
    (if m.promo == 0 then "" else String.ofList [['n', 'b', 'r', 'q'].getD (m.promo - 2) '?'])

end ChessProof
