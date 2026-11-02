import Chess

/-!
# The generated-file interface

The signatures of the names that generated certificate files may use (`Chess.Game.Cert`, module
docstring), each checked with `#guard_msgs`, so that a change to a name, an argument order, a
binder name or a field of a certificate type fails `lake build ChessTest` instead of breaking
generated files that have not been regenerated. Specification: `docs/spec/ChessTest.Interface.md`.

## Implementation notes

* Theorems and functions are recorded by `#check`, which shows the binder names (generated files
  may pass arguments by name, as in `checkWin_sound (c := …)`); the certificate types by `#print`,
  which shows their constructors and fields.
* An expected message with a line over 100 characters is wrapped and compared with
  `#guard_msgs (whitespace := lax)`, which ignores the line breaks but not the text.
* A deliberate change to this interface updates this file in the same change, and says so in the
  process log of `Chess.Game`.
-/

/-! ### Certificates (data) -/

/--
info: inductive Chess.Cert : Type → Type
number of parameters: 1
constructors:
Chess.Cert.goal : {M : Type} → Chess.Cert M
Chess.Cert.move : {M : Type} → M → Chess.Cert M → Chess.Cert M
Chess.Cert.replies : {M : Type} → List (M × Chess.Cert M) → Chess.Cert M
-/
#guard_msgs in #print Chess.Cert
/--
info: structure Chess.OnlyMoveCert (M : Type) : Type
number of parameters: 1
fields:
  Chess.OnlyMoveCert.next : Chess.Cert M
  Chess.OnlyMoveCert.refBudget : Nat
  Chess.OnlyMoveCert.refs : List (M × Chess.Cert M)
constructor:
  Chess.OnlyMoveCert.mk {M : Type} (next : Chess.Cert M) (refBudget : Nat) (refs : List
    (M × Chess.Cert M)) :
    Chess.OnlyMoveCert M
-/
#guard_msgs (whitespace := lax) in #print Chess.OnlyMoveCert

/-! ### Checkers and their soundness -/

/--
info: Chess.Game.checkWin (G : Chess.Game) (a : Chess.Color) (n : Nat) (x : G.State)
  (c : Chess.Cert G.Move) : Bool
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.checkWin
/--
info: Chess.Game.checkOnlyMove (G : Chess.Game) (n : Nat) (x : G.State) (best : G.Move)
  (oc : Chess.OnlyMoveCert G.Move) :
  Bool
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.checkOnlyMove
/--
info: Chess.Game.checkWin_sound {G : Chess.Game} {a : Chess.Color} {n : Nat} {x : G.State}
  {c : Chess.Cert G.Move}
  (h : G.checkWin a n x c = true) : G.WinsIn a n x
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.checkWin_sound
/--
info: Chess.Game.checkOnlyMove_sound {G : Chess.Game} {n : Nat} {x : G.State} {best : G.Move}
  {oc : Chess.OnlyMoveCert G.Move}
  (h : G.checkOnlyMove n x best oc = true) : G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.checkOnlyMove_sound

/-! ### Glue for per-node proofs -/

/--
info: Chess.Game.Forces.of_play_eq {G : Chess.Game} {a : Chess.Color} {T : G.State → Prop} {n : Nat}
  {x y : G.State}
  {m : G.Move} (h : G.play x m = y) (w : G.Forces a T n y) : G.Forces a T n (G.play x m)
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.Forces.of_play_eq
/--
info: Chess.Game.Forces.move_of_play_eq {G : Chess.Game} {a : Chess.Color} {T : G.State → Prop}
  {n : Nat} {x y : G.State}
  {m : G.Move} (ht : G.turn x = a) (hm : m ∈ G.moves x) (h : G.play x m = y)
    (w : G.Forces a T n y) :
  G.Forces a T (n + 1) x
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.Forces.move_of_play_eq
/--
info: Chess.Game.Forces.replies_of_moves_eq {G : Chess.Game} {a : Chess.Color} {T : G.State → Prop}
  {n : Nat} {x : G.State}
  {m : G.Move} {ms : List G.Move} (ht : G.turn x = a.other) (hl : G.moves x = m :: ms)
  (h : ∀ (m' : G.Move), m' ∈ m :: ms → G.Forces a T n (G.play x m')) : G.Forces a T n x
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.Forces.replies_of_moves_eq
/--
info: Chess.Game.Forces.forall_mem_nil {G : Chess.Game} {a : Chess.Color} {T : G.State → Prop}
  {n : Nat} {x : G.State}
  (m' : G.Move) : m' ∈ [] → G.Forces a T n (G.play x m')
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.Forces.forall_mem_nil
/--
info: Chess.Game.Forces.forall_mem_cons {G : Chess.Game} {a : Chess.Color} {T : G.State → Prop}
  {n : Nat} {x : G.State}
  {m : G.Move} {ms : List G.Move} (h : G.Forces a T n (G.play x m))
  (t : ∀ (m' : G.Move), m' ∈ ms → G.Forces a T n (G.play x m')) (m' : G.Move) :
  m' ∈ m :: ms → G.Forces a T n (G.play x m')
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.Forces.forall_mem_cons
/--
info: Chess.Game.WinsIn.of_mated {G : Chess.Game} {a : Chess.Color} {n : Nat} {x : G.State}
  (ht : G.turn x = a.other)
  (h : G.Mated x) : G.WinsIn a n x
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.WinsIn.of_mated
/--
info: Chess.Game.OnlyWinningMove.of_refuted {G : Chess.Game} {n : Nat} {x : G.State} {m : G.Move}
  (hm : m ∈ G.moves x)
  (w : G.WinsIn (G.turn x) n (G.play x m))
  (hr : ∀ (m' : G.Move), m' ∈ G.moves x → m' ≠ m → ∃ k, G.WinsIn (G.turn x).other k (G.play x m')) :
  G.OnlyWinningMove x m
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.OnlyWinningMove.of_refuted
/--
info: Chess.Game.OnlyWinningMove.of_moves_eq {G : Chess.Game} {a : Chess.Color} {n : Nat}
  {x : G.State} {m : G.Move}
  {ms : List G.Move} (ht : G.turn x = a) (hl : G.moves x = ms) (hm : m ∈ ms)
  (w : G.WinsIn a n (G.play x m))
  (hr : ∀ (m' : G.Move), m' ∈ ms → m' ≠ m → ∃ k, G.WinsIn a.other k (G.play x m')) :
  G.OnlyWinningMove x m
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.OnlyWinningMove.of_moves_eq
/--
info: Chess.Game.OnlyWinningMove.refuted_nil {G : Chess.Game} {a : Chess.Color} {x : G.State}
  {m : G.Move} (m' : G.Move) :
  m' ∈ [] → m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.OnlyWinningMove.refuted_nil
/--
info: Chess.Game.OnlyWinningMove.refuted_cons_self {G : Chess.Game} {a : Chess.Color}
  {x : G.State} {m : G.Move}
  {ms : List G.Move} (t : ∀ (m' : G.Move), m' ∈ ms → m' ≠ m → ∃ k, G.WinsIn a k (G.play x m'))
  (m' : G.Move) :
  m' ∈ m :: ms → m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.OnlyWinningMove.refuted_cons_self
/--
info: Chess.Game.OnlyWinningMove.refuted_cons {G : Chess.Game} {a : Chess.Color} {x : G.State}
  {m : G.Move} {ms : List G.Move}
  {m' : G.Move} {k : Nat} (w : G.WinsIn a k (G.play x m'))
  (t : ∀ (m'' : G.Move), m'' ∈ ms → m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'')) (m'' : G.Move) :
  m'' ∈ m' :: ms → m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'')
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.OnlyWinningMove.refuted_cons

/-! ### Diagnostics -/

/--
info: inductive Chess.Cert.Rejection : Type → Type
number of parameters: 1
constructors:
Chess.Cert.Rejection.notInTarget : {M : Type} → Chess.Cert.Rejection M
Chess.Cert.Rejection.noBudget : {M : Type} → Chess.Cert.Rejection M
Chess.Cert.Rejection.notAttackerTurn : {M : Type} → Chess.Cert.Rejection M
Chess.Cert.Rejection.unavailable : {M : Type} → M → Chess.Cert.Rejection M
Chess.Cert.Rejection.notDefenderTurn : {M : Type} → Chess.Cert.Rejection M
Chess.Cert.Rejection.noDefenderMove : {M : Type} → Chess.Cert.Rejection M
Chess.Cert.Rejection.missingReply : {M : Type} → M → Chess.Cert.Rejection M
Chess.Cert.Rejection.unrefuted : {M : Type} → M → Chess.Cert.Rejection M
-/
#guard_msgs in #print Chess.Cert.Rejection
/--
info: Chess.Game.firstFailureWin (G : Chess.Game) (a : Chess.Color) (n : Nat) (x : G.State)
  (c : Chess.Cert G.Move) :
  Option (List G.Move × Chess.Cert.Rejection G.Move)
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.firstFailureWin
/--
info: Chess.Game.firstFailureOnlyMove (G : Chess.Game) (n : Nat) (x : G.State) (best : G.Move)
  (oc : Chess.OnlyMoveCert G.Move) : Option (List G.Move × Chess.Cert.Rejection G.Move)
-/
#guard_msgs in #check Chess.Game.firstFailureOnlyMove

/-! ### Chess vocabulary of generated files -/

/-- info: Chess.Game.chess : Chess.Game -/
#guard_msgs in #check Chess.Game.chess

/-- info: Chess.WinsIn (a : Chess.Color) (n : Nat) (p : Chess.Position) : Prop -/
#guard_msgs in #check Chess.WinsIn
/-- info: Chess.OnlyWinningMove (p : Chess.Position) (m : Chess.Move) : Prop -/
#guard_msgs in #check Chess.OnlyWinningMove
/-- info: Chess.legalMoves (p : Chess.Position) : List Chess.Move -/
#guard_msgs in #check Chess.legalMoves
/-- info: Chess.Position.play (p : Chess.Position) (m : Chess.Move) : Chess.Position -/
#guard_msgs in #check Chess.Position.play
/--
info: Chess.mem_legalMoves {p : Chess.Position} {m : Chess.Move} : m ∈ Chess.legalMoves p ↔
  Chess.Legal p m
-/
#guard_msgs (whitespace := lax) in #check Chess.mem_legalMoves
/--
info: Chess.mem_chess_moves {p : Chess.Position} {m : Chess.Move} :
  m ∈ Chess.Game.chess.moves p ↔ Chess.Legal p m
-/
#guard_msgs (whitespace := lax) in #check Chess.mem_chess_moves
/--
info: Chess.fen (s : String) (h : (Chess.parseFEN s).isSome = true := by decide +kernel)
  : Chess.Position
-/
#guard_msgs (whitespace := lax) in #check Chess.fen
/--
info: Chess.uci (s : String) (h : (Chess.parseUCI s).isSome = true := by decide +kernel)
  : Chess.Move
-/
#guard_msgs (whitespace := lax) in #check Chess.uci
/-- info: Chess.Puzzles.gotham : Chess.Position -/
#guard_msgs in #check Chess.Puzzles.gotham

