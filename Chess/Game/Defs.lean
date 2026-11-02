import Chess.Basic

/-!
# Game: definitions

The trusted part of `Chess.Game`: two-player games with alternating turns, forcing play into a
target within a budget, and the notions of winning built on it. The other files of `Chess.Game`
prove laws about these definitions, decide them, or check claims about them; none of them is
trusted. Specification: `docs/spec/Game.md` §1; every definition below carries the docstring given
there.

## Main definitions

* `Game`: states, moves, the side to move, the available moves, the effect of a move, and when the
  side to move has been mated.
* `Game.Forces a T n x`: from `x`, the attacker `a` forces play into the target `T` using at most
  `n` moves of its own. Three rules: the state is in the target; the attacker has an available
  move to a forced state; the defender has an available move and all its available moves lead to
  forced states.
* `Game.WinsIn`, `Game.Wins`, `Game.MateIn`: forcing the defender to be mated, within a budget,
  within some budget, and in exactly a budget.
* `Game.OnlyWinningMove x m`: `m` is available, the side to move wins after it, and after no other
  available move.

## Implementation notes

* The only way to lose is to be mated. A state with no available move that is not mated, and play
  that never ends, are wins for nobody. There is no clock, repetition or move-count rule: for
  chess, `Wins` ignores the fifty-move rule and repetition.
* The defender rule demands at least one available move, so a stalemated defender has not lost.
* Budgets count attacker moves only, the mating move included, and are always counted at the state
  of the claim.
* For chess, `Chess.Spec.Winning` states the same notions with the rules alone, and
  `Chess.ChessGame.Fide` proves the two readings equivalent (THEOREMS G8), so a chess headline can
  be read without this file.
-/

namespace Chess

/-! ## Games -/

/-- A two-player game with alternating turns and finitely many moves in each state: its states, its
moves, the side to move, the moves available in each state, the effect of playing a move, and when
the side to move has been mated. The only way to lose is to be mated. A state with no available
move that is not mated, and endless play, are wins for nobody. There is no clock, repetition or
move-count rule. -/
structure Game where
  /-- The states of the game (for chess, positions). -/
  State : Type
  /-- The moves of the game, as data (for chess, a source, a destination and a promotion choice). -/
  Move : Type
  /-- The side to move in a state. -/
  turn : State → Color
  /-- The moves available to the side to move in a state, as a list. Only membership and emptiness
  of this list carry meaning; its order and any repetitions do not. An instance must not list two
  different values for the same move (for chess, two encodings of one castling), since
  `OnlyWinningMove` tells moves apart by their values. -/
  moves : State → List Move
  /-- The state after a move is played. It is total; its value at an unavailable move is
  unconstrained, and no trusted definition reads it. -/
  play : State → Move → State
  /-- The side to move has been mated: it has lost. -/
  Mated : State → Prop
  /-- Whether the side to move has been mated is decidable. -/
  [decMated : DecidablePred Mated]
  /-- Equality of moves is decidable. -/
  [decEqMove : DecidableEq Move]
  /-- Playing an available move passes the turn to the other side. -/
  turn_play : ∀ {x : State} {m : Move}, m ∈ moves x → turn (play x m) = (turn x).other
  /-- In a state where the side to move has been mated, no move is available. -/
  moves_eq_nil_of_mated : ∀ {x : State}, Mated x → moves x = []

-- Structure fields are not instances on their own. Without this line every decision about `Mated`
-- or about equality of moves would need `classical` or an explicit argument.
attribute [instance] Game.decMated Game.decEqMove

namespace Game

/-- In state `x` the defender `a.other` is to move and has been mated. -/
def DefenderMated (G : Game) (a : Color) (x : G.State) : Prop :=
  G.turn x = a.other ∧ G.Mated x

/-- Whether the defender has been mated is decidable. -/
instance DefenderMated.decidable (G : Game) (a : Color) : DecidablePred (G.DefenderMated a) :=
  fun x => inferInstanceAs (Decidable (G.turn x = a.other ∧ G.Mated x))

/-- `G.Forces a T n x`: from state `x`, the attacker `a` can force play into the target `T` using at
most `n` moves of its own, whatever the defender `a.other` does. Defender moves cost nothing. `T` is
tested at every state, `x` included. A defender to move with no available move escapes unless the
state is in `T`, and play that never reaches `T` is never forced. -/
inductive Forces (G : Game) (a : Color) (T : G.State → Prop) : Nat → G.State → Prop
  /-- A state in the target is forced, within any budget. -/
  | goal {n : Nat} {x : G.State} : T x → G.Forces a T n x
  /-- If the attacker is to move and some available move leads to a state forced within `n`, the
  state is forced within `n + 1`. -/
  | move {n : Nat} {x : G.State} (m : G.Move) : G.turn x = a → m ∈ G.moves x →
      G.Forces a T n (G.play x m) → G.Forces a T (n + 1) x
  /-- If the defender is to move, has at least one available move, and every available move leads
  to a state forced within `n`, the state is forced within `n`. This rule never applies to a
  defender with no available move. Such a state is forced only if it is already in the target, so
  for `WinsIn` a stalemated defender has not lost. -/
  | replies {n : Nat} {x : G.State} : G.turn x = a.other → G.moves x ≠ [] →
      (∀ m ∈ G.moves x, G.Forces a T n (G.play x m)) → G.Forces a T n x

/-- `G.WinsIn a n x`: from state `x`, the attacker `a` can force the defender to be mated using at
most `n` moves of its own, the mating move included. -/
abbrev WinsIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop :=
  G.Forces a (G.DefenderMated a) n x

/-- `G.Wins a x`: from state `x`, the attacker `a` can force the defender to be mated within a
bound: there is a number `n` such that `G.WinsIn a n x`. -/
def Wins (G : Game) (a : Color) (x : G.State) : Prop :=
  ∃ n, G.WinsIn a n x

/-- `G.MateIn a n x`: from state `x`, the attacker `a` mates in exactly `n`: it can force mate
within `n` moves of its own and not within fewer. -/
def MateIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop :=
  G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x

/-- `G.OnlyWinningMove x m`: `m` is available in state `x`, the side to move wins after `m`, and
after every other available move it does not win. 'Other' means a different value of `G.Move`, so
if another available move also wins, however slowly, there is no only winning move; in particular
there is none when two promotions both win. -/
def OnlyWinningMove (G : Game) (x : G.State) (m : G.Move) : Prop :=
  m ∈ G.moves x ∧ G.Wins (G.turn x) (G.play x m) ∧
    ∀ m' ∈ G.moves x, m' ≠ m → ¬ G.Wins (G.turn x) (G.play x m')

end Game

end Chess
