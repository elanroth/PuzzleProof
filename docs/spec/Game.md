# Specification of `Chess.Game`

Role: English specification writer (Round 1); translator (Rounds 2–3); refiner (Round 4).
Date: 2026-11-01.
Status: Round 4. The English was revised after the Round 1 critique (Round 2), where the
translation into `Chess/Game.lean` forced a decision (Round 3), and after the Round 3 critique of
the Lean (Round 4); `docs/process/Game.md` lists every change. Items marked *(checked)* were elaborated in Lean 4.28; since Round 3 every item of this spec
is in the library file and builds.

File: `Chess/Game.lean`. Depends on: `Chess.Basic`, and only for `Color`, `Color.other` and the
lemmas `Color.other_other`, `Color.self_ne_other`, `Color.eq_other_iff_ne` (Basic §1). Core only.
Refines DESIGN §6.1–§6.3, §7.2, §7.4 and §8.5. Theorem targets: **G1** (the interface; the chess
instance is `ChessGame`'s), **G2**, **G3**, **G4**, **G5**, **G6**, **O2** (`wins_iff`), **C1**,
**C2**, **C3**, **C7** (THEOREMS §4–§6), and the definition of O8 (`Forces`, with `Forces.trans`).

What a reader must trust from this module: the definitions of §1 only (`Game`, `DefenderMated`,
`Forces`, `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`). Everything in §2–§4 is either a theorem
or an executable function with a soundness theorem (and, for `searchForces` and `checkForces`,
completeness).

---

## 0. How to read this document

The conventions of `docs/spec/Basic.md` §0 apply, with these specifics:

- Each definition has an ID (`D1.5`), its Lean name and type, its Lean body, and a **docstring** in
  quotation marks; the Lean docstring is that text, word for word.
- Each lemma has an ID (`L2.4`), an English statement, the Lean statement, and a tag:
  - **[core]**: proved in this file; later modules or the theorems of THEOREMS depend on it.
  - **[sanity]**: checks that a definition says what its docstring says; proved in this file.
  - **[cheap]**: not on the Stage 1 critical path, proved in this file because the proof is a few
    lines (difficulty D1 of THEOREMS §0.2: routine induction). If it turns out longer than about 15
    lines, the translator moves it to §7's list and records that in the process log.
- The trust label **[kernel]** is THEOREMS §0.4's (DESIGN §7.3): `#print axioms` shows at most
  `propext`, `Classical.choice`, `Quot.sound`.
- The Lean docstring of a lemma is its English column. A leading tag such as "(G3)" or "(O8)",
  naming the THEOREMS entry the lemma realizes, is moved to the end of the docstring as
  "THEOREMS G3." (so the docstring opens with the claim).
- **Lemma IDs are stable labels, not positions.** A lemma added in a later round gets the next
  free number of its section and is placed where it reads best; L2.19–L2.25 are such.
- **Binding rule.** Every name a docstring mentions is bound in the signature before the colon,
  with one exception: a definition by pattern matching (D3.2, D4.2) has no names after the colon,
  so its docstring names those arguments itself, in phrases that say what each name is ("bounded
  search … at `x` … within `n`", "checks certificate `c`", "a `move m next` node", "a budget of
  the form `k + 1`", "every pair `(m, c)` of `rs`"). Naming the binders after the colon
  (`(n : Nat) → (x : G.State) → Bool`) is legal but buys nothing: the equation compiler drops the
  names, so hovers and `#check` show `Nat → G.State → Bool` anyway *(checked, Round 4)*.
- `autoImplicit = false`. Each Lean `section` declares the `variable` line given for it here, and
  only that line, immediately before its first lemma. In `section Search` the definitions D3.1–D3.4
  come first (they bind every argument explicitly), then the `variable` line, then the lemmas and
  instances. In particular `[DecidablePred T]` appears only in the sections that need it
  (Search, Certificates): Lean includes an instance variable in every theorem that mentions `T`,
  and warns when it is unused *(checked)*.
- Namespaces: everything lives in `namespace Chess`. `Game` and everything about games live in
  `namespace Chess.Game`; the certificate type is `Chess.Cert`. Names below are given relative to
  `Chess`. `namespace Game` opens right after D1.2 and closes before D4.1 (`Cert`); a second
  `namespace Game` opens after D4.1 and holds the rest of the file. `section Laws`,
  `section Search`, `section Certificates`, `section PerNode` and `namespace Toy` sit inside
  `namespace Game`.
- **The game is always the first explicit argument of a definition** (`G.WinsIn a n x`), so dot
  notation reads naturally and `G` is never inferred from a state (DESIGN §6.1). In theorems `G` is
  implicit, from the `variable` line.
- Inside `namespace Chess.Game`, never write a bare `Move` or `State`: they would mean the
  projections `Game.Move : Game → Type`. Always write `G.Move`, `G.State`.

Letters (used consistently in every statement):

- `G` a game; `x y` states; `m m' best` moves; `ms` a list of moves.
- `a` the **attacker**, a `Color`; the defender is always `a.other`. No other colour letter is
  used.
- `T U` targets (`G.State → Prop`); `n n' k` budgets (`Nat`).
- `c next` certificates (`Cert G.Move`); `rs refs` lists of pairs `(move, certificate)`; `r` one
  such pair.
- `atk` a Boolean test on states (`G.State → Bool`), the argument of the defender rule of §3.
- `h …` hypotheses: `ht` about a turn, `hm` about membership in a move list, `hne` non-emptiness,
  `hdiff` that two moves differ (`m' ≠ m`), `hnm` that a state is not mated, `hl` a move-list
  equation, `w` a forcing derivation (`Forces`/`WinsIn` proof).

Words (used consistently in the English):

- An **attacker state** (or attacker node) is one where `a` is to move; a **defender state** (or
  defender node) is one where `a.other` is to move.
- The **children** of `x` are the states `G.play x m` for `m ∈ G.moves x`; a node "below" `x` is a
  child of `x`.
- A move is **available** at `x` when it is a member of `G.moves x`.

### The idea of the module, in one paragraph

A game is a set of states with a side to move, a finite list of available moves in each state, a
total function that plays a move, and a decidable notion "the side to move has been mated". The
central definition is **forcing**: the attacker forces play into a target set within a budget of
attacker moves, given by three rules (the state is in the target; the attacker has a move to a
forced state, spending one unit of budget; the defender **has at least one move** and all its moves
lead to forced states, spending nothing). Winning is forcing the defender to be mated. Everything
else is proved once from these three rules: monotonicity, that two sides cannot both win, that a
stalemated side has not lost, a bounded search that decides forcing, and a certificate checker,
mirroring the three rules, whose acceptance proves forcing. Chess is one instance, defined in
`Chess.ChessGame`; nothing here mentions a piece.

### Contents of the file, in order

1. Module docstring, text below.
2. `/-! ## Games -/` (trusted): D1.1–D1.9.
3. `/-! ## Laws -/`, `section Laws`: L2.1–L2.25, under the subheadings `/-! ### … -/` of §2.1–§2.5
   ("One step of forcing, read backwards", "Budgets and targets", "Winning", "Exact distance", "The
   only winning move").
4. `/-! ## Search -/`, `section Search`: D3.1–D3.4, L3.1–L3.5, the instances D3.5–D3.6.
5. `/-! ## Certificates -/`: D4.1 (outside `namespace Game`), D4.2–D4.4, then
   `section Certificates` (L4.1–L4.7) and, under `/-! ### Lemmas for per-node kernel proofs -/`,
   `section PerNode` (L4.8–L4.10).
6. `/-! ## Examples -/`, `namespace Toy`: D5.1–D5.2 and the tests T1–T14.

### The module docstring, word for word

```
# Game

Two-player games with alternating turns, forced play into a target, forced wins, a bounded search
that decides them, and a certificate checker whose acceptance proves them. Chess is one instance
(`Chess.ChessGame`); nothing here mentions a piece. Specification: `docs/spec/Game.md`; every
definition below carries the docstring given there.

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
* `Game.searchForces`: bounded search, by structural recursion on the budget.
* `Cert`, `Game.checkForces`, `Game.checkWin`, `Game.checkOnlyMove`: certificates proposed by an
  untrusted search, and their checkers.

## Main statements

* `Forces.mono` (G3), `WinsIn.not_both` and `Wins.not_both` (G4), `winsIn_zero_iff` and
  `not_wins_of_stalemate` (G2), `MateIn.unique` (G6), `OnlyWinningMove.wins_iff` (O2).
* `wins_attacker_iff`, `wins_defender_iff`: one step of winning, read backwards (for G9, G10).
* `searchForces_iff` (G5): the search decides forcing; hence `Forces` and `MateIn` are decidable.
* `checkForces_sound`, `checkForces_complete`, `checkWin_sound`, `checkWin_complete` (C1, C2), and
  `checkOnlyMove_sound` (C7).
* `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`, `Forces.of_play_eq` (C3): the glue for
  proofs that check one node at a time.

## Implementation notes

* The only way to lose is to be mated. A state with no available move that is not mated, and play
  that never ends, are wins for nobody. There is no clock, repetition or move-count rule: for
  chess, `Wins` ignores the fifty-move rule and repetition.
* The defender rule demands at least one available move, so a stalemated defender has not lost.
* Budgets count attacker moves only, the mating move included, and are always counted at the state
  of the claim.
* Only the definitions of the section "Games" are trusted. The search and the checkers are
  executable Boolean functions, each with a soundness theorem; the search and `checkForces` are
  also complete.
```

---

## 1. Section "Games" (trusted)

No `variable` line: every definition binds its arguments explicitly.

### D1.1 `structure Game : Type 1`

```lean
structure Game where
  State : Type
  Move : Type
  turn : State → Color
  moves : State → List Move
  play : State → Move → State
  Mated : State → Prop
  [decMated : DecidablePred Mated]
  [decEqMove : DecidableEq Move]
  turn_play : ∀ {x : State} {m : Move}, m ∈ moves x → turn (play x m) = (turn x).other
  moves_eq_nil_of_mated : ∀ {x : State}, Mated x → moves x = []
```
*(checked)*

Docstring of the structure: "A two-player game with alternating turns and finitely many moves in
each state: its states, its moves, the side to move, the moves available in each state, the effect
of playing a move, and when the side to move has been mated. The only way to lose is to be mated. A
state with no available move that is not mated, and endless play, are wins for nobody. There is no
clock, repetition or move-count rule."

Field docstrings, in order:

- `State`: "The states of the game (for chess, positions)."
- `Move`: "The moves of the game, as data (for chess, a source, a destination and a promotion
  choice)."
- `turn`: "The side to move in a state."
- `moves`: "The moves available to the side to move in a state, as a list. Only membership and
  emptiness of this list carry meaning; its order and any repetitions do not. An instance must not
  list two different values for the same move (for chess, two encodings of one castling), since
  `OnlyWinningMove` tells moves apart by their values."
- `play`: "The state after a move is played. It is total; its value at an unavailable move is
  unconstrained, and no trusted definition reads it."
- `Mated`: "The side to move has been mated: it has lost."
- `decMated`: "Whether the side to move has been mated is decidable."
- `decEqMove`: "Equality of moves is decidable."
- `turn_play`: "Playing an available move passes the turn to the other side."
- `moves_eq_nil_of_mated`: "In a state where the side to move has been mated, no move is
  available."

Notes for the translator:

- The two decidability fields are written with **instance-implicit binders** `[…]`. Then a
  `where` construction may omit them and Lean fills them by instance search (the toy games of §5
  do so *(checked)*; so will `Game.chess` for `Mated p := InCheck p ∧ legalMoves p = []`).
- `turn_play` and `moves_eq_nil_of_mated` take `x` and `m` implicitly and the hypothesis
  explicitly, so a proof writes `G.turn_play hm` and `G.moves_eq_nil_of_mated h`. This deviates
  from THEOREMS G1, where `turn_play` takes `x` and `m` explicitly (§6, choice 19).
- **Instance obligation (for `ChessGame`).** `OnlyWinningMove` compares moves as values of
  `G.Move` (D1.9), so an instance must not list two different values that play the same move (for
  chess, two encodings of the same castling). The `moves` docstring states it (Round 4). `Game`
  does not state it as a field: nothing in this module needs it, it would cost every toy game a
  proof, and breaking it can only make `OnlyWinningMove` false, never wrongly true.

### D1.2 Instances from the fields

`attribute [instance] Game.decMated Game.decEqMove` *(checked)*, immediately after D1.1, outside
`namespace Game`. Comment above it (not a docstring, since `attribute` takes none): "Structure
fields are not instances on their own. Without this line every decision about `Mated` or about
equality of moves would need `classical` or an explicit argument."

### D1.3 `Game.DefenderMated (G : Game) (a : Color) (x : G.State) : Prop`

`G.turn x = a.other ∧ G.Mated x`.
Docstring: "In state `x` the defender `a.other` is to move and has been mated."

### D1.4 `instance Game.DefenderMated.decidable (G : Game) (a : Color) : DecidablePred (G.DefenderMated a)`

`fun x => inferInstanceAs (Decidable (G.turn x = a.other ∧ G.Mated x))` *(checked; writing the
proposition out, rather than `(_ ∧ _)`, keeps `x` used and avoids an unused-variable warning)*.
Docstring: "Whether the defender has been mated is decidable."

### D1.5 `inductive Game.Forces (G : Game) (a : Color) (T : G.State → Prop) : Nat → G.State → Prop`

```lean
inductive Forces (G : Game) (a : Color) (T : G.State → Prop) : Nat → G.State → Prop
  | goal {n : Nat} {x : G.State} : T x → G.Forces a T n x
  | move {n : Nat} {x : G.State} (m : G.Move) : G.turn x = a → m ∈ G.moves x →
      G.Forces a T n (G.play x m) → G.Forces a T (n + 1) x
  | replies {n : Nat} {x : G.State} : G.turn x = a.other → G.moves x ≠ [] →
      (∀ m ∈ G.moves x, G.Forces a T n (G.play x m)) → G.Forces a T n x
```
*(checked: dot notation `G.Forces` works inside the constructors' own types.)*

Docstring: "`G.Forces a T n x`: from state `x`, the attacker `a` can force play into the target `T`
using at most `n` moves of its own, whatever the defender `a.other` does. Defender moves cost
nothing. `T` is tested at every state, `x` included. A defender to move with no available move
outside `T` escapes, and play that never reaches `T` is never forced."

Constructor docstrings:

- `goal`: "A state in the target is forced, within any budget."
- `move`: "If the attacker is to move and some available move leads to a state forced within `n`,
  the state is forced within `n + 1`."
- `replies`: "If the defender is to move, has at least one available move, and every available move
  leads to a state forced within `n`, the state is forced within `n`. This rule never applies to a
  defender with no available move. Such a state is forced only if it is already in the target, so
  for `WinsIn` a stalemated defender has not lost."

The three constructors are the whole meaning of the module. In English, read as a definition:
**the family `(F n)` of sets of states forced within `n` is the least family such that, for every
`n`: `T ⊆ F n`; every attacker state with an available move into `F n` lies in `F (n + 1)`; and
every defender state that has an available move, all of whose available moves lead into `F n`,
lies in `F n`.**

### D1.6 `abbrev Game.WinsIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop`

`G.Forces a (G.DefenderMated a) n x`.
Docstring: "`G.WinsIn a n x`: from state `x`, the attacker `a` can force the defender to be mated
using at most `n` moves of its own, the mating move included."

An `abbrev`, not a `def` (design choice 5): every lemma and instance about `Forces` then applies to
`WinsIn` without restatement, and `h.mono` for `h : G.WinsIn a n x` finds `Forces.mono`
*(checked)*.

### D1.7 `def Game.Wins (G : Game) (a : Color) (x : G.State) : Prop`

`∃ n, G.WinsIn a n x`.
Docstring: "`G.Wins a x`: from state `x`, the attacker `a` can force the defender to be mated
within a bound: there is a number `n` such that `G.WinsIn a n x`."

The bound is one `n` for every line of the defender. Since every state has finitely many moves,
this agrees with the unbounded notion of a winning strategy, but the definition does not rely on
that.

### D1.8 `def Game.MateIn (G : Game) (a : Color) (n : Nat) (x : G.State) : Prop`

`G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x`.
Docstring: "`G.MateIn a n x`: from state `x`, the attacker `a` mates in exactly `n`: it can force
mate within `n` moves of its own and not within fewer."

An engine's report of mate in 3 for `a` claims `MateIn a 3`; it is an untrusted claim, and its
distance is not proved minimal. (Stockfish reports "mate −3" when the side to move is the one
mated, so the attacker is then the opponent of the side to move.) A problem's stipulation "#3" is
`WinsIn a 3`; a sound #3 problem also satisfies `¬ WinsIn a 2`, which together with the
stipulation is `MateIn a 3` by L2.12.

### D1.9 `def Game.OnlyWinningMove (G : Game) (x : G.State) (m : G.Move) : Prop`

`m ∈ G.moves x ∧ G.Wins (G.turn x) (G.play x m) ∧ ∀ m' ∈ G.moves x, m' ≠ m → ¬ G.Wins (G.turn x) (G.play x m')`.
Docstring: "`G.OnlyWinningMove x m`: `m` is available in state `x`, the side to move wins after
`m`, and after every other available move it does not win. 'Other' means a different value of
`G.Move`, so if another available move also wins, however slowly, there is no only winning move;
in particular there is none when two promotions both win."

"Wins after `m`" means: in the state after `m`, where the opponent is to move, the side that played
`m` is the attacker and can force mate.

**No other definition is trusted.** In particular `Holds`, `Trap` and the game value are Stage 3
(§7), and the chess instance and the `Chess.*` abbreviations are `Chess.ChessGame`'s.

---

## 2. Section "Laws"

```lean
variable {G : Game} {a : Color} {T U : G.State → Prop} {n n' k : Nat} {x y : G.State}
  {m m' : G.Move} {ms : List G.Move}
```

### 2.1 One step of forcing, read backwards

L2.1–L2.3 say what a `Forces` derivation at a single state can be, given who is to move. They are
the backbone of the search proof (§3), of `winsIn_zero_iff` and of the stalemate lemma, and they
are what a reader uses to unfold a claim by hand. Each one uses L2.21 to rule out the constructor of
the wrong side. L2.21 comes first in the file; it is the one contradiction that recurs throughout
§2 (seven times in Round 3).

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.21 | The side to move is never both the attacker and the defender. | `theorem turn_ne_both (ht : G.turn x = a) (ht' : G.turn x = a.other) : False` | core |
| L2.1 | With no budget left and the attacker to move, the attacker forces the target exactly when the state is already in it. | `theorem forces_attacker_zero_iff (ht : G.turn x = a) : G.Forces a T 0 x ↔ T x` | core *(checked)* |
| L2.2 | With budget `n + 1` and the attacker to move, the attacker forces the target exactly when the state is in it or some available move leads to a state forced within `n`. | `theorem forces_attacker_succ_iff (ht : G.turn x = a) : G.Forces a T (n + 1) x ↔ T x ∨ ∃ m ∈ G.moves x, G.Forces a T n (G.play x m)` | core *(checked)* |
| L2.3 | With the defender to move, the attacker forces the target within `n` exactly when the state is in it, or the defender has an available move and every available move leads to a state forced within `n`. | `theorem forces_defender_iff (ht : G.turn x = a.other) : G.Forces a T n x ↔ T x ∨ (G.moves x ≠ [] ∧ ∀ m ∈ G.moves x, G.Forces a T n (G.play x m))` | core *(checked)* |

Proofs *(checked)*. L2.21: `Color.self_ne_other a (ht.symm.trans ht')`. L2.1–L2.3: `constructor`;
forwards by `cases h`, closing the wrong side's constructor with `(turn_ne_both ht ht').elim` (or
`turn_ne_both ht' ht` for L2.3); backwards by the constructors.

### 2.2 Budgets and targets

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.4 | (G3) More budget never hurts. | `theorem Forces.mono (w : G.Forces a T n x) (hn : n ≤ n') : G.Forces a T n' x` | core *(checked)* |
| L2.5 | (O8) If the attacker forces `T` within `n`, and from every state of `T` forces `U` within `k`, then it forces `U` within `n + k`. | `theorem Forces.trans (w : G.Forces a T n x) (hT : ∀ y, T y → G.Forces a U k y) : G.Forces a U (n + k) x` | cheap |
| L2.22 | If after each move of the finite list `ms` the target is forced within some budget, then it is forced after all of them within one budget, the largest. | `theorem forces_common_budget (h : ∀ m ∈ ms, ∃ n, G.Forces a T n (G.play x m)) : ∃ n, ∀ m ∈ ms, G.Forces a T n (G.play x m)` | cheap |

Proofs. L2.4 *(checked)*: `induction w generalizing n'`; in the `move` case obtain `n' = k + 1`
from `⟨n' - 1, by omega⟩`, then `.move m ht hm (ih (by omega))`. L2.5: `induction w`; `goal` case
`(hT _ h).mono (Nat.le_add_left k _)`; `move` case `rw [Nat.add_right_comm]` then the constructor;
`replies` case the constructor. L2.22: induction on `ms`; `[]` with budget 0; on `m :: ms` take
`max n k` of the head's budget and the tail's, and lift both by L2.4 (`Nat.le_max_left`,
`Nat.le_max_right`). L2.22 is what turns "the attacker wins after every defender reply" into one
budget; it is stated for moves at `x` (not for an arbitrary function into states) because that is
its only use.

For `h : G.WinsIn a n x`, `h.mono hn` is L2.4; no separate `WinsIn.mono` is declared *(checked)*.
THEOREMS G3's name `WinsIn.mono` is therefore satisfied by dot notation. If a later Lean version
stops unfolding the `abbrev` for dot notation, add the one-line alias
`theorem WinsIn.mono (w : G.WinsIn a n x) (hn : n ≤ n') : G.WinsIn a n' x := Forces.mono w hn`.

### 2.3 Winning

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.6 | (G2) With no budget, the attacker wins exactly when the defender is to move and has already been mated. | `theorem winsIn_zero_iff : G.WinsIn a 0 x ↔ G.turn x = a.other ∧ G.Mated x` | core |
| L2.20 | In a state with no available move, `a` wins exactly when the defender is to move and has been mated. (This covers a mated attacker, a stalemated attacker and a stalemated defender.) | `theorem wins_iff_of_moves_eq_nil (hl : G.moves x = []) : G.Wins a x ↔ G.turn x = a.other ∧ G.Mated x` | core |
| L2.7 | (G2) If the side to move has not been mated and has no available move (it is stalemated), the attacker does not win, whichever side it is. | `theorem not_wins_of_stalemate (hnm : ¬ G.Mated x) (hl : G.moves x = []) : ¬ G.Wins a x` | core |
| L2.23 | With the attacker to move, it wins exactly when some available move leads to a state it wins. | `theorem wins_attacker_iff (ht : G.turn x = a) : G.Wins a x ↔ ∃ m ∈ G.moves x, G.Wins a (G.play x m)` | cheap |
| L2.24 | With the defender to move, the attacker wins exactly when the defender has been mated, or the defender has an available move and the attacker wins after every available move. | `theorem wins_defender_iff (ht : G.turn x = a.other) : G.Wins a x ↔ G.Mated x ∨ (G.moves x ≠ [] ∧ ∀ m ∈ G.moves x, G.Wins a (G.play x m))` | cheap |
| L2.8 | (G4) No state is a forced win for both sides, whatever the two budgets. | `theorem WinsIn.not_both (w : G.WinsIn a n x) (w' : G.WinsIn a.other k x) : False` | core |
| L2.9 | (G4) No state is won by both sides. | `theorem Wins.not_both (h : G.Wins a x) (h' : G.Wins a.other x) : False` | core |
| L2.10 | If the opponent of `a` wins within some budget, then `a` does not win. | `theorem not_wins_of_winsIn_other (w : G.WinsIn a.other k x) : ¬ G.Wins a x` | core |

Proofs.

- L2.6: split on `G.turn x = a` (else `G.turn x = a.other` by `Color.eq_other_iff_ne.2`). If the
  attacker is to move, L2.1 gives `WinsIn a 0 x ↔ G.DefenderMated a x`, which is the right side by
  definition. If the defender is to move, `(forces_defender_iff ht').trans ⟨?_, .inl⟩` (a bare
  `rw` does not see through the `abbrev`; choice 5 gives two workarounds): the second disjunct is impossible, because the
  defender has a move `m` (from `hne`), the child is an attacker state (`G.turn_play hm`,
  `Color.other_other`), and by L2.1 an attacker state forced within 0 is in `DefenderMated a`,
  whose turn clause contradicts it (L2.21).
- L2.20: forwards, `rintro ⟨n, w⟩; cases w`: `goal` is the claim; `move` has a member of
  `G.moves x = []`; `replies` has `G.moves x ≠ []`. Backwards, `fun h => ⟨0, .goal h⟩`.
- L2.20's right side is written out, as in L2.6, rather than as `G.DefenderMated a x` (Round 4): the
  two sibling lemmas state the same condition the same way, as THEOREMS G2 does. The proof is
  unchanged, since `DefenderMated` unfolds by definition.
- L2.7: `fun h => hnm ((wins_iff_of_moves_eq_nil hl).1 h).2`. No turn hypothesis is needed: L2.20
  already says that with no moves only a mated defender loses. (THEOREMS G2 states it with
  `ht : G.turn x = a.other`; the version here is stronger; §6, choice 19.)
- L2.8 (the prototype's `not_both`): `induction w generalizing k`, then `cases w'`. Nine cases. A
  `goal`/`move` or `move`/`goal` pair contradicts `G.moves_eq_nil_of_mated` with the membership;
  `move`/`replies` and `replies`/`move` use the induction hypothesis at the child of the move;
  every other pair has `G.turn x = a` and `G.turn x = a.other` (after `Color.other_other`), closed by
  L2.21. Uses no decidability. The turn clauses of the second derivation, stated for
  `a.other.other`, are transported by `Color.other_other a ▸ _`.
- L2.9: `obtain ⟨n, w⟩ := h; obtain ⟨k, w'⟩ := h'; exact w.not_both w'`.
- L2.10: `fun ⟨n, w'⟩ => w'.not_both w`.
- L2.23: forwards, `rintro ⟨n, w⟩; cases w`: `goal` and `replies` contradict `ht` by L2.21; `move`
  gives the move and its budget. Backwards, `⟨n + 1, .move m ht hm w⟩`. Uses no axiom.
- L2.24: forwards, L2.3 on the derivation; the `goal` disjunct gives `Mated`, the other gives each
  child's win with the same budget. Backwards, a mate is `⟨0, .goal ⟨ht, h⟩⟩`; otherwise L2.22 gives
  one budget for all children and `.replies` closes.

L2.23 and L2.24 are the one-step characterizations of `Wins` that the trap duality (G9) and the
negamax equations of the game value (G10) need; with them those theorems are mostly assembly.

### 2.4 Exact distance

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.11 | (G6) Mating in exactly `n` and in exactly `k` from the same state forces `n = k`. | `theorem MateIn.unique (h : G.MateIn a n x) (h' : G.MateIn a k x) : n = k` | core |
| L2.12 | (G6) Mating in exactly `n + 1` is winning within `n + 1` and not within `n`. | `theorem mateIn_succ_iff : G.MateIn a (n + 1) x ↔ G.WinsIn a (n + 1) x ∧ ¬ G.WinsIn a n x` | core |
| L2.13 | Mating in exactly 0 is winning within 0. | `theorem mateIn_zero_iff : G.MateIn a 0 x ↔ G.WinsIn a 0 x` | sanity |
| L2.14 | (G6) A side that wins mates in some exact number of moves. | `theorem Wins.exists_mateIn (h : G.Wins a x) : ∃ n, G.MateIn a n x` | cheap |
| L2.15 | Mating in exactly `n` implies winning. | `theorem MateIn.wins (h : G.MateIn a n x) : G.Wins a x` | sanity |

Proofs.

- L2.11: `rcases Nat.lt_trichotomy n k with hlt | rfl | hlt`; `h'.2 n hlt h.1`; `rfl`;
  `h.2 k hlt h'.1`.
- L2.12: forwards `⟨h.1, h.2 n (Nat.lt_succ_self n)⟩`; backwards
  `⟨h.1, fun k hk w => h.2 (w.mono (by omega))⟩`.
- L2.13: `⟨And.left, fun h => ⟨h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩⟩`.
- L2.14: prove `∀ n, G.WinsIn a n x → ∃ k, G.MateIn a k x` by ordinary induction on `n` (no strong
  induction, no `Nat.find`): for `0`, `MateIn a 0` by L2.13; for `n + 1`, `by_cases G.WinsIn a n x`:
  if so, the induction hypothesis; if not, `MateIn a (n + 1)` by L2.12. `by_cases` here is
  classical, which a [kernel] label allows.
- L2.15: `⟨n, h.1⟩`.

### 2.5 The only winning move

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.16 | (O2) If `m` is the only winning move at `x`, then for every available move `m'`, the side to move wins after `m'` exactly when `m' = m`. | `theorem OnlyWinningMove.wins_iff (h : G.OnlyWinningMove x m) (hm' : m' ∈ G.moves x) : G.Wins (G.turn x) (G.play x m') ↔ m' = m` | core |
| L2.17 | If `m` is the only winning move at `x`, the side to move wins at `x`. | `theorem OnlyWinningMove.wins (h : G.OnlyWinningMove x m) : G.Wins (G.turn x) x` | sanity |
| L2.18 | A state has at most one only winning move. | `theorem OnlyWinningMove.unique (h : G.OnlyWinningMove x m) (h' : G.OnlyWinningMove x m') : m = m'` | sanity |
| L2.25 | If `m` is the only winning move at `x` and the side to move wins within `n + 1`, then it wins within `n` after `m`: a fastest win starts with `m`. | `theorem OnlyWinningMove.winsIn_play (h : G.OnlyWinningMove x m) (w : G.WinsIn (G.turn x) (n + 1) x) : G.WinsIn (G.turn x) n (G.play x m)` | cheap |
| L2.19 | If `m` is available at `x`, the side to move wins within `n` after it, and after every other available move the opponent wins within some budget, then `m` is the only winning move. | `theorem OnlyWinningMove.of_refuted (hm : m ∈ G.moves x) (w : G.WinsIn (G.turn x) n (G.play x m)) (hr : ∀ m' ∈ G.moves x, m' ≠ m → ∃ k, G.WinsIn (G.turn x).other k (G.play x m')) : G.OnlyWinningMove x m` | core |

Proofs. L2.16: forwards `fun hw => Decidable.byContradiction fun hdiff => h.2.2 m' hm' hdiff hw`,
constructive through the instance `G.decEqMove` (D1.2); backwards `fun he => he ▸ h.2.1`. L2.17, in
term mode: `let ⟨n, w⟩ := h.2.1; ⟨n + 1, .move m rfl h.1 w⟩`. L2.18:
`(h'.wins_iff h.1).1 h.2.1`, which yields `m = m'` in hypothesis order, like L2.11. L2.25: L2.2 at
`a := G.turn x`; the `goal` disjunct says the side to move is its own defender, absurd by L2.21; the
`move` disjunct gives a winning move `m'` with a budget-`n` win after it, and L2.16 says `m' = m`.
L2.19:
`⟨hm, ⟨n, w⟩, fun m' hm' hdiff => let ⟨k, w'⟩ := hr m' hm' hdiff; not_wins_of_winsIn_other w'⟩`.

L2.19 is a law about `OnlyWinningMove` and mentions no certificate, so it sits here (it was L4.11
in Round 1). It is the root lemma of a per-node only-move proof (§4.1) and the last step of L4.7.

L2.25 recovers what L4.7 does not state: after the only winning move, the win takes one budget
unit less. Fastest mate (O3) and only mate within a horizon (O4) need it. It is a separate lemma,
not a third conjunct of L4.7, because it holds of every only winning move, certified or not.

---

## 3. Section "Search"

The search decides `Forces` for a decidable target (G5). It is bounded minimax by **structural
recursion on the budget**, with no fuel and no well-founded recursion, so `decide`, `decide +kernel`
and `rfl` can all run it (lean-eng §7). It is feasible only for small budgets: a negative fact
`¬ WinsIn a k x` in chess branches over every attacker move at each of `k` attacker plies, and over
defender replies until one escapes, so between about 35^k and 35^(2k) leaves; hence `k ≤ 2` or `3`
(DESIGN §6.3).

The difficulty is that a defender node does not consume budget, so a single function recursive on
the budget cannot call itself at a defender child with the same budget. The answer is to name the
defender rule once, as a non-recursive function that takes the attacker test as an argument
(`defenderStep`), and to let the attacker function, recursive on the budget, call it with its own
recursive call at the smaller budget. The alternation law then guarantees that the children of an
attacker node are defender nodes and vice versa.

The attacker function does not take the colour `a`: at an attacker node, what the attacker can do
does not depend on its name. Its correctness lemma therefore says that at every state it decides
forcing **for the side to move** (L3.3), and dually `defenderForced` decides forcing for the
opponent of the side to move (L3.4). The colour `a` enters only through the dispatch in
`searchForces`.

### D3.1 `Game.defenderStep (G : Game) (T : G.State → Prop) [DecidablePred T] (atk : G.State → Bool) (x : G.State) : Bool`

`decide (T x) || (!(G.moves x).isEmpty && (G.moves x).all fun m => atk (G.play x m))` *(checked)*.
Docstring: "The rule at a defender node, given a test `atk` for the attacker nodes below it: `x`
is in the target, or the defender at `x` has an available move and every available move leads to a
state that passes `atk`."

### D3.2 `Game.attackerForces (G : Game) (T : G.State → Prop) [DecidablePred T] : Nat → G.State → Bool`

```lean
def attackerForces (G : Game) (T : G.State → Prop) [DecidablePred T] : Nat → G.State → Bool
  | 0, x => decide (T x)
  | n + 1, x => decide (T x) ||
      (G.moves x).any fun m => G.defenderStep T (G.attackerForces T n) (G.play x m)
```
*(checked: structural on the budget, including the partially applied recursive call
`G.attackerForces T n`.)*
Docstring: "Bounded search for the side to move: can the side to move at `x`, as attacker, force
the target within `n` moves of its own? With no budget, only if `x` is in the target; with budget
`n + 1`, if `x` is in the target or some available move leads to a state where the opponent,
now to move, is forced within `n`."

### D3.3 `Game.defenderForced (G : Game) (T : G.State → Prop) [DecidablePred T] (n : Nat) (x : G.State) : Bool`

`G.defenderStep T (G.attackerForces T n) x` *(checked)*.
Docstring: "Bounded search for the opponent of the side to move: is the side to move at `x`, as
defender, forced into the target within `n` moves of the attacker?"

### D3.4 `Game.searchForces (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] (n : Nat) (x : G.State) : Bool`

`if G.turn x = a then G.attackerForces T n x else G.defenderForced T n x`.
Docstring: "Bounded search: decides whether the attacker `a` forces the target `T` within `n`
moves of its own from `x` (`searchForces_iff`)."

### Lemmas of §3

```lean
variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat} {x : G.State}
```

| ID | English | Lean | Tag |
|---|---|---|---|
| L3.1 | At an attacker node with budget `n + 1`, the search asks whether `x` is in the target or some move leads to a defender node that is forced within `n`. | `theorem attackerForces_succ (n : Nat) (x : G.State) : G.attackerForces T (n + 1) x = (decide (T x) \|\| (G.moves x).any fun m => G.defenderForced T n (G.play x m))` | sanity *(checked, `rfl`)* |
| L3.2 | If `atk` answers correctly for budget `n` at every attacker node, then the defender rule answers correctly for budget `n` at every defender node. | `theorem defenderStep_iff {atk : G.State → Bool} (hatk : ∀ y, G.turn y = a → (atk y = true ↔ G.Forces a T n y)) (ht : G.turn x = a.other) : G.defenderStep T atk x = true ↔ G.Forces a T n x` | core *(checked)* |
| L3.3 | At every state, the attacker search decides forcing for the side to move. | `theorem attackerForces_iff : G.attackerForces T n x = true ↔ G.Forces (G.turn x) T n x` | core |
| L3.4 | At every state, the defender search decides forcing for the opponent of the side to move. | `theorem defenderForced_iff : G.defenderForced T n x = true ↔ G.Forces (G.turn x).other T n x` | core |
| L3.5 | (G5) The search is correct at every state. | `theorem searchForces_iff : G.searchForces a T n x = true ↔ G.Forces a T n x` | core |

L3.3 and L3.4 have no turn hypothesis: the attacker is named by the state. The section variable
`a` is unused by them, and Lean includes a section variable only when the statement mentions it.

Proofs.

- L3.2 *(checked)*: `rw [forces_defender_iff ht]`, then
  `simp only [defenderStep, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
  List.isEmpty_eq_false_iff, List.all_eq_true]`; every child is an attacker node
  (`G.turn_play hm`, `ht`, `Color.other_other`), so `hatk` converts each conjunct; the two sides
  then match by core's congruence lemmas `or_congr`, `and_congr_right`, `forall_congr'`,
  `imp_congr_right` (L3.3 likewise with `exists_congr`).
- L3.3: `induction n generalizing x`. Zero: `simp [attackerForces, forces_attacker_zero_iff rfl]`.
  Successor: `rw [forces_attacker_succ_iff rfl]`,
  `simp only [attackerForces, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]`, and L3.2 at
  `a := G.turn x` for each child (a defender node by `G.turn_play hm`), with `hatk` from the
  induction hypothesis: at an attacker node `y`, `G.turn y = G.turn x`, so the hypothesis's
  `Forces (G.turn y)` is `Forces (G.turn x)`.
- L3.4: L3.2 at `a := (G.turn x).other`, with `ht` by `Color.other_other` and `hatk` from L3.3.
- L3.5: `unfold searchForces; split`. In the `then` branch rewrite L3.3 with `G.turn x = a`; in the
  `else` branch `G.turn x = a.other` (from `Color.eq_other_iff_ne.2`), rewrite L3.4 with it and
  `Color.other_other`.

### D3.5 `instance Game.Forces.decidable : Decidable (G.Forces a T n x)`

`decidable_of_iff _ searchForces_iff` (with the section's variables).
Docstring: "Forcing within a budget is decidable, by the bounded search `searchForces`." Through
the `abbrev`, this also decides `G.WinsIn a n x` *(checked)*.

### D3.6 `instance Game.MateIn.decidable : Decidable (G.MateIn a n x)`

`inferInstanceAs (Decidable (G.WinsIn a n x ∧ ∀ k < n, ¬ G.WinsIn a k x))` *(checked)*, with the
section's variables, like D3.5 (Round 4; Round 3 bound `G a n x` explicitly). `[DecidablePred T]`
is not included, since the statement does not mention `T`. The bounded `∀ k < n` is core's
`Nat.decidableBallLT`.
Docstring: "Mating in exactly `n` is decidable, by searching each budget from 0 to `n`." (The cost is
dominated by the largest budget, so checking every `k < n` instead of only `n - 1` costs little.)

`Wins` is not decidable here: its budget is unbounded.

---

## 4. Section "Certificates"

An untrusted search (Stockfish through a script) proposes a **certificate**, a finite strategy tree.
A Boolean checker replays it against the rules of the game; the soundness theorem turns acceptance
into the forcing claim. If a certificate checks, the claim holds. No certificate for a false claim
checks. The checker mirrors the three constructors of `Forces` one for one.

### D4.1 `inductive Cert (M : Type) : Type` (namespace `Chess`, not `Chess.Game`)

```lean
inductive Cert (M : Type) where
  | goal
  | move (m : M) (next : Cert M)
  | replies (rs : List (M × Cert M))
  deriving Inhabited
```
*(checked)*

Docstring: "A certificate for a forcing claim: a finite strategy tree for the attacker, proposed by
an untrusted search and checked by `Game.checkForces`. It is data; it is never trusted."
Constructor docstrings:

- `goal`: "The state is in the target."
- `move`: "The attacker plays `m`; `next` is the certificate for the state after it."
- `replies`: "The defender is to move; each pair `(m, c)` of `rs` gives the certificate `c` for the
  state after the defender's move `m`. Pairs for moves that are not available, and repeated moves,
  are allowed; every pair must check."

`Cert` is declared after `end Game` and before a second `namespace Game` that holds the checkers.
No `Repr` is derived: certificates live in generated files and are never printed by Lean.

### D4.2 `Game.checkForces` and `Game.checkReplies`, by mutual structural recursion

```lean
mutual
def checkForces (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → Cert G.Move → Bool
  | _, x, .goal => decide (T x)
  | 0, _, .move _ _ => false
  | k + 1, x, .move m next =>
      decide (G.turn x = a) && decide (m ∈ G.moves x) && G.checkForces a T k (G.play x m) next
  | n, x, .replies rs =>
      decide (G.turn x = a.other) && decide (G.moves x ≠ []) &&
        decide (∀ m ∈ G.moves x, m ∈ rs.map Prod.fst) && G.checkReplies a T n x rs

def checkReplies (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → List (G.Move × Cert G.Move) → Bool
  | _, _, [] => true
  | n, x, (m, c) :: rs => G.checkForces a T n (G.play x m) c && G.checkReplies a T n x rs
end
```
*(checked: Lean 4.28 accepts the mutual structural recursion through `List (M × Cert M)`; the
checker evaluates under `decide`, `decide +kernel` and `rfl`; `#print axioms checkForces` shows
only `propext`.)*

Docstring of `checkForces`: "Checks certificate `c` for the claim `G.Forces a T n x`, one rule of
forcing per constructor. A `goal` leaf needs `x` to be in the target. A `move m next` node needs the
attacker to be to move, a budget of the form `k + 1`, `m` to be available, and `next` to check
after `m` with budget `k`. A `replies rs` node needs the defender to be to move and to have an
available move, every available move to appear in `rs` (as the first component of some pair), and
every certificate in `rs` to check after its move with the same budget `n`. Pairs for moves that
are not available, and repeated moves, are allowed; every pair must check."

Docstring of `checkReplies`: "Checks every pair `(m, c)` of `rs`: the certificate `c` checks, with
budget `n`, in the state after `m` is played at `x`."

Line comment above `mutual` (Round 4), answering the reader's question "why not `rs.all`?":
"`checkReplies` walks the reply list by hand instead of calling `List.all`: structural recursion
cannot pass through `List.all` over the nested `List (G.Move × Cert G.Move)`, and the hand-written
recursion keeps the checker reducible by the kernel (`decide +kernel`, `rfl`)."

Every conjunct is the `decide` of the corresponding proposition of `Forces`, so the soundness proof
is one `simp only [checkForces, Bool.and_eq_true, decide_eq_true_eq]` per node (design choice 10).

### D4.3 `Game.checkWin (G : Game) (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) : Bool`

`G.checkForces a (G.DefenderMated a) n x c`.
Docstring: "Checks certificate `c` for the claim `G.WinsIn a n x`."

### D4.4 `Game.checkOnlyMove (G : Game) (n k : Nat) (x : G.State) (best : G.Move) (next : Cert G.Move) (refs : List (G.Move × Cert G.Move)) : Bool`

```lean
G.checkWin (G.turn x) n x (.move best next) &&
  decide (∀ m ∈ G.moves x, m ≠ best → m ∈ refs.map Prod.fst) &&
  refs.all fun r => G.checkWin (G.turn x).other k (G.play x r.1) r.2
```
*(checked)*

Docstring: "Accepts only if `best` is the only winning move at `x` and the side to move wins
within `n` moves, counted at `x` with `best` included. Accepting proves both
(`checkOnlyMove_sound`). `next` is the win certificate for the state after `best`; `refs` gives,
for every other available move, a certificate that the opponent wins within `k` moves after it. It
rejects true claims in which some alternative does not lose but only draws: this checker cannot
certify those, and refutations by traps are future work."

The budget convention is DESIGN §7.2's: **`n` is counted at `x`, before the best move**, like
every budget in the library. So for the Gotham position the headline uses `n = 11` with no
subtraction anywhere.

### Lemmas of §4

```lean
section Certificates
variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n k : Nat}
  {x : G.State} {best : G.Move} {c next : Cert G.Move} {refs : List (G.Move × Cert G.Move)}
```

| ID | English | Lean | Tag |
|---|---|---|---|
| L4.1 | (C1, general) If the checker accepts a certificate, the attacker forces the target. | `theorem checkForces_sound : ∀ {n : Nat} {x : G.State} (c : Cert G.Move), G.checkForces a T n x c = true → G.Forces a T n x` | core *(checked)* |
| L4.2 | If every pair of a reply list checks, the attacker forces the target after each listed move. | `theorem checkReplies_sound : ∀ {n : Nat} {x : G.State} (rs : List (G.Move × Cert G.Move)), G.checkReplies a T n x rs = true → ∀ r ∈ rs, G.Forces a T n (G.play x r.1)` | core *(checked)* |
| L4.3 | If after each move of `ms` some certificate checks with budget `n`, then some reply list whose moves are exactly `ms`, in the same order, checks. | `theorem exists_checkReplies (ms : List G.Move) (h : ∀ m ∈ ms, ∃ c, G.checkForces a T n (G.play x m) c = true) : ∃ rs : List (G.Move × Cert G.Move), rs.map Prod.fst = ms ∧ G.checkReplies a T n x rs = true` | core |
| L4.4 | (C2, general) Every true forcing claim has an accepted certificate: the format is not lossy. | `theorem checkForces_complete (w : G.Forces a T n x) : ∃ c, G.checkForces a T n x c = true` | core |
| L4.5 | (C1) If the checker accepts a win certificate, the attacker wins within the budget. | `theorem checkWin_sound (h : G.checkWin a n x c = true) : G.WinsIn a n x` | core |
| L4.6 | (C2) Every forced win has an accepted win certificate. | `theorem checkWin_complete (w : G.WinsIn a n x) : ∃ c, G.checkWin a n x c = true` | core |
| L4.7 | (C7) If the only-move checker accepts, `best` is the only winning move at `x` and the side to move wins within `n`. | `theorem checkOnlyMove_sound (h : G.checkOnlyMove n k x best next refs = true) : G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x` | core |

L4.1 and L4.2 are one `mutual … end` block of theorems by structural recursion on the certificate
and on the list (not `induction`, which does not handle the nested inductive). Their binders are
after the colon for that reason, unlike every other lemma here; the section variables supply only
`G`, `a`, `T` and the instance. Close the section with `end Certificates` after L4.7.

Proofs.

- L4.1/L4.2 *(checked)*: as in the scratch file. `goal`: `.goal (by simpa [checkForces] using h)`.
  `move` at budget 0: `simp [checkForces] at h`. `move` at `k + 1`:
  `simp only [checkForces, Bool.and_eq_true, decide_eq_true_eq] at h`, then
  `.move m h.1.1 h.1.2 (checkForces_sound next h.2)`. `replies`: the same `simp only`, then
  `.replies ht hne fun m hm => …` where coverage gives `⟨r, hr, rfl⟩ := List.mem_map.1 (hcov m hm)`
  and `checkReplies_sound rs hrs r hr` finishes. `checkReplies_sound`: `[]` by `simp`; on
  `(m, c) :: rs`, `List.mem_cons.1` and the two recursive calls.
- L4.3: induction on `ms`. `[]`: `⟨[], rfl, rfl⟩`. `m :: ms`: from `h m` obtain `c`, from the
  induction hypothesis obtain `rs`, and take `(m, c) :: rs`.
- L4.4: `induction w`. `goal`: `⟨.goal, by simp [checkForces, h]⟩`. `move`: from the induction
  hypothesis `⟨c, hc⟩`, take `.move m c`. `replies`: L4.3 on `G.moves x` with the induction
  hypothesis gives `rs` with `rs.map Prod.fst = G.moves x`; take `.replies rs`; coverage holds
  because the map is the move list itself.
- L4.5, L4.6: L4.1 and L4.4 at `T := G.DefenderMated a`.
- L4.7: `simp only [checkOnlyMove, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h`.
  From the first conjunct: L4.5 gives `G.WinsIn (G.turn x) n x`; and `cases n` on it (budget 0
  makes `checkForces` false) with one more `simp only [checkWin, checkForces, …]` gives
  `best ∈ G.moves x` and the win after `best` with budget `n - 1`. For each other available move,
  coverage finds its pair in `refs` and L4.5 gives the opponent's win after it. L2.19 assembles
  `OnlyWinningMove x best`.

### 4.1 Lemmas for per-node kernel proofs (C3)

A large certificate is not checked by one evaluation of `checkWin`. It is compiled into one small
theorem per node, each stating the state after a move as a literal (`G.play x m = y`, proved by
`decide`), and the nodes are chained by the lemmas below (DESIGN §7.4). They are stated for
`Forces`, so they also serve `WinsIn`.

```lean
section PerNode
variable {G : Game} {a : Color} {T : G.State → Prop} {n : Nat} {x y : G.State}
  {m : G.Move} {ms : List G.Move}
```

| ID | English | Lean | Tag |
|---|---|---|---|
| L4.8 | If playing `m` at `x` gives `y`, every forcing fact about `y` holds after `m`. | `theorem Forces.of_play_eq (h : G.play x m = y) (w : G.Forces a T n y) : G.Forces a T n (G.play x m)` | core |
| L4.9 | Attacker node: if the attacker is to move, `m` is available, playing it gives `y`, and `y` is forced within `n`, then `x` is forced within `n + 1`. | `theorem Forces.move_of_play_eq (ht : G.turn x = a) (hm : m ∈ G.moves x) (h : G.play x m = y) (w : G.Forces a T n y) : G.Forces a T (n + 1) x` | core |
| L4.10 | Defender node: if the defender is to move, its available moves are the explicit non-empty list `m :: ms`, and each of them leads to a state forced within `n`, then `x` is forced within `n`. | `theorem Forces.replies_of_moves_eq (ht : G.turn x = a.other) (hl : G.moves x = m :: ms) (h : ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m')) : G.Forces a T n x` | core |

Proofs: L4.8 `h ▸ w`; L4.9 `.move m ht hm (h ▸ w)`; L4.10
`.replies ht (by rw [hl]; exact List.cons_ne_nil _ _) (by rw [hl]; exact h)`.
`end PerNode`.

L4.10 needs `G.moves x = m :: ms` **exactly**: the literal list the generator returns, in its order
and with any repetitions, since `hl` is proved by evaluation. Choice 16's "order carries no
meaning" is about the definitions; it does not let a per-node proof list the moves in another
order. The only-move root of a per-node proof is L2.19.

A per-node defender proof walks the explicit list with core's `List.forall_mem_cons`
(`(∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x`) and `List.forall_mem_nil`
(`∀ (p : α → Prop) (x : α), x ∈ [] → p x`) *(both checked to exist with these shapes)*, so this
module needs no `all_cons`/`all_nil` of its own. The intended generated shape, for chess (names as
in `ChessGame`), is:

```lean
theorem w5 : Chess.WinsIn .black 10 p2 :=
  Game.Forces.move_of_play_eq rfl (by decide) (by decide : p2.play m₁ = p3) w4
theorem w6 : Chess.WinsIn .black 10 p1 :=
  Game.Forces.replies_of_moves_eq rfl (by decide : legalMoves p1 = [m₂]) <|
    List.forall_mem_cons.2 ⟨Game.Forces.of_play_eq (by decide : p1.play m₂ = p2) w5,
      List.forall_mem_nil _⟩
```

At an attacker node the membership `m ∈ G.moves x` may be proved by any means. For chess, once
`mem_legalMoves` is proved, `mem_legalMoves.2 (by decide : Legal p m)` decides legality of one move
(about 0.27 s) instead of generating all of them (about 3.2 s; MoveGen review C2). This is why
`Game` has no `isLegal` field (design choice 13).

---

## 5. Section "Examples"

Toy games make every definition run instantly under `decide`, so these tests stay in the library
file (they add well under a second). They live in `namespace Chess.Game.Toy`.

### D5.1 `abbrev Game.Toy.takeAway : Game`

```lean
abbrev takeAway : Game where
  State := Color × Nat
  Move := Nat
  turn x := x.1
  moves x := [1, 2].filter (· ≤ x.2)
  play x t := (x.1.other, x.2 - t)
  Mated x := x.2 = 0
  turn_play _ := rfl
  moves_eq_nil_of_mated {x} h := by simp [h]
```
*(checked)*
Docstring: "The take-away game: a state is the side to move and a pile of counters; a move takes one
or two counters; the side to move facing an empty pile has lost."

It must be an `abbrev`: with a `def`, numerals like `1 : takeAway.Move` find no `OfNat` instance
*(checked)*.

### D5.2 `abbrev Game.Toy.takeAwayStalemate : Game`

The same, written out in full (not by `{ takeAway with … }`, which copies `decMated` and then fails
to typecheck *(checked)*), except
`Mated x := x.2 = 0 ∧ x.1 = .white` and `moves_eq_nil_of_mated {x} h := by simp [h.1]` *(checked)*.
Docstring: "The take-away game in which an empty pile with White to move is a loss for White; with
Black to move it is a stalemate."

### The tests

Each is an `example` (or, for T11, a `theorem` named as given, so it can be cited). An `example`
carries no docstring; each test is preceded by a line comment `-- Tn. …` giving its "What it
tests" column in a sentence. T11 has a docstring, since it is a named theorem. T6 is two examples,
one by `decide +kernel` and one by `rfl`. All values were computed by hand, and since Round 3 every
test elaborates in the library file against the proved lemmas.

| ID | Statement | Proof | What it tests |
|---|---|---|---|
| T1 | `takeAway.WinsIn .white 2 (.white, 4)` | `by decide` *(checked)* | search, a two-move win |
| T2 | `takeAway.MateIn .white 2 (.white, 4)` | `by decide` *(checked)* | exact distance |
| T3 | `¬ takeAway.WinsIn .white 5 (.white, 3)` | `by decide` *(checked)* | a negative fact by search |
| T4 | `takeAway.WinsIn .white 0 (.black, 0)` | `by decide` *(checked)* | a mate leaf at budget 0 |
| T5 | `¬ takeAway.Wins .white (.white, 3)` | `not_wins_of_winsIn_other (by decide : takeAway.WinsIn .black 1 (.white, 3))` *(checked)* | `not_both` |
| T6 | `takeAway.checkWin .white 2 (.white, 4) (.move 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)])) = true` | `by decide +kernel` and also `rfl` *(both checked)* | the checker accepts |
| T7 | the same certificate with budget `1` `= false` | `by decide` *(checked)* | budget is enforced |
| T8 | `takeAway.checkWin .white 2 (.white, 4) (.move 1 (.replies [(1, .move 2 .goal)])) = false` | `by decide` *(checked)* | a missing defender reply is rejected |
| T9 | `takeAway.checkOnlyMove 2 1 (.white, 4) 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)]) [(2, .move 2 .goal)] = true` | `by decide +kernel` *(checked)* | the only-move checker accepts |
| T10 | the same with `refs := []` `= false` | `by decide` *(checked)* | an unrefuted alternative is rejected |
| T11 | `theorem takeAway_onlyWinningMove : takeAway.OnlyWinningMove (.white, 4) 1` | `(checkOnlyMove_sound (by decide +kernel : takeAway.checkOnlyMove 2 1 (.white, 4) 1 (.replies [(1, .move 2 .goal), (2, .move 1 .goal)]) [(2, .move 2 .goal)] = true)).1`, the instance of T9 | soundness end to end |
| T12 | `¬ takeAwayStalemate.Wins .white (.black, 0)` | `not_wins_of_stalemate (by decide) rfl` | a stalemated defender has not lost |
| T13 | `¬ takeAwayStalemate.WinsIn .white 3 (.black, 0)` | `by decide` *(checked)* | the search agrees on stalemate |
| T14 | `takeAwayStalemate.WinsIn .black 1 (.black, 1)` | `by decide` *(checked)* | the variant still has mates |

Reading of T1/T9: from a pile of 4 with White to move, White takes 1, leaving 3; whatever Black
takes, White takes the rest and Black faces an empty pile. Taking 2 instead leaves 2, and Black
takes both and wins: that is the refutation in T9.

---

## 6. Design choices, with reasons

1. **`Game` is a structure, the game is the first explicit argument** (DESIGN §6.1). A morphism
   between two games on the same state type is easy to name (G7), and `G.WinsIn a n x` reads like
   the English.
2. **Decidability as instance-implicit fields, registered as instances** (D1.1–D1.2). Instance
   binders let constructions omit them; the `attribute` line makes them available everywhere
   without `classical`.
3. **The alternation law is required only for available moves.** That is all any proof uses (every
   use is at a child `G.play x m` with `m ∈ G.moves x`), and it asks the least of an instance. Chess
   satisfies the stronger unconditional law anyway (`play_turn`).
4. **`Forces` is the primitive; winning is one instance of it** (THEOREMS O8, DESIGN §6.2).
   Monotonicity, search, certificates, soundness and completeness are proved once for any decidable
   target; only `winsIn_zero_iff`, `not_both`, `wins_iff_of_moves_eq_nil`, the stalemate lemma and
   the one-step `Wins` lemmas (L2.23, L2.24) are about mate. The goal holds at any budget, so
   the index means "within"; the budget counts only attacker moves, the mating move included; the
   defender rule demands at least one move, so stalemate is never a loss (the dwrensha `ForcedWin`
   bug, prior-work §5).
5. **`WinsIn` is an `abbrev`; `Wins`, `MateIn`, `OnlyWinningMove` and `DefenderMated` are `def`s.**
   `WinsIn` is only a name for one target, and every `Forces` lemma, the decidability instance and
   dot notation must reach through it *(checked)*. The others are new concepts, which a reader
   should see by name in goals; each has the instances and lemmas it needs. **Caveat (Rounds 3–4):**
   term application, `exact`, instance search, dot notation and `simp` see through the `abbrev`,
   but a bare `rw` does not: `rw [forces_defender_iff ht]` fails on a goal stated with `WinsIn`,
   because `rw` matches the goal's head symbol syntactically. Three ways round it, all
   *(checked)*: unfold first, `rw [WinsIn, forces_defender_iff ht]`; use
   `simp only [forces_defender_iff ht]`, which unfolds reducible definitions; or compose with
   `Iff.trans`, as L2.6 does.
6. **`MateIn` is "within `n` and not within any `k < n`"**, not "within `n` and not within `n − 1`":
   it handles `n = 0` without truncated subtraction, and L2.12 recovers the second form.
7. **`OnlyWinningMove` says the alternatives do not win, not that they lose.** That is the semantic
   claim (THEOREMS O2). The Stage 1 checker proves it by showing the opponent wins after each
   alternative (stronger evidence, through `not_both`); Stage 3 adds traps for alternatives that
   only draw, without changing the definition.
8. **The search names the defender rule once** (`defenderStep`), as a non-recursive function of the
   attacker test. The attacker search is then structural on the budget, `defenderForced` is that
   rule applied to the attacker search at the same budget, and the proof is one lemma per rule
   (L3.2, L3.3) instead of a joint induction on two mutually defined functions.
9. **The attacker search does not take the colour.** At an attacker node the colour is irrelevant;
   it is a hypothesis of the correctness lemma. One fewer argument, and the search reads as the rule.
10. **Every Boolean conjunct of the checkers is `decide` of the proposition it stands for.** Then
    `simp only [checkForces, Bool.and_eq_true, decide_eq_true_eq]` turns acceptance into exactly the
    hypotheses of the matching `Forces` constructor, and no Boolean helper (`memB`, `lookup`) or its
    lemma is needed. The prototype needed both.
11. **The checker recurses over the certificate's reply list, and checks coverage separately**
    (DESIGN §7.2): structural recursion, no fuel (the prototype's fuel had no meaning in the claim).
    **Deviation from DESIGN §7.2 and §8.5:** the checker does *not* require every listed reply to be
    an available move. Soundness does not need it: a pair for a move that is not available is still
    checked and must pass, but contributes nothing to the conclusion, since `replies` quantifies
    only over available moves. Dropping it removes a conjunct, one membership
    test per pair (each of which re-reads `G.moves x`), and a sentence from the docstring.
    Completeness is unaffected (L4.4 builds a reply list naming exactly the available moves).
12. **Certificates carry no budgets and no states.** The budget belongs to the claim; states are
    recomputed by `play`. `Cert` is generic in the move type (`Chess.Cert`, not `Game.Cert`), so a
    certificate for one game can be transported along a game morphism by mapping its moves (G7).
13. **No `isLegal` field in `Game` (Stage 1).** DESIGN §6.1 left it optional. The per-node lemmas
    (L4.9) take the membership `m ∈ G.moves x` as a hypothesis, so a chess proof can supply it from
    `Legal` through `mem_legalMoves` at the cost of one legality decision. The field would help only
    the monolithic checker, whose cost is not the bottleneck; adding it later changes one
    construction (`Game.chess`) and the `move` conjunct of `checkForces`.
14. **`checkOnlyMove` takes the certificate *after* the best move** (`next`) and checks
    `.move best next` at `x`. **Deviation from DESIGN §7.2**, which takes a certificate "whose root is
    `move best _`": building the root instead of inspecting it needs no root extractor and no
    conjunct saying "the root is `best`", and the budget is still counted at `x`.
15. **One refutation budget `k` for all alternatives** (resolves DESIGN §10's open question). By
    monotonicity the maximum of the individual budgets works for all of them, so nothing is lost,
    and the refutation list keeps the same type as a reply list.
16. **The trusted definitions read `moves x` only through membership and emptiness**, and the
    executable ones only through order-insensitive `any`, `all`, `isEmpty` and membership. So
    nothing here needs `Nodup` or a fixed move order, and the game morphisms of G7 can be stated by
    membership rather than `Perm` (MoveGen review C3).
17. **Glue lemmas are stated for `Forces` and lean on core list lemmas.** Four lemmas (L4.8–L4.10
    and L2.19) replace the prototype's six (`of_play_eq`, `all_nil`, `all_cons`, `iff_best`,
    `iff_refuted`, `iff_cons`/`iff_nil`); the list walking is core's `List.forall_mem_cons`.
18. **`Forces.trans` (O8) is proved now**, ahead of Stage 3, because it is five lines and it is the
    lemma that splits a long forced win into "reach a position already proved won" plus that proof.
19. **Deviations from THEOREMS, by name or shape** (for the theorem architect; DESIGN §12 lists
    the edits THEOREMS needs):
    - `searchWin`/`searchWin_iff` (G5) are `searchForces`/`searchForces_iff`, since the search
      decides any decidable target.
    - `turn_play` (G1) takes `x` and `m` implicitly and only the membership explicitly.
    - `WinsIn.mono` (G3) is reached by dot notation through `Forces.mono` (§2.2).
    - `not_wins_of_stalemate` (G2) has no turn hypothesis; it is stronger (L2.7).
    - `checkOnlyMove_sound` (C7) concludes `WinsIn (G.turn x) n x`, with the budget counted at `x`,
      not `… (G.play x best)` (DESIGN §12, "C7 and O2").
    - `Cert`'s leaf (C1) is `goal`, not `mate`, since a certificate proves any `Forces` claim.
    - The toy games (G1) are in the library file (§5), not in `test/`: they cost well under a
      second and document the definitions.
    - `turn_ne_both` (L2.21), `forces_common_budget` (L2.22), `wins_attacker_iff` (L2.23),
      `wins_defender_iff` (L2.24), `OnlyWinningMove.winsIn_play` (L2.25),
      `wins_iff_of_moves_eq_nil` (L2.20) and `OnlyWinningMove.of_refuted` (L2.19) are new.
20. **One certificate checker for the attacker's role** (Round 4). `checkForces` hardcodes the
    attacker's side of the three rules; it is not written generically in the role. So survival
    certificates (C4), where the checked side is the defender, will be a second checker with its
    own soundness proof, mirroring the dual rules, rather than an instance of this one. THEOREMS
    C4's hope of one shared checker does not come for free; it was judged not worth an extra
    parameter on every Stage 1 claim.
21. **Equality of states is not a field** (Round 4). The trap checker (C5) will need
    `DecidableEq G.State` to recognise a returning state; it takes it as an instance argument of
    `checkTrap`, not as a field of `Game`, by the principle of choice 13: do not burden every
    instance with what one checker needs.

---

## 7. Not in this module, and open items

Not here:

- `Game.chess`, `Chess.WinsIn`, `Chess.MateIn`, `Chess.Wins`, `Chess.OnlyWinningMove`, the FEN and
  UCI parsers: `Chess.ChessGame`.
- `Holds`, `Trap`, `holds_iff_not_forces`, the game value, `Optimal` (G9, G10, O0–O7): Stage 3.
  Nothing here needs to change for them: the `replies` guard is what the trap duality requires.
- Survival and trap certificates (C4, C5), and the `Refutation` sum type of THEOREMS C7: Stage 3.
- `Game.Hom` and `winsIn_iff` along a morphism (G7): Stage 2/3, stated by membership (choice 16).
- Ranked-set certificates (C6): Stage 5.

Open, for the critic and the owner:

1. **Stage 3 refutations.** When trap refutations arrive, does `checkOnlyMove` change its `refs`
   type to `List (G.Move × Refutation G)` (a breaking change to every generated only-move file), or
   does a second checker `checkOnlyMoveWithTraps` sit beside it? The draft prefers the second.
2. **Kernel cost of the `replies` case.** It names `G.moves x` twice (non-emptiness, coverage). If a
   measurement on chess shows the kernel evaluating it twice, merge the two conjuncts into one
   `match G.moves x with | [] => false | ms => decide (∀ m ∈ ms, …)`, and adjust L4.1. The per-node
   route (§4.1) is unaffected, since it computes the move list once in `hl`. The search's
   `defenderStep` (D3.1) has the same shape (`isEmpty` and `all`) and takes the same fix, in the
   same change, if the measurement calls for it.
3. **`Wins.exists_mateIn` uses classical `by_cases`.** It could be made constructive by placing it
   after D3.5; it is in §2 because it is a law, not a computation, and [kernel] allows
   `Classical.choice`.
4. **Names.** `forces_attacker_zero_iff`, `forces_attacker_succ_iff`, `forces_defender_iff` read
   the conclusion and say whose turn it is. The alternative `Forces.attacker_succ_iff` (dot
   notation on a hypothesis) does not fit, since these lemmas take no `Forces` hypothesis.

---

## 8. Checklist for the translator

Status after Round 4 (all done; `lake build` succeeds with no warnings).

- [x] `import Chess.Basic` only.
- [x] Section order as in "Contents of the file"; `Cert` between the two `namespace Game` blocks.
- [x] Every docstring above, word for word, on its declaration, its fields and its constructors
      (lemma tags moved to a trailing "THEOREMS …" sentence, §0).
- [x] Never a bare `Move` or `State` inside `namespace Game`.
- [x] `[DecidablePred T]` only in `section Search` and `section Certificates`.
- [x] No `sorry`; `#print axioms` for `checkWin_sound`, `checkOnlyMove_sound`, `searchForces_iff`
      shows at most `propext`, `Classical.choice`, `Quot.sound` (the output is recorded in
      `docs/process/Game.md`, Rounds 3 and 4).
- [x] The tests T1–T14 elaborate, and T6 also by `rfl`.
- [x] Record in `docs/process/Game.md` every place where the English had to change for the Lean to
      go through, and every [cheap] lemma that turned out not to be (none did).
