# Specification of `Chess.Game`

Role: English specification writer (Round 1); translator (Rounds 2–3); refiner (Round 4);
interface round (Round 5, ROADMAP step 5); review fixes of Round 5 (Round 6).
Date: 2026-11-01 (Rounds 1–4); 2026-11-02 (Rounds 5–6).
Status: Round 7 (2026-11-02: the only-move root glue L4.19–L4.22, and §4.1/§4.3 on what a generated file must write; documentation fixes from its review, the same day, in §4.1 and §4.3 only; then two docstring fixes, the same day: the `Forces` docstring in §1 and the interface paragraph of the `Cert` module docstring). The English was revised after the Round 1 critique (Round 2), where the
translation into `Chess/Game.lean` forced a decision (Round 3), and after the Round 3 critique of
the Lean (Round 4); `docs/process/Game.md` lists every change. Items marked *(checked)* were
elaborated in Lean 4.28; since Round 3 every item of this spec is in the library and builds.
Round 5 split the file at the trust boundary (Game review C2), gave the only-move checker a
certificate structure, froze the interface of generated certificate files, and added diagnostics
for rejected certificates (Game review C3). Round 6 fixed the review of Round 5: two glue lemmas
for defender nodes (L4.17, L4.18), so that the frozen interface needs no lemma of core, and a
per-node test of the glue (T20).

Files (since Round 5): `Chess/Game.lean`, which only imports the five files of the module and
carries the module docstring; `Chess/Game/Defs.lean` (§1), `Chess/Game/Laws.lean` (§2),
`Chess/Game/Search.lean` (§3), `Chess/Game/Cert.lean` (§4) and `Chess/Game/Examples.lean` (§5).
Depends on: `Chess.Basic`, and only for `Color`, `Color.other` and the
lemmas `Color.other_other`, `Color.self_ne_other`, `Color.eq_other_iff_ne` (Basic §1). Core only.
Refines DESIGN §6.1–§6.3, §7.2, §7.4 and §8.5. Theorem targets: **G1** (the interface; the chess
instance is `ChessGame`'s), **G2**, **G3**, **G4**, **G5**, **G6**, **O2** (`wins_iff`), **C1**,
**C2**, **C3**, **C7** (THEOREMS §4–§6), and the definition of O8 (`Forces`, with `Forces.trans`).

What a reader must trust from this module: the definitions of §1 only (`Game`, `DefenderMated`,
`Forces`, `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`), which are exactly the file
`Chess/Game/Defs.lean`. Everything in §2–§4 is either a theorem or an executable function with a
soundness theorem (and, for `searchForces` and `checkForces`, completeness); the diagnostics of
§4.2 are executable functions that no theorem about a game uses. For chess, since G8, a headline
can be read through `Chess.Spec.Winning` instead, and then not even §1 is trusted.

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
  "THEOREMS G3." (so the docstring opens with the claim). A qualifier inside the tag is dropped:
  "(C1, general)" becomes "THEOREMS C1." (L4.1, L4.4).
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
  (Search, Certificates, Diagnostics): Lean includes an instance variable in every theorem that mentions `T`,
  and warns when it is unused *(checked)*.
- Namespaces: everything lives in `namespace Chess`. `Game` and everything about games live in
  `namespace Chess.Game`; the certificate types are `Chess.Cert`, `Chess.OnlyMoveCert` and
  `Chess.Cert.Rejection`. Names below are given relative to `Chess`. Every file opens
  `namespace Chess`. In `Defs.lean`, `namespace Game` opens right after D1.2. `Laws.lean`,
  `Search.lean` and `Examples.lean` open `namespace Game` at once. `Cert.lean` declares D4.1 and
  D4.5 in `namespace Chess`, opens `namespace Game` for D4.2–D4.4 and the sections Certificates
  and PerNode, closes it to declare D4.6 (`Cert.Rejection`), and opens it again for D4.7–D4.9 and
  the section Diagnostics. `section Laws`, `section Search`, `section Certificates`,
  `section PerNode`, `section Diagnostics` and `namespace Toy` sit inside `namespace Game`.
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
  such pair; `oc` an only-move certificate (`OnlyMoveCert G.Move`).
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

### Files and their contents, in order

Since Round 5 the module is six files, split at the trust boundary as Game review C2 proposed.
Every declaration kept its name, its docstring and its place relative to its neighbours; only the
module docstrings are new.

1. `Chess/Game.lean`: `import` of the five files below, and the module docstring of `Chess.Game`.
   Downstream code imports `Chess.Game` as before.
2. `Chess/Game/Defs.lean` (imports `Chess.Basic`): its module docstring; `/-! ## Games -/`
   (trusted): D1.1–D1.9.
3. `Chess/Game/Laws.lean` (imports `Defs`): its module docstring; `/-! ## Laws -/`,
   `section Laws`: L2.1–L2.25, under the subheadings `/-! ### … -/` of §2.1–§2.5 ("One step of
   forcing, read backwards", "Budgets and targets", "Winning", "Exact distance", "The only winning
   move").
4. `Chess/Game/Search.lean` (imports `Laws`): its module docstring; `/-! ## Search -/`,
   `section Search`: D3.1–D3.4, L3.1–L3.5, the instances D3.5–D3.6.
5. `Chess/Game/Cert.lean` (imports `Laws`, and **not** `Search`): its module docstring;
   `/-! ## Certificates -/`: D4.1 and D4.5 (outside `namespace Game`), D4.2–D4.4, then
   `section Certificates` (L4.1–L4.3, L4.15, L4.4–L4.7) and, under
   `/-! ### Lemmas for per-node kernel proofs -/`, `section PerNode` (L4.8–L4.10, L4.12,
   L4.17–L4.22); `/-! ## Diagnostics -/`: D4.6 (outside `namespace Game`), D4.7–D4.9, then
   `section Diagnostics` (L4.13–L4.14, L4.16).
6. `Chess/Game/Examples.lean` (imports `Search` and `Cert`): its module docstring;
   `/-! ## Examples -/`, `namespace Toy`: D5.1–D5.2 and the tests T1–T20.

`Search` and `Cert` do not import each other: a certificate is checked without the search, and the
search is not needed to state or check any certificate. `Examples` is imported by `Chess/Game.lean`,
so the toy tests still run on every library build (they cost well under a second).

### The module docstrings, word for word

`Chess/Game.lean`:

```
# Game

Two-player games with alternating turns, forced play into a target, forced wins, a bounded search
that decides them, and a certificate checker whose acceptance proves them. Chess is one instance
(`Chess.ChessGame`); nothing here mentions a piece. This file imports the five files of the
module, which follow the trust boundary. Specification: `docs/spec/Game.md`; every definition
carries the docstring given there.

## Main definitions

* `Game`, `Game.Forces`, `Game.WinsIn`, `Game.Wins`, `Game.MateIn`, `Game.OnlyWinningMove`: games,
  forcing and winning (`Chess.Game.Defs`).
* `Game.searchForces`: bounded search, by structural recursion on the budget
  (`Chess.Game.Search`).
* `Cert`, `OnlyMoveCert`, `Game.checkWin`, `Game.checkOnlyMove`: certificates proposed by an
  untrusted search, and their checkers; `Game.firstFailure` and its variants say where a rejected
  certificate fails (`Chess.Game.Cert`).

## Main statements

* The laws G2–G4, G6, O2 and O8 (`Chess.Game.Laws`).
* `searchForces_iff` (G5): the search decides forcing.
* `checkWin_sound`, `checkOnlyMove_sound` (C1, C7), and the glue for proofs that check one node at
  a time (C3).

## Implementation notes

* Only `Chess.Game.Defs` is trusted. `Chess.Game.Laws` proves facts about its definitions;
  `Chess.Game.Search` and `Chess.Game.Cert` are executable, each with a soundness theorem, and
  import `Laws` but not each other; `Chess.Game.Examples` holds two toy games and the tests.
* `Chess.Game.Cert` is the interface of generated certificate files; its module docstring says
  which names they may use.
```

`Chess/Game/Defs.lean`:

```
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
```

`Chess/Game/Laws.lean`:

```
# Game: laws

What follows from the definitions of `Chess.Game.Defs`: one step of forcing read backwards,
monotonicity in the budget and composition of forcing, that no state is won by both sides, that
stalemate is no loss, exact distance to mate, and the only winning move. Specification:
`docs/spec/Game.md` §2.

## Main statements

* `Forces.mono` (G3), `Forces.trans` (O8), `WinsIn.not_both` and `Wins.not_both` (G4),
  `winsIn_zero_iff` and `not_wins_of_stalemate` (G2), `MateIn.unique` (G6),
  `OnlyWinningMove.wins_iff` (O2).
* `forces_attacker_zero_iff`, `forces_attacker_succ_iff`, `forces_defender_iff`: one step of
  forcing, read backwards.
* `wins_attacker_iff`, `wins_defender_iff`: one step of winning, read backwards (for G9, G10).
* `OnlyWinningMove.of_refuted`: a move is the only winning move when it wins and the opponent wins
  after every other move. `OnlyWinningMove.winsIn_play`: a fastest win starts with it.

## Implementation notes

* Every proof goes by cases or induction on `Forces`; nothing here computes.
```

`Chess/Game/Search.lean`:

```
# Game: search

A bounded search that decides forcing for any decidable target, by structural recursion on the
budget, and its correctness. Specification: `docs/spec/Game.md` §3.

## Main definitions

* `Game.defenderStep`: the defender rule, given a test for the attacker nodes below it.
* `Game.attackerForces`, `Game.defenderForced`: the search for the side to move, as attacker and
  as defender.
* `Game.searchForces`: the search for a given attacker.

## Main statements

* `searchForces_iff` (G5): the search decides forcing.
* `Forces.decidable`, `MateIn.decidable`: hence forcing within a budget, and mating in exactly a
  budget, are decidable, and `decide` proves small claims.

## Implementation notes

* The search branches over every attacker move at every attacker node, so it is feasible only for
  small budgets. Long wins are proved by certificates (`Chess.Game.Cert`), which do not depend on
  this file.
```

`Chess/Game/Cert.lean`:

```
# Game: certificates

Certificates for forcing claims, proposed by an untrusted search; the Boolean checkers that replay
them against the rules of the game; the lemmas that turn acceptance into the claim; and diagnostics
that say where a rejected certificate fails. This file is the interface of generated certificate
files. Specification: `docs/spec/Game.md` §4; every definition below carries the docstring given
there.

## Main definitions

* `Cert`: a finite strategy tree for the attacker.
* `OnlyMoveCert`: the evidence for an only-move claim, a win certificate after the best move and
  refutations of the other moves.
* `Game.checkForces`, `Game.checkWin`, `Game.checkOnlyMove`: the checkers.
* `Game.firstFailure`, `Game.firstFailureWin`, `Game.firstFailureOnlyMove`: the path to the first
  node a checker rejects, and the condition that fails there (`Cert.Rejection`).

## Main statements

* `checkForces_sound`, `checkForces_complete`, `checkWin_sound`, `checkWin_complete` (C1, C2), and
  `checkOnlyMove_sound` (C7).
* `Forces.of_play_eq`, `Forces.move_of_play_eq`, `Forces.replies_of_moves_eq`,
  `Forces.forall_mem_cons`, `Forces.forall_mem_nil`, `WinsIn.of_mated`, and for the root of an
  only-move claim `OnlyWinningMove.of_moves_eq`, `.refuted_nil`, `.refuted_cons_self`,
  `.refuted_cons` (C3): the glue for proofs that check one node at a time.
* `firstFailure_eq_none_iff`, `firstFailureOnlyMove_eq_none_iff`: the diagnostics find a failure
  exactly when the checkers reject.

## Implementation notes

* Nothing here is trusted. The checkers are executable Boolean functions with soundness theorems,
  and `checkForces` is also complete. The diagnostics are for reading a rejected certificate; no
  theorem about a game depends on them.
* The generated-file interface (`docs/spec/Game.md` §4.3). A generated certificate file states its
  claims with the definitions of `Chess.Game.Defs` (for chess, their abbreviations in
  `Chess.ChessGame`), writes its certificates as values of `Cert` and `OnlyMoveCert`, and proves
  its claims only through `checkWin_sound`, `checkOnlyMove_sound`, the glue lemmas above,
  `OnlyWinningMove.of_refuted`, literal checkpoint equations for `Position.play` and
  `Game.chess.moves` proved by `decide +kernel`, and for chess `mem_chess_moves`. It never applies
  a constructor of `Forces`, so the constructors may change. The test file `ChessTest.Interface`
  records the signatures of these names.
```

`Chess/Game/Examples.lean`:

```
# Game: examples

Two take-away games on which every definition of `Chess.Game` runs instantly under `decide`, and
tests of the search, the checkers and the diagnostics on them. Specification: `docs/spec/Game.md`
§5.

## Main definitions

* `Game.Toy.takeAway`, `Game.Toy.takeAwayStalemate`: take one or two counters from a pile.

## Main statements

* `Game.Toy.takeAway_onlyWinningMove`: an only winning move, proved through the only-move checker.
```

---

## 1. Section "Games" (trusted)

File `Chess/Game/Defs.lean`. No `variable` line: every definition binds its arguments explicitly.

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
escapes unless the state is in `T`, and play that never reaches `T` is never forced."

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

File `Chess/Game/Laws.lean`.

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

File `Chess/Game/Search.lean`.

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

File `Chess/Game/Cert.lean`, which imports `Chess.Game.Laws` but not `Chess.Game.Search`.

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

`Cert` is declared in `namespace Chess`, before the `namespace Game` that holds the checkers.
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

### D4.4 `Game.checkOnlyMove (G : Game) (n : Nat) (x : G.State) (best : G.Move) (oc : OnlyMoveCert G.Move) : Bool`

```lean
G.checkWin (G.turn x) n x (.move best oc.next) &&
  decide (∀ m ∈ G.moves x, m ≠ best → m ∈ oc.refs.map Prod.fst) &&
  oc.refs.all fun r => G.checkWin (G.turn x).other oc.refBudget (G.play x r.1) r.2
```
*(checked)*

Docstring: "Accepts only if `best` is the only winning move at `x` and the side to move wins
within `n` moves, counted at `x` with `best` included. Accepting proves both
(`checkOnlyMove_sound`). `oc.next` is the win certificate for the state after `best`; `oc.refs`
gives, for every other available move, a certificate that the opponent wins within `oc.refBudget`
moves after it. It rejects true claims in which some alternative does not lose but only draws:
this checker cannot certify those, and refutations by traps are future work."

The budget convention is DESIGN §7.2's: **`n` is counted at `x`, before the best move**, like
every budget in the library. So for the Gotham position the headline uses `n = 11` with no
subtraction anywhere.

**Arguments and certificate (Round 5).** The arguments are the claim: the state, the best move
and the budget of the win, which all occur in the conclusion of `checkOnlyMove_sound`. The
evidence is one `OnlyMoveCert` value (D4.5): the certificate after `best`, the refutation budget
and the refutations. The refutation budget is not part of the claim (the conclusion only says that
alternatives do not win), so it belongs to the certificate; this is the same principle as design
choice 12, which keeps the claim's budget out of `Cert`. Until Round 5 the checker took six
positional arguments, `checkOnlyMove n k x best next refs`, two of them adjacent budgets (Game
review C3.3). A generated call now names every part of the evidence:

```lean
Game.chess.checkOnlyMove 11 gotham (uci "b7b2")
  { next := …, refBudget := 10, refs := [(uci "a5a2", …), …] } = true
```

### D4.5 `structure OnlyMoveCert (M : Type) : Type` (namespace `Chess`, not `Chess.Game`)

```lean
structure OnlyMoveCert (M : Type) where
  next : Cert M
  refBudget : Nat
  refs : List (M × Cert M)
  deriving Inhabited
```
*(checked)*

Docstring: "The evidence for an only-move claim, proposed by an untrusted search and checked by
`Game.checkOnlyMove`: a win certificate for the state after the best move, and refutations of the
other moves. The claim itself (the state, the best move and the budget of the win) is not part of
it. It is data; it is never trusted."
Field docstrings:

- `next`: "The win certificate for the state after the best move."
- `refBudget`: "The budget within which the opponent wins after each refuted move; one budget
  serves them all."
- `refs`: "For each refuted move `m`, a certificate that the opponent wins within `refBudget` after
  `m`. Pairs for moves that are not available, and repeated moves, are allowed; every pair must
  check."

Declared right after D4.1, in `namespace Chess`. A future kind of refutation (spec open item 1:
traps, Stage 3) can be a new field with a default value, so a file generated before it still
elaborates.

### Lemmas of §4

```lean
section Certificates
variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat}
  {x : G.State} {best : G.Move} {c : Cert G.Move} {oc : OnlyMoveCert G.Move}
```

(Round 5: `k`, `next` and `refs` left the line with the old signature of `checkOnlyMove`; `oc`
joined it.)

| ID | English | Lean | Tag |
|---|---|---|---|
| L4.1 | (C1, general) If the checker accepts a certificate, the attacker forces the target. | `theorem checkForces_sound : ∀ {n : Nat} {x : G.State} (c : Cert G.Move), G.checkForces a T n x c = true → G.Forces a T n x` | core *(checked)* |
| L4.2 | If every pair of a reply list checks, the attacker forces the target after each listed move. | `theorem checkReplies_sound : ∀ {n : Nat} {x : G.State} (rs : List (G.Move × Cert G.Move)), G.checkReplies a T n x rs = true → ∀ r ∈ rs, G.Forces a T n (G.play x r.1)` | core *(checked)* |
| L4.3 | If after each move of `ms` some certificate checks with budget `n`, then some reply list whose moves are exactly `ms`, in the same order, checks. | `theorem exists_checkReplies (ms : List G.Move) (h : ∀ m ∈ ms, ∃ c, G.checkForces a T n (G.play x m) c = true) : ∃ rs : List (G.Move × Cert G.Move), rs.map Prod.fst = ms ∧ G.checkReplies a T n x rs = true` | core |
| L4.15 | Every pair of a reply list checks exactly when each certificate in it checks after its move. | `theorem checkReplies_eq_true_iff {rs : List (G.Move × Cert G.Move)} : G.checkReplies a T n x rs = true ↔ ∀ r ∈ rs, G.checkForces a T n (G.play x r.1) r.2 = true` | core (Round 5, for L4.16) *(checked)* |
| L4.4 | (C2, general) Every true forcing claim has an accepted certificate: the format is not lossy. | `theorem checkForces_complete (w : G.Forces a T n x) : ∃ c, G.checkForces a T n x c = true` | core |
| L4.5 | (C1) If the checker accepts a win certificate, the attacker wins within the budget. | `theorem checkWin_sound (h : G.checkWin a n x c = true) : G.WinsIn a n x` | core |
| L4.6 | (C2) Every forced win has an accepted win certificate. | `theorem checkWin_complete (w : G.WinsIn a n x) : ∃ c, G.checkWin a n x c = true` | core |
| L4.7 | (C7) If the only-move checker accepts, `best` is the only winning move at `x` and the side to move wins within `n`. | `theorem checkOnlyMove_sound (h : G.checkOnlyMove n x best oc = true) : G.OnlyWinningMove x best ∧ G.WinsIn (G.turn x) n x` | core |

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
- L4.15: induction on `rs`, each case `simp [checkReplies]` (with the induction hypothesis).
- L4.4: `induction w`. `goal`: `⟨.goal, by simp [checkForces, h]⟩`. `move`: from the induction
  hypothesis `⟨c, hc⟩`, take `.move m c`. `replies`: L4.3 on `G.moves x` with the induction
  hypothesis gives `rs` with `rs.map Prod.fst = G.moves x`; take `.replies rs`; coverage holds
  because the map is the move list itself.
- L4.5, L4.6: L4.1 and L4.4 at `T := G.DefenderMated a`.
- L4.7: `simp only [checkOnlyMove, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h`.
  From the first conjunct: L4.5 gives `G.WinsIn (G.turn x) n x`; and `cases n` on it (budget 0
  makes `checkForces` false) with one more `simp only [checkWin, checkForces, …]` gives
  `best ∈ G.moves x` and the win after `best` with budget `n - 1`. For each other available move,
  coverage finds its pair in `oc.refs` and L4.5 gives the opponent's win within `oc.refBudget`
  after it. L2.19 assembles `OnlyWinningMove x best`.

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
| L4.8 | (C3) If playing `m` at `x` gives `y`, every forcing fact about `y` holds after `m`. | `theorem Forces.of_play_eq (h : G.play x m = y) (w : G.Forces a T n y) : G.Forces a T n (G.play x m)` | core |
| L4.9 | (C3) Attacker node: if the attacker is to move, `m` is available, playing it gives `y`, and `y` is forced within `n`, then `x` is forced within `n + 1`. | `theorem Forces.move_of_play_eq (ht : G.turn x = a) (hm : m ∈ G.moves x) (h : G.play x m = y) (w : G.Forces a T n y) : G.Forces a T (n + 1) x` | core |
| L4.10 | (C3) Defender node: if the defender is to move, its available moves are the explicit non-empty list `m :: ms`, and each of them leads to a state forced within `n`, then `x` is forced within `n`. | `theorem Forces.replies_of_moves_eq (ht : G.turn x = a.other) (hl : G.moves x = m :: ms) (h : ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m')) : G.Forces a T n x` | core |
| L4.12 | (C3) Mate leaf: if the defender is to move and has been mated, the attacker wins within any budget. | `theorem WinsIn.of_mated (ht : G.turn x = a.other) (h : G.Mated x) : G.WinsIn a n x` | core (Round 5) *(checked)* |
| L4.17 | (C3) The end of a defender's move list: every move of the empty list leads to a state forced within `n`. | `theorem Forces.forall_mem_nil : ∀ m' ∈ ([] : List G.Move), G.Forces a T n (G.play x m')` | core (Round 6) *(checked)* |
| L4.18 | (C3) One move of a defender's move list: if `m` leads to a state forced within `n`, and so does every move of `ms`, then so does every move of `m :: ms`. | `theorem Forces.forall_mem_cons (h : G.Forces a T n (G.play x m)) (t : ∀ m' ∈ ms, G.Forces a T n (G.play x m')) : ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m')` | core (Round 6) *(checked)* |
| L4.19 | (C3) Only-move root: if `a` is to move, its available moves are the explicit list `ms`, `m` is one of them, `a` wins within `n` after `m`, and after every other move of `ms` the opponent wins within some budget, then `m` is the only winning move at `x`. | `theorem OnlyWinningMove.of_moves_eq (ht : G.turn x = a) (hl : G.moves x = ms) (hm : m ∈ ms) (w : G.WinsIn a n (G.play x m)) (hr : ∀ m' ∈ ms, m' ≠ m → ∃ k, G.WinsIn a.other k (G.play x m')) : G.OnlyWinningMove x m` | core (Round 7) *(checked)* |
| L4.20 | (C3) The end of a list of alternatives: every move of the empty list other than `m` is refuted. | `theorem OnlyWinningMove.refuted_nil : ∀ m' ∈ ([] : List G.Move), m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')` | core (Round 7) *(checked)* |
| L4.21 | (C3) The move `m` itself in a list of alternatives: if every move of `ms` other than `m` is refuted, so is every move of `m :: ms` other than `m`. | `theorem OnlyWinningMove.refuted_cons_self (t : ∀ m' ∈ ms, m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')) : ∀ m' ∈ m :: ms, m' ≠ m → ∃ k, G.WinsIn a k (G.play x m')` | core (Round 7) *(checked)* |
| L4.22 | (C3) One refuted move in a list of alternatives: if the opponent `a` wins within `k` after `m'`, and every move of `ms` other than `m` is refuted, then so is every move of `m' :: ms` other than `m`. | `theorem OnlyWinningMove.refuted_cons {m' : G.Move} {k : Nat} (w : G.WinsIn a k (G.play x m')) (t : ∀ m'' ∈ ms, m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'')) : ∀ m'' ∈ m' :: ms, m'' ≠ m → ∃ k, G.WinsIn a k (G.play x m'')` | core (Round 7) *(checked)* |

Proofs: L4.8 `h ▸ w`; L4.9 `.move m ht hm (h ▸ w)`; L4.10
`.replies ht (by rw [hl]; exact List.cons_ne_nil _ _) (by rw [hl]; exact h)`; L4.12
`.goal ⟨ht, h⟩`; L4.17 `fun _ h => nomatch h`; L4.18 `List.forall_mem_cons.2 ⟨h, t⟩`;
L4.19 `subst ht hl` and L2.19; L4.20 `fun _ h => nomatch h`; L4.21
`List.forall_mem_cons.2 ⟨fun h => (h rfl).elim, t⟩`; L4.22 `List.forall_mem_cons.2 ⟨fun _ => ⟨k, w⟩, t⟩`.
`end PerNode`.

L4.19–L4.22 (Round 7) close the last gap of the interface, at the root of an only-move claim. L2.19
needs, for every available move other than the best, a win of the opponent; a per-node proof has
these as separate theorems, one per alternative, and must gather them over the explicit move list
without core's list lemmas, as L4.17 and L4.18 do at defender nodes. In L4.20–L4.22 `a` is the
side that refutes, that is, the opponent of the side to move at `x`. L4.19 takes `ht : G.turn x =
a` and states everything with `a` instead of `G.turn x`, so that a generated file's types say
`.black` and `.white` and the elaborator never has to evaluate the turn of a position written
`fen "…"`. The generated shape at the root, for chess (as in `ChessDemo/GothamCert.lean`):

```lean
theorem refutes_c3b2 : WinsIn .white 1 (Puzzles.gotham.play c3b2) :=
  Game.Forces.of_play_eq (by decide +kernel : Puzzles.gotham.play c3b2 = p57) w62
…
theorem moves_root : Game.chess.moves Puzzles.gotham = [c3b2, …, b7b2, …] := by decide +kernel
theorem refutations : ∀ m ∈ Game.chess.moves Puzzles.gotham, m ≠ b7b2 →
    ∃ k, WinsIn .white k (Puzzles.gotham.play m) := by
  rw [moves_root]
  exact
    Game.OnlyWinningMove.refuted_cons refutes_c3b2 <|
    …
    Game.OnlyWinningMove.refuted_cons_self <|
    …
    Game.OnlyWinningMove.refuted_nil
theorem onlyWinningMove : OnlyWinningMove Puzzles.gotham b7b2 :=
  Game.OnlyWinningMove.of_moves_eq (by decide +kernel) moves_root (by decide +kernel)
    (Game.Forces.of_play_eq play_best w60) (moves_root ▸ refutations)
```

The refutations are a theorem of their own, stated over `Game.chess.moves`, because they say more
than the only-move claim: a forced mate for the opponent after each alternative, where
`OnlyWinningMove` says only that the side to move does not win (review of Round 7;
`ChessDemo.gotham_refuted` restates it). The move-list equation `moves_root` carries them between
`Game.chess.moves Puzzles.gotham` and the explicit list, with `rw` in one direction and `▸` in the
other; neither names a lemma of core.

L4.12 (Round 5) closes the gap at mate leaves: before it, a per-node proof of a mate leaf had to
apply the constructor `Forces.goal` (the prototype's `WinsIn.mate`), which the frozen interface of
§4.3 forbids. L4.17 and L4.18 (Round 6) close the gap at defender nodes, described below. Their tag
"THEOREMS C3." follows L4.8–L4.10. (L4.11 is not reused: it was the Round 1 label of what is now
L2.19.)

L4.10 needs `G.moves x = m :: ms` **exactly**: the literal list the generator returns, in its order
and with any repetitions, since `hl` is proved by evaluation. Choice 16's "order carries no
meaning" is about the definitions; it does not let a per-node proof list the moves in another
order. The only-move root of a per-node proof is L2.19.

A per-node defender proof discharges the hypothesis `h` of L4.10 by walking the explicit list:
L4.18 once per move, and L4.17 at the end, as the prototype did with its `all_cons` and `all_nil`
(`chess-lean/ChessProof/Cert.lean`). Round 5 left this step to core's `List.forall_mem_cons` and
`List.forall_mem_nil`, which the interface of §4.3 does not list. Round 6 added L4.17 and L4.18
(review of Round 5) so that the interface is self-sufficient: a generated file names no lemma of
core, whose names and shapes may change with the toolchain, and such a change is then absorbed by
the two proofs above instead of by every generated file. The intended generated shape, for chess
(names as in `ChessGame`), is:

```lean
theorem w4 : Chess.WinsIn .black 9 p3 :=
  Game.WinsIn.of_mated (by decide +kernel) (by decide +kernel)
theorem w5 : Chess.WinsIn .black 10 p2 :=
  Game.Forces.move_of_play_eq (by decide +kernel) (mem_chess_moves.2 (by decide +kernel))
    (by decide +kernel : p2.play m₁ = p3) w4
theorem w6 : Chess.WinsIn .black 10 p1 :=
  Game.Forces.replies_of_moves_eq (by decide +kernel)
    (by decide +kernel : Game.chess.moves p1 = [m₂]) <|
    Game.Forces.forall_mem_cons (Game.Forces.of_play_eq
      (by decide +kernel : p1.play m₂ = p2) w5) <|
    Game.Forces.forall_mem_nil
```

(Round 7: this is the shape `scripts/gen_cert.py` emits. Two details of it are forced by the
elaborator, not by the kernel. The move list is written `Game.chess.moves p1`, not `legalMoves p1`,
and an attacker's move is shown available with `mem_chess_moves` (`Chess.ChessGame.Fide`), not
`mem_legalMoves`: the hypotheses of L4.9 and L4.10 then match the proofs' types syntactically.
Written with `legalMoves`, the two sides are equal only after unfolding the projection
`Game.chess.moves`, and the elaborator's unifier unfolded `legalMoves p1` first and began to
evaluate it, which ran out of heartbeats on positions with many moves.)

T20 (§5) is this shape on the toy game, a whole win proved node by node with the glue alone, and
it is checked on every build.

At an attacker node the membership `m ∈ G.moves x` may be proved by any means. For chess,
`mem_chess_moves.2 (by decide +kernel : Legal p m)` decides legality of one move (about 0.1 s on
the Gotham certificate's nodes, Round 7) instead of generating all of them (about 0.5 s after
MoveGen's Round 5 king-safety change, 1.5 s before it; MoveGen review C2). This is why `Game` has no
`isLegal` field (design choice 13).

### 4.2 Diagnostics (Round 5)

When a certificate of a few hundred nodes is rejected, `checkWin … = false` says nothing about
where. The diagnostics answer that: they walk the certificate as the checker does and return the
path of moves from the root to the first node that fails, with the condition that fails there.
They are executable functions for `#eval` and `#guard`, run by a person or by the generator after a
rejection. No theorem about a game uses them, so they are not trusted (Game review C3.4). They are
nevertheless proved to agree with the checkers (L4.13, L4.16): a diagnostic returns `none` exactly
when its checker accepts, so it never reports a failure in an accepted certificate, nor misses one
in a rejected certificate.

#### D4.6 `inductive Cert.Rejection (M : Type) : Type` (namespace `Chess`, after `end Game`)

```lean
inductive Cert.Rejection (M : Type) where
  | notInTarget
  | noBudget
  | notAttackerTurn
  | unavailable (m : M)
  | notDefenderTurn
  | noDefenderMove
  | missingReply (m : M)
  | unrefuted (m : M)
  deriving Repr, DecidableEq
```
*(checked)*

Docstring: "Why a checker rejects a certificate: the condition of `Game.checkForces` or
`Game.checkOnlyMove` that fails at the node where checking stops. Reported by `Game.firstFailure`
and `Game.firstFailureOnlyMove`; it is never trusted."
Constructor docstrings:

- `notInTarget`: "A `goal` leaf at a state that is not in the target."
- `noBudget`: "A `move` node with no budget left."
- `notAttackerTurn`: "A `move` node at a state where the attacker is not to move."
- `unavailable`: "A `move` node whose move `m` is not available."
- `notDefenderTurn`: "A `replies` node at a state where the defender is not to move."
- `noDefenderMove`: "A `replies` node at a state where the defender has no available move."
- `missingReply`: "A `replies` node with no pair for the available move `m`."
- `unrefuted`: "An only-move certificate with no refutation of the available move `m`, which is not
  the best move."

One constructor per conjunct of D4.2 and per coverage conjunct of D4.4, in the checker's order.
`Repr` is derived so that `#eval` prints a rejection, `DecidableEq` so that tests compare one by
`decide` or `#guard`. The name lives under `Cert` (`Chess.Cert.Rejection`) because it describes a
certificate, not a game.

#### D4.7 `Game.firstFailure` and `Game.firstFailureReplies`, by mutual structural recursion

```lean
mutual
def firstFailure (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → Cert G.Move → Option (List G.Move × Cert.Rejection G.Move)
  | _, x, .goal => if T x then none else some ([], .notInTarget)
  | 0, _, .move _ _ => some ([], .noBudget)
  | k + 1, x, .move m next =>
      if G.turn x ≠ a then some ([], .notAttackerTurn)
      else if m ∉ G.moves x then some ([], .unavailable m)
      else match G.firstFailure a T k (G.play x m) next with
        | some (ms, r) => some (m :: ms, r)
        | none => none
  | n, x, .replies rs =>
      if G.turn x ≠ a.other then some ([], .notDefenderTurn)
      else if G.moves x = [] then some ([], .noDefenderMove)
      else match (G.moves x).find? (fun m => m ∉ rs.map Prod.fst) with
        | some m => some ([], .missingReply m)
        | none => G.firstFailureReplies a T n x rs

def firstFailureReplies (G : Game) (a : Color) (T : G.State → Prop) [DecidablePred T] :
    Nat → G.State → List (G.Move × Cert G.Move) → Option (List G.Move × Cert.Rejection G.Move)
  | _, _, [] => none
  | n, x, (m, c) :: rs =>
      match G.firstFailure a T n (G.play x m) c with
      | some (ms, r) => some (m :: ms, r)
      | none => G.firstFailureReplies a T n x rs
end
```
*(checked: structural recursion through the `match`es is accepted, as for D4.2. Round 6: the
`move` case prefixes the path with a `match`, as `firstFailureReplies` does, where Round 5 used
`Option.map`; the two definitions now build the path the same way.)*

Docstring of `firstFailure`: "Finds where certificate `c` for the claim `G.Forces a T n x` fails:
`none` if `checkForces` accepts it (`firstFailure_eq_none_iff`), and otherwise `some (ms, r)`,
where `ms` is the path of moves from `x` to the first node that fails and `r` is the first
condition of `checkForces` that fails there. Conditions are tested in the order `checkForces`
states them, and the pairs of a reply list in their order. An untrusted diagnostic, for reading a
rejected certificate."

Docstring of `firstFailureReplies`: "Finds the first pair `(m, c)` of `rs` whose certificate `c`
fails with budget `n` in the state after `m` is played at `x`: `none` if every pair checks, and
otherwise the path from `x`, starting with `m`, to the first node that fails, and the condition
that fails there."

The binding rule of §0 applies as for D4.2: the docstrings name the arguments after the colon.

#### D4.8 `Game.firstFailureWin (G : Game) (a : Color) (n : Nat) (x : G.State) (c : Cert G.Move) : Option (List G.Move × Cert.Rejection G.Move)`

`G.firstFailure a (G.DefenderMated a) n x c`, as `checkWin` is `checkForces` at the target of
winning.
Docstring: "Finds where certificate `c` for the claim `G.WinsIn a n x` fails, as `firstFailure`
does for the target of `checkWin`."

#### D4.9 `Game.firstFailureOnlyMove (G : Game) (n : Nat) (x : G.State) (best : G.Move) (oc : OnlyMoveCert G.Move) : Option (List G.Move × Cert.Rejection G.Move)`

```lean
match G.firstFailureWin (G.turn x) n x (.move best oc.next) with
| some f => some f
| none =>
  match (G.moves x).find? (fun m => m ≠ best ∧ m ∉ oc.refs.map Prod.fst) with
  | some m => some ([], .unrefuted m)
  | none =>
    G.firstFailureReplies (G.turn x).other (G.DefenderMated (G.turn x).other) oc.refBudget x
      oc.refs
```
*(checked)*

Docstring: "Finds where `checkOnlyMove n x best oc` fails: `none` if it accepts
(`firstFailureOnlyMove_eq_none_iff`), and otherwise the path of moves from `x` to the first node
that fails and the condition that fails there. It tests, in this order, the win certificate
`.move best oc.next`, that every other available move has a refutation, and the refutations of
`oc.refs` in their order; the path to a node of a refutation starts with the refuted move. An
untrusted diagnostic, for reading a rejected certificate."

The refutations are walked with `firstFailureReplies`, since checking every pair of `oc.refs` for
the opponent with budget `oc.refBudget` is what `checkReplies` does (L4.15 connects the two
readings). One ambiguity is accepted: if `oc.refs` lists `best` itself and its refutation fails,
the path starts with `best`, like a path inside the win certificate. A refutation of the best move
can never check once the win certificate checks (`not_both`), so such a pair is a generator bug
either way.

#### Lemmas of §4.2

```lean
section Diagnostics
variable {G : Game} {a : Color} {T : G.State → Prop} [DecidablePred T] {n : Nat}
  {x : G.State} {best : G.Move} {oc : OnlyMoveCert G.Move}
```

| ID | English | Lean | Tag |
|---|---|---|---|
| L4.13 | The diagnostic finds no failure exactly when the checker accepts. | `theorem firstFailure_eq_none_iff : ∀ {n : Nat} {x : G.State} (c : Cert G.Move), G.firstFailure a T n x c = none ↔ G.checkForces a T n x c = true` | sanity *(checked)* |
| L4.14 | The diagnostic finds no failing pair exactly when every pair of the reply list checks. | `theorem firstFailureReplies_eq_none_iff : ∀ {n : Nat} {x : G.State} (rs : List (G.Move × Cert G.Move)), G.firstFailureReplies a T n x rs = none ↔ G.checkReplies a T n x rs = true` | sanity *(checked)* |
| L4.16 | The diagnostic of the only-move checker finds no failure exactly when that checker accepts. | `theorem firstFailureOnlyMove_eq_none_iff : G.firstFailureOnlyMove n x best oc = none ↔ G.checkOnlyMove n x best oc = true` | sanity *(checked)* |

L4.13 and L4.14 are one `mutual … end` block by structural recursion, like L4.1–L4.2. Proofs: at
`goal` and at a `move` node, `by_cases` on each tested condition and `simp` with the definitions;
when both conditions of a `move` node hold, rewrite with the recursive call and split on the
diagnostic of the child (Round 6, since the `move` case is now a `match`). At a `replies` node,
after the turn and emptiness tests, rewrite with the equations `firstFailure.eq_4` and
`checkForces.eq_4` and split on the `find?`: if it finds a missing move `m`,
`List.mem_of_find?_eq_some` and `List.find?_some` refute coverage; if it finds none,
`List.find?_eq_none` gives coverage and L4.14 finishes. L4.14: on `(m, c) :: rs`, split on
`firstFailure … c` and use L4.13. L4.16: unfold, split in the same way on the win certificate and on
the `find?`, and finish with L4.14 and L4.15. All three are [kernel]: `#print axioms` shows
`propext`, `Classical.choice`, `Quot.sound` (recorded in the axioms ledger).

### 4.3 The generated-file interface (Round 5, frozen)

Generated certificate files are the largest Lean of the project and are regenerated rather than
edited, so the names and argument orders they use are expensive to change (Game review C3). From
Round 5 on, a generated file:

- states its claims with the definitions of §1, or for chess with their abbreviations
  `Chess.WinsIn`, `Chess.OnlyWinningMove`, and names its positions with `fen "…"` (or with a name
  from `Chess.Puzzles`) and its moves either with `uci "…"` or with literal `Move` definitions
  named by their UCI writing; in the second case, the file that restates the claim proves
  `uci "…" = lit` by `decide +kernel` (as `ChessDemo.uci_b7b2` does) (review of Round 7: the
  first generated file, `ChessDemo.GothamCert`, uses literals, which are cheap for the kernel and
  the elaborator);
- writes its certificates as values of `Cert` and `OnlyMoveCert` (D4.1, D4.5);
- proves its claims only through `checkWin_sound`, `checkOnlyMove_sound` (with `checkWin` and
  `checkOnlyMove` evaluated by `decide +kernel`), the per-node glue L4.8–L4.10, L4.12 and
  L4.17–L4.22, and
  `OnlyWinningMove.of_refuted` (L2.19), with literal checkpoints `Position.play`/`Game.chess.moves`
  equations (used directly, or by `rw` and `▸`, as at the only-move root of §4.1) and, for chess,
  `mem_chess_moves` (Round 7; `mem_legalMoves` until then, see §4.1);
- **never applies a constructor of `Forces`** (`Forces.goal`, `Forces.move`, `Forces.replies`).
  The constructors' argument order is then free to change; the glue lemmas are the stable API.

The names and signatures of this interface are recorded, with their binder names (a generated file
may pass an argument by name, as in `checkWin_sound (c := …)`), in the test file
`ChessTest/Interface.lean` (`docs/spec/ChessTest.Interface.md`), so that a change fails
`lake build ChessTest`. A deliberate change updates that file in the same change and is logged in
`docs/process/Game.md`. The name `Cert` is kept (Game review C3.2: decided, not renamed); its
siblings of later stages (survival certificates C4, traps C5, ranked sets C6) will be new types
beside it, not renamings of it.

---

## 5. Section "Examples"

File `Chess/Game/Examples.lean`, which imports `Chess.Game.Search` and `Chess.Game.Cert`.

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
tests" column in a sentence (T18 and T19 are groups of examples under one comment; T20 is one
example whose proof has one `have` per node). T11 has a
docstring, since it is a named theorem: "Taking one counter is the only winning move from a pile of
4 with White to move, proved through the only-move checker (T11)." (Round 5: the text is now given
here, Game review C9.) T6 is two examples,
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
| T9 | `takeAway.checkOnlyMove 2 (.white, 4) 1 { next := .replies [(1, .move 2 .goal), (2, .move 1 .goal)], refBudget := 1, refs := [(2, .move 2 .goal)] } = true` | `by decide +kernel` *(checked)* | the only-move checker accepts |
| T10 | the same with `refs := []` `= false` | `by decide` *(checked)* | an unrefuted alternative is rejected |
| T11 | `theorem takeAway_onlyWinningMove : takeAway.OnlyWinningMove (.white, 4) 1` | `(checkOnlyMove_sound (by decide +kernel : …T9's statement… = true)).1`, the instance of T9 | soundness end to end |
| T12 | `¬ takeAwayStalemate.Wins .white (.black, 0)` | `not_wins_of_stalemate (by decide) rfl` | a stalemated defender has not lost |
| T13 | `¬ takeAwayStalemate.WinsIn .white 3 (.black, 0)` | `by decide` *(checked)* | the search agrees on stalemate |
| T14 | `takeAwayStalemate.WinsIn .black 1 (.black, 1)` | `by decide` *(checked)* | the variant still has mates |
| T15 | `takeAway.firstFailureWin .white 2 (.white, 4) (T6's certificate) = none` | `by decide` *(checked)* | the diagnostic finds nothing wrong with an accepted certificate |
| T16 | `takeAway.firstFailureWin .white 1 (.white, 4) (T6's certificate) = some ([1, 1], .noBudget)` | `by decide` *(checked)* | T7's rejection: after 1 and Black's 1, White has no budget left |
| T17 | `takeAway.firstFailureWin .white 2 (.white, 4) (.move 1 (.replies [(1, .move 2 .goal)])) = some ([1], .missingReply 2)` | `by decide` *(checked)* | T8's rejection: Black's move 2 has no pair |
| T18 | five one-node certificates: `.goal` at `(.white, 4)` gives `notInTarget`; `.move 1 .goal` at `(.black, 4)` gives `notAttackerTurn`; `.move 3 .goal` gives `unavailable 3`; `.replies []` at `(.white, 4)` gives `notDefenderTurn`; in `takeAwayStalemate`, `.replies []` at `(.black, 0)` gives `noDefenderMove` (all with path `[]`) | `by decide` *(checked)* | the other rejections of `checkForces` |
| T19 | `firstFailureOnlyMove` on T9's certificate `= none`; on T10's `= some ([], .unrefuted 2)`; with `refs := [(2, .goal)]` `= some ([2], .notInTarget)` | `by decide` *(checked)* | the diagnostic of the only-move checker, including a path inside a refutation |

Reading of T1/T9: from a pile of 4 with White to move, White takes 1, leaving 3; whatever Black
takes, White takes the rest and Black faces an empty pile. Taking 2 instead leaves 2, and Black
takes both and wins: that is the refutation in T9.

| T20 | `takeAway.WinsIn .white 2 (.white, 4)`, T1's claim | node by node with L4.8–L4.10, L4.12, L4.17 and L4.18 only, each checkpoint by `decide` or `rfl` *(checked)* | the glue of §4.1 proves a win without a constructor of `Forces` or a lemma of core (§4.3) |

Every constructor of `Cert.Rejection` is produced by some test of T16–T19. A test of the
diagnostic on chess (a rejected mate in one) is in `ChessTest/ChessGame.lean`
(`docs/spec/ChessGame.md` §6).

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
12. **Certificates carry no budgets of the claim and no states.** The budget belongs to the claim; states are
    recomputed by `play`. `Cert` is generic in the move type (`Chess.Cert`, not `Game.Cert`), so a
    certificate for one game can be transported along a game morphism by mapping its moves (G7).
13. **No `isLegal` field in `Game` (Stage 1).** DESIGN §6.1 left it optional. The per-node lemmas
    (L4.9) take the membership `m ∈ G.moves x` as a hypothesis, so a chess proof can supply it from
    `Legal` through `mem_legalMoves` at the cost of one legality decision. The field would help only
    the monolithic checker, whose cost is not the bottleneck; adding it later changes one
    construction (`Game.chess`) and the `move` conjunct of `checkForces`.
14. **`checkOnlyMove` takes the certificate *after* the best move** (`oc.next` since Round 5) and checks
    `.move best next` at `x`. **Deviation from DESIGN §7.2**, which takes a certificate "whose root is
    `move best _`": building the root instead of inspecting it needs no root extractor and no
    conjunct saying "the root is `best`", and the budget is still counted at `x`.
15. **One refutation budget for all alternatives** (resolves DESIGN §10's open question; since
    Round 5 the field `refBudget` of `OnlyMoveCert`, earlier the argument `k`). By
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

22. **The module is six files, split at the trust boundary** (Round 5, Game review C2). DESIGN §11
    asked for a split past about 600 lines; the file had 748. The reason that matters is the reader:
    the trusted definitions are now a file of their own (`Defs`, 130 lines with its module
    docstring), and an auditor stops at its end. `Search` and `Cert` are siblings above `Laws`, so
    neither builds the other. The umbrella `Chess/Game.lean` keeps every downstream
    `import Chess.Game` working. The toy games stay in the library (`Examples`), as in Rounds 1–4,
    because they cost well under a second and document the definitions; the larger tests of the
    other modules are in `ChessTest`. One spec covers the six files, since a declaration's spec
    entry did not change when it moved.
23. **The only-move checker takes a certificate structure** (Round 5, Game review C3.3). The
    arguments of `checkOnlyMove` are the claim, and the `OnlyMoveCert` is the evidence (D4.4). Three
    gains: a generated call names every part (`refBudget := 10` cannot be confused with the
    claim's `11`); the refutation budget moves into the evidence, where choice 12 puts everything
    that is not part of the claim; and the type can grow a field (trap refutations, open item 1)
    with a default value, without breaking files already generated. The cost was one breaking
    change while no generated file existed.
24. **One refutation budget, kept** (owner decision of ROADMAP §5, taken in Round 5). One budget
    per alternative would make `refs` a list of triples and buy nothing that monotonicity does not
    give (choice 15): the generator can always use the largest refutation length. With the
    structure of choice 23, a per-alternative budget can still be added later as a field.
25. **Diagnostics, proved to agree with the checkers** (Round 5, Game review C3.4). The review
    asked for an untrusted function with no proof. The agreement theorems (L4.13, L4.14, L4.16,
    with L4.15) cost about 80 lines, and they say that a diagnostic returns `none` exactly when
    its checker accepts, and `some` exactly when it rejects. That the reported path and reason
    are the right ones is tested (T16–T19, `ChessTest/ChessGame.lean`), not proved.
    They do not make the diagnostics trusted: no theorem about a game uses them. They live beside
    the checkers so that a change to a checker shows up as a broken agreement proof.
26. **A frozen generated-file interface, checked by a test** (Round 5, Game review C3.1). §4.3
    lists the names a generated file may use; `ChessTest/Interface.lean` records their
    signatures with `#guard_msgs`, as `ChessTest/Axioms.lean` records axioms. The glue gained
    L4.12 (mate leaf) in Round 5 and L4.17–L4.18 (walking a defender's move list) in Round 6, so
    that no generated proof needs a constructor of `Forces` or a lemma of core.

---

## 7. Not in this module, and open items

Not here:

- `Game.chess`, `Chess.WinsIn`, `Chess.MateIn`, `Chess.Wins`, `Chess.OnlyWinningMove`, the FEN and
  UCI parsers: `Chess.ChessGame`. Named headline positions (`Puzzles.gotham`): `Chess.Puzzles`.
- The record of the generated-file interface (§4.3): `ChessTest/Interface.lean`.
- `Holds`, `Trap`, `holds_iff_not_forces`, the game value, `Optimal` (G9, G10, O0–O7): Stage 3.
  Nothing here needs to change for them: the `replies` guard is what the trap duality requires.
- Survival and trap certificates (C4, C5), and the `Refutation` sum type of THEOREMS C7: Stage 3.
- `Game.Hom` and `winsIn_iff` along a morphism (G7): Stage 2/3, stated by membership (choice 16).
- Ranked-set certificates (C6): Stage 5.

Open, for the critic and the owner:

1. **Stage 3 refutations.** When trap refutations arrive, does `checkOnlyMove` change its `refs`
   type to `List (G.Move × Refutation G)` (a breaking change to every generated only-move file), or
   does a second checker `checkOnlyMoveWithTraps` sit beside it? The draft prefers the second.
   Since Round 5 there is a third way: a new field of `OnlyMoveCert` (say `traps`, defaulting to
   `[]`) and one more conjunct in `checkOnlyMove`, which leaves files generated before it valid
   (choice 23).
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

Status after Round 6 (all done; `lake build` succeeds with no warnings).

- [x] `Chess/Game/Defs.lean` imports `Chess.Basic` only; `Laws` imports `Defs`; `Search` and
      `Cert` import `Laws`; `Examples` imports `Search` and `Cert`; `Chess/Game.lean` imports the
      five.
- [x] Declarations in the files and order of "Files and their contents"; in `Cert.lean`, `Cert`
      and `OnlyMoveCert` before the first `namespace Game`, `Cert.Rejection` between the two.
- [x] Every docstring above, word for word, on its declaration, its fields and its constructors
      (lemma tags moved to a trailing "THEOREMS …" sentence, §0), and the six module docstrings
      word for word.
- [x] Never a bare `Move` or `State` inside `namespace Game`.
- [x] `[DecidablePred T]` only in `section Search`, `section Certificates` and
      `section Diagnostics`.
- [x] No `sorry`; `#print axioms` for `checkWin_sound`, `checkOnlyMove_sound`, `searchForces_iff`
      shows at most `propext`, `Classical.choice`, `Quot.sound` (the output is recorded in
      `docs/process/Game.md`, Rounds 3 and 4, and checked by `ChessTest/Axioms.lean`, which since
      Round 5 also lists L4.12, L4.13 and L4.16, and since Round 6 L4.17 and L4.18).
- [x] The tests T1–T20 elaborate, and T6 also by `rfl`.
- [x] The names of §4.3 are recorded in `ChessTest/Interface.lean`.
- [x] Record in `docs/process/Game.md` every place where the English had to change for the Lean to
      go through, and every [cheap] lemma that turned out not to be (none did).
