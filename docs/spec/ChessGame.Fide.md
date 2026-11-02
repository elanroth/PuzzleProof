# Specification of `Chess.ChessGame.Fide`

Role: English specification writer and translator (one overnight round, G8).
Date: 2026-11-02.
Status: Round 1, matched to the Lean of `Chess/ChessGame/Fide.lean` (see
`docs/process/ChessGame.Fide.md`). Every lemma below is proved in the library, with no `sorry`.

File: `Chess/ChessGame/Fide.lean`. Depends on: `Chess.ChessGame` (and through it `Chess.MoveGen`,
`Chess.Game`) and `Chess.Spec.Winning`; core only. Carries out `docs/spec/ChessGame.md` §7
(L7.1–L7.6, planned there in Round 1) and THEOREMS **G8** ★★, the Stage 2 headline together with M4.

What a reader must trust from this module: **nothing.** It contains only theorems. Its effect on
trust is the point of it: a headline stated with `Chess.WinsIn`, `Chess.Wins`, `Chess.MateIn` or
`Chess.OnlyWinningMove` may be read with `SpecWinsIn`, `SpecWins`, `SpecMateIn` or
`SpecOnlyWinningMove` of `Chess.Spec.Winning` instead, so the move generator and `Chess.Game` are no
longer part of what a reader must check.

## 0. How to read this document

The conventions of `docs/spec/ChessGame.md` §0 apply unchanged (IDs, docstrings word for word,
tags, `autoImplicit = false`, `namespace Chess`, `Chess.Move` qualified only inside declarations
whose names start with `Game.`; none here do).

Letters: `a` the attacker (a colour); `T` a target; `n` a budget; `p` a position; `m` a move;
`x` a state of `Game.chess` (a position, typed as `Game.chess.State`).

## Contents of the file, in order

1. The chess game is FIDE chess (`section Fide`): `mem_chess_moves`, `chess_mated_iff_checkmate`,
   `forces_iff_specForces`, `winsIn_iff_specWinsIn`, `wins_iff_specWins`, `mateIn_iff_specMateIn`,
   `onlyWinningMove_iff_specOnlyWinningMove`.
2. Tests.

---

## 1. Section "The chess game is FIDE chess" (`section Fide`)

`section Fide`, opening with `variable {a : Color} {n : Nat} {p : Position} {m : Move}`.

| ID | English | Lean | Tag |
|---|---|---|---|
| L1.1 | The moves available in chess are exactly the legal moves. | `theorem mem_chess_moves : m ∈ Game.chess.moves p ↔ Legal p m := mem_legalMoves` | [core] (ChessGame L7.1) |
| L1.2 | In chess, being mated is FIDE checkmate. | `theorem chess_mated_iff_checkmate : Game.chess.Mated p ↔ Checkmate p := checkmate_iff.symm` | [core] (ChessGame L7.2) |
| L1.3 | Forcing in the chess game is forcing in FIDE chess, for every target. | `theorem forces_iff_specForces {T : Position → Prop} : Game.chess.Forces a T n p ↔ SpecForces a T n p` | [core] (ChessGame L7.3) |
| L1.4 | `WinsIn` is `SpecWinsIn`: a win in the chess game is a forced checkmate under the FIDE rules. (THEOREMS G8.) | `theorem winsIn_iff_specWinsIn : WinsIn a n p ↔ SpecWinsIn a n p` | [core] (ChessGame L7.4) |
| L1.5 | `Wins` is `SpecWins`. | `theorem wins_iff_specWins : Wins a p ↔ SpecWins a p` | [core] (ChessGame L7.5) |
| L1.6 | `MateIn` is `SpecMateIn`: mate in exactly `n` in the chess game is mate in exactly `n` under the FIDE rules. | `theorem mateIn_iff_specMateIn : MateIn a n p ↔ SpecMateIn a n p` | [core] (ChessGame L7.5) |
| L1.7 | `OnlyWinningMove` is `SpecOnlyWinningMove`. | `theorem onlyWinningMove_iff_specOnlyWinningMove : OnlyWinningMove p m ↔ SpecOnlyWinningMove p m` | [core] (ChessGame L7.6) |

Proofs.
- L1.1 and L1.2 are M4 and M6 of `Chess.MoveGen` (`mem_legalMoves`, `checkmate_iff`), read in the
  game's vocabulary. They are the only facts about the generator that this file uses.
- L1.3 is an induction in each direction, one rule to the same rule, with L1.1 at each step. In the
  `replies` rule, "the list of moves is not empty" and "some move is legal" are exchanged by
  `List.exists_mem_of_ne_nil` and `List.ne_nil_of_mem`.
- L1.4 rewrites the target: `Game.chess.DefenderMated a` equals `fun q => q.turn = a.other ∧
  Checkmate q` by `funext`, `propext` and L1.2. Then it is L1.3. (The Round 1 plan proposed
  `Forces.trans` with `k := 0` as the congruence; rewriting the target as a function is shorter.)
- L1.5–L1.7 are congruences (`exists_congr`, `and_congr`, `forall_congr'`, `imp_congr`,
  `not_congr`) over L1.1 and L1.4, following the shape of the definitions. No unfolding is needed
  beyond what `exact` does by definitional unfolding.
- `#print axioms` on each of L1.1–L1.7: `propext`, `Classical.choice`, `Quot.sound` (the
  `Classical.choice` comes from `mem_legalMoves`).

Notes.
- **A Lean detail in L1.3.** `induction` on `w : Game.chess.Forces a T n p` fails with "Internal
  error in mkElimApp: Expected first 3 arguments of motive in conclusion to be one of the targets"
  when `p` has the type `Position`, although `Game.chess.State` unfolds to `Position`. Restating `p`
  as a variable of type `Game.chess.State` first
  (`obtain ⟨x, rfl⟩ : ∃ x : Game.chess.State, x = p := ⟨p, rfl⟩`) fixes it. The other direction, by
  induction on `SpecForces`, needs nothing. The statement keeps `p : Position`, so that readers
  never see `Game.chess.State`.
- The names say which side of each `↔` is which (ChessGame spec §9): the chess-game notion first,
  the `Spec` notion second.
- None of these is `@[simp]`: they are used to move a finished claim from one reading to the other,
  by `.1` or `.2`.

---

## 2. Section "Tests"

**Where they live (2026-11-02).** These tests are in `ChessTest/ChessGame/Fide.lean`, in the test
library `ChessTest` (`lake build ChessTest`; not built by `lake build`); they were about 2.3 s of
this module's 2.4 s build. The module's section "Tests" now only points there. What follows
specifies that file.

```lean
-- A certificate checked through `Chess.Game` proves a mate in one under the FIDE rules.
example : SpecWinsIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") :=
  winsIn_iff_specWinsIn.1 <|
    Game.checkWin_sound (c := .move (uci "a1a8") .goal) (by decide +kernel)
-- Stalemate, decided through the generator (`Stalemate.decidableByGen`), is a win for nobody.
example : ¬ SpecWins .white (fen "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1") :=
  not_specWins_of_stalemate (by decide +kernel)
```

Notes.
- The first test is the headline pipeline in miniature: an untrusted certificate (`a1a8`, then
  mate), the checker's soundness theorem, then L1.4, ending in a statement that mentions only
  `Chess.Spec.Winning` and the notation.
- The second uses the sanity lemma of `Chess.Spec.Winning` (L2.2 there) with `Stalemate` decided
  through the generator; in this file the generator-backed instance of `Chess.MoveGen` is in scope,
  so `decide +kernel` does not enumerate every move.
- With these tests the module elaborated in about 2.4 s (`lake build`, this machine); the test file
  now takes about 2.6 s and the module 0.14 s. A third test,
  `SpecMateIn .white 1` of the same position via L1.6 and `decide +kernel`, was checked in scratch
  (about 3 s more) and left out to keep the build short; the same claim is tested as `MateIn` in
  `Chess.ChessGame`.

---

## 3. Design choices, with reasons

1. **Its own file, not the end of `Chess/ChessGame.lean`** (ChessGame review C2; ChessGame spec
   open item 2, decided). The reason that still holds: the definitions these theorems target
   (`Chess.Spec.Winning`) import only `Chess.Rules`, so the trusted reading after Stage 2 has no
   generator and no abstract game in it. The other reason C2 gave, that certificate files should
   not depend on these proofs, no longer holds (corrected 2026-11-02, finding game-2). Since ROADMAP
   step 6, a generated chess certificate shows each attacker move available with
   `mem_chess_moves.2 (by decide +kernel)` (L1.1; Game spec §4.3 lists it, and §4.1 explains why
   not `mem_legalMoves`), so `scripts/gen_cert.py` makes every file it writes import this module,
   and `ChessDemo/GothamCert.lean` does. Such a file therefore rebuilds when this file changes and
   depends on `Chess.Spec.Winning` and on the proofs here, of which it uses only L1.1. This adds no
   axiom and nothing to trust: L1.1 is `mem_legalMoves`, which the file could reach through
   `Chess.ChessGame` alone. A file that only checks a certificate of the abstract `Game` layer, or
   a puzzle file such as `Chess.Puzzles`, still does not import this module. Moving L1.1 into
   `Chess.ChessGame` would restore the separation; it touches the generator, the generated file
   and many documents, and is not done.
2. **Equivalences, not one-way implications.** A one-way bridge (`WinsIn → SpecWinsIn`) suffices to
   read a proved headline, but `OnlyWinningMove` contains a negation (`¬ Wins` after the other
   moves), and its bridge needs both directions of L1.5. Proving `↔` throughout costs nothing extra.
3. **No new decision procedure.** Claims are proved in the chess game (search, certificates), then
   moved by `.1`.
