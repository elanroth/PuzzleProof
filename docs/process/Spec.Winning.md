# Process log: `Chess.Spec.Winning`

The record of the back-and-forth between the English specification (`docs/spec/Spec.Winning.md`)
and the Lean (`Chess/Spec/Winning.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English and Lean (G8, Stage 2)

Date: 2026-11-02. Author role: overnight implementer (ROADMAP step 2), writing spec and Lean in one
round. Inputs: `docs/ROADMAP.md` §5 step 2, `docs/spec/ChessGame.md` §7 (the Round 1 plan of
D7.1–D7.4), `docs/reviews/ChessGame.md` C2, `Chess/Game.lean` (section "Games", whose three rules
are copied), `Chess/Rules.lean` (`Legal`, `Position.play`, `Checkmate`, `Stalemate`).

**English first.** The definitions of the plan were kept: `SpecForces` (three rules, with the
defender's `∃ m, Legal p m` guard), `SpecWinsIn`, `SpecWins`, `SpecOnlyWinningMove`. Added:
`SpecMateIn` (not in the plan), so that the `MateIn` bridge reads like the other three; constructor
docstrings for `SpecForces`, as `Game.Forces` has them; and two [sanity] lemmas, THEOREMS G2 in
FIDE terms (`specWinsIn_zero_iff`, `not_specWins_of_stalemate`), proved from the definitions
without the generator, so that the definitions are checked on their own.

The docstrings were rewritten from the plan's one-liners to say what the `Game` docstrings say
(budget counts the attacker's moves only, the mating move included; the defender escapes with no
legal move; no move-count, repetition or dead-position rule; 'other' means a different move value).
`SpecWinsIn`'s docstring names FIDE 5.1.1; `not_specWins_of_stalemate`'s names FIDE 5.2.1.

**Lean → English.**
- `refine ⟨fun w => ?_, .goal⟩` did not elaborate for the backward direction of
  `specWinsIn_zero_iff`: Lean reported an application type mismatch for `SpecForces.goal` used
  unapplied as a function. The eta-expanded `fun h => .goal h` works. No English change.
- The inner `cases` of `specWinsIn_zero_iff` is on a `SpecForces` whose position is `p.play m`, not
  a variable; `generalize p.play m = q at hc w` first. A comment in the proof gives the argument in
  one sentence. No English change.
- `#print axioms`: `propext`, `Quot.sound` for both lemmas.

**Checked.** All 10 Lean docstrings (5 definitions, 3 constructors, 2 lemmas) occur word for word
in the spec. The module imports `Chess.Rules` only and elaborates in about 0.2 s.

---

## Note, 2026-11-02 (readability round): checkmate's FIDE article

Spec §0's word list said `Checkmate` is "in check and no legal move (FIDE 5.1.1)". FIDE 5.1.1 only
says that a checkmate wins; Articles 1.4 and 1.4.1 define it. The line now cites 1.4 and 1.4.1 and
says 5.1.1 makes it a win, as Rules' `Checkmate` docstring now does. The docstring of `SpecWinsIn`
("force checkmate (FIDE 5.1.1) of the other side") is about winning and is unchanged. No Lean
change.
