# Process log: `Chess.ChessGame.Fide`

The record of the back-and-forth between the English specification
(`docs/spec/ChessGame.Fide.md`) and the Lean (`Chess/ChessGame/Fide.lean`). Each round says what
changed, in which direction, and why.

---

## Round 1: English and Lean (G8, Stage 2)

Date: 2026-11-02. Author role: overnight implementer (ROADMAP step 2), writing spec and Lean in one
round. Inputs: `docs/spec/ChessGame.md` §7 (L7.1–L7.6 of the Round 1 plan and its proof hints),
`docs/reviews/ChessGame.md` C2, `Chess/MoveGen.lean` section `Completeness` (`mem_legalMoves`,
`checkmate_iff`), `Chess/Game.lean` (sections "Games" and "Laws").

**English first.** The six planned lemmas, with their planned names except two: L7.5's `MateIn`
half is `mateIn_iff_specMateIn` (against the new `SpecMateIn`), and L7.6 is
`onlyWinningMove_iff_specOnlyWinningMove`, so that every bridge is named `x_iff_specX`. Docstrings
are the plan's English columns; L1.4 and L1.6 gained a clause saying what the equivalence means for
a chess reader.

**Lean → English.**
- **`induction` and the state's type.** `induction w` with `w : Game.chess.Forces a T n p` and
  `p : Position` fails: "Internal error in mkElimApp: Expected first 3 arguments of motive in
  conclusion to be one of the targets". With the state declared as `x : Game.chess.State` it works.
  Tried: `generalize (p : Game.chess.State) = x` (the new variable still has type `Position`, same
  error); `Game.Forces.rec (motive := …)` applied by hand (works, but reads worse); `obtain ⟨x, rfl⟩
  : ∃ x : Game.chess.State, x = p := ⟨p, rfl⟩` (works, one line). The last is used, with a comment.
  The statement keeps `p : Position`. The spec's notes on L1.3 record this.
- **The target congruence for L1.4.** The plan proposed `Forces.trans` with `k := 0`. Rewriting the
  target as a function is shorter: `Game.chess.DefenderMated a = fun q => q.turn = a.other ∧
  Checkmate q` by `funext`, `propext`, `and_congr_right` and L1.2, then `rw` and L1.3. The spec's
  proof notes say so.
- L1.5–L1.7 are term-mode congruences (`exists_congr`, `and_congr`, `forall_congr'`, `imp_congr`,
  `imp_congr_right`, `not_congr`), following the shape of the definitions; `exact` unfolds
  `Game.Wins`, `Game.MateIn`, `Game.OnlyWinningMove` and the `Spec` definitions by itself.
- `#print axioms` on all seven: `propext`, `Classical.choice`, `Quot.sound`.

**Tests.** Two: a mate in one proved by a certificate and carried to `SpecWinsIn` by L1.4, and a
stalemate shown to be no `SpecWins` by the sanity lemma of `Chess.Spec.Winning`, decided through the
generator. A third (`SpecMateIn` by `decide +kernel` and L1.6) was checked in scratch (about 3 s)
and left out to keep the build short. The module builds in about 2.4 s.

**Checked.** All 7 Lean docstrings occur word for word in the spec. No line over 100 characters.
`lake build` green (11 jobs).

**Library-wide docstring check (same round).** The same whitespace-normalised script was run on all
eight modules. Every docstring of `Position`, `MoveGen`, `ChessGame`, `Spec.Winning` and
`ChessGame.Fide` occurs word for word in its spec, after one repair: `candidates` in
`Chess/MoveGen.lean` had a leftover fragment of its pre-M4 wording (logged in
`docs/process/MoveGen.md`). The remaining misses, not changed here, are all lemma or test-position
docstrings, not definitions: 78 in `Basic` (spec tables merge lemma pairs and put the THEOREMS tag
first, e.g. "(R2) Every colour is listed, once." for `Color.mem_all` and `Color.all_nodup`), 20 in
`Game` (tag placement, e.g. "(G3) More budget never hurts." against "More budget never hurts.
THEOREMS G3."), and 12 in `Rules` (docstrings of test positions, which the spec describes rather
than quotes). Whether the convention should cover lemma docstrings word for word is for the owner.


---

## Note, 2026-11-02 (test library round, ROADMAP step 3): the tests moved to `ChessTest/ChessGame/Fide.lean`

The two tests of section "Tests" moved verbatim to `ChessTest/ChessGame/Fide.lean`; the module's
section now only points there. Spec §2 says so. Clean build of the module: 2.4 s before, 0.14 s
after. The theorems of this module are in the axioms ledger (`ChessTest/Axioms.lean`), each with
`propext`, `Classical.choice` and `Quot.sound`.

---

## Note, 2026-11-02 (finding game-2, low): the C2 rationale corrected

Two reviewers found that the module docstring's implementation note said this file is kept apart
from `Chess.ChessGame` "so that files that only check certificates do not depend on it", while the
one generated certificate file, `ChessDemo/GothamCert.lean`, imports it and uses `mem_chess_moves`
160 times. Since ROADMAP step 6 (Game spec §4.1 Round 7 note, §4.3), `scripts/gen_cert.py` emits
`mem_chess_moves.2 (by decide +kernel)` at every attacker node and puts `import
Chess.ChessGame.Fide` first in every file it writes, so the note had gone stale. Soundness was never
affected: `mem_chess_moves` is `mem_legalMoves`.

**English first.** Spec §3 choice 1 now keeps the reason that still holds (`Chess.Spec.Winning`
imports only `Chess.Rules`), says the certificate reason no longer holds and why, says what the
dependency costs (rebuilds when this file changes; no axiom, nothing to trust), and names the
alternative not taken. **Then the Lean.** The implementation note was rewritten to match. No
declaration and no declaration docstring changed.

**Alternative not taken.** Moving `mem_chess_moves` into `Chess.ChessGame` would make the old
reason true again (the lemma's full name, `Chess.mem_chess_moves`, would not change). It was not
done for a low finding: it changes `scripts/gen_cert.py`, the generated `ChessDemo/GothamCert.lean`
(whose check takes about 160 s) and about twenty documents that place the lemma in this module. It
remains possible later.

**Checked.** `lake build` green.
