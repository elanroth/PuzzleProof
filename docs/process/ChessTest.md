# Process log: the test library `ChessTest` and the program `chess-perft`

The record of the round that created the test library (ROADMAP step 3): what moved, what is new,
what was measured, and what the differential test against python-chess found. Specifications:
`docs/spec/ChessTest.Perft.md`, `docs/spec/ChessTest.Axioms.md`, `docs/spec/ChessPerft.md`; the
moved tests keep their specifications in `docs/spec/Rules.md` §10, `MoveGen.md` §6,
`ChessGame.md` §6 and `ChessGame.Fide.md` §2.

---

## Round 1 (2026-11-02, overnight implementer)

Inputs: ROADMAP §5 step 3, MoveGen review C4 and C7, ChessGame review C3, DESIGN §7.3 and §8.4,
THEOREMS M7, the prototype's perft notes.

### 1. The library and the move

`lakefile.toml` gained a second `lean_lib`, `ChessTest` (not in `defaultTargets`), and a
`lean_exe`, `chess-perft` (root `ChessPerft`). `lake build` builds `Chess` alone, as before.

The sections "Tests" of four modules moved verbatim, each to a file of the same name under
`ChessTest/` with a module docstring in the library's format: `Rules` (with its thirteen named
positions), `MoveGen` (with `epCheckPos` and `promoKnightPos`), `ChessGame`, `ChessGame/Fide`.
Each module keeps a pointer and, except `ChessGame/Fide`, a few cheap `#guard`s as documentation
(quoted in each spec). `Basic`, `Position` and `Game` keep their tests: measured with
`lake env lean`, their test sections cost 1.7 s, 0.14 s and 0.05 s, and Basic's spec asks for its
whole-board `decide` check "on every build". The specs of the four modules now say where their
tests live; Rules §10 now also quotes the thirteen position docstrings word for word (the G8
round had recorded them as described, not quoted).

**Build time, clean, same machine** (`rm -rf .lake/build; lake build`):

| Module | before | after |
|---|---|---|
| `Chess.Basic` | 3.2 s | 3.4 s |
| `Chess.Position` | 1.1 s | 1.2 s |
| `Chess.Rules` | 3.6 s | 0.4 s |
| `Chess.Game` | 0.5 s | 0.5 s |
| `Chess.MoveGen` | 13 s | 1.0 s |
| `Chess.ChessGame` | 11 s | 1.5 s |
| `Chess.Spec.Winning` | 0.16 s | 0.16 s |
| `Chess.ChessGame.Fide` | 2.4 s | 0.14 s |
| **whole build, wall clock** | **36.3 s** | **8.1 s** |

The moved tests themselves (`lake build ChessTest` before the perft suite existed): 28.6 s wall
clock, `ChessTest.MoveGen` 14 s, `ChessTest.ChessGame` 10 s, `ChessTest.Rules` 3.4 s,
`ChessTest.ChessGame.Fide` 2.6 s; peak 1.1 GB.

### 2. Compiled perft, and a slow board

MoveGen review C7 asked to time compiled perft before fixing depths. (Every compiled time in this
section and in §5 is as re-timed in Round 2, with one search per run; Round 1's program ran the
search twice and reported twice these times.) First measurement, the program reading the initial
position from its FEN: perft 3 in 10.9 s, perft 4 in 234 s. The
profile (`sample`) showed the time in `splitOn`, `readBoard`, `Piece.ofLetter?` and `emptyCount?`:
**the board read from the FEN re-read the FEN text at every square read.** The same perft from
`Position.initial` (a board defined square by square) took 0.39 s at depth 3.

A first fix, a `Board`-valued `Board.tabulate b := let a := …; fun s => a[s.index.val]!`, was
worse: perft 3 did not finish in 10 minutes, because the compiled definition took the square as a
second argument and rebuilt the array at every read (the trap of Position review C1, from the
reading side). The fix that works returns a structure: `Position.tabulate` builds the array once
and returns the position with a board that reads it. `Position.tabulate_eq : p.tabulate = p` is
proved (eight lines, standard axioms), so a check on `p.tabulate` is a check on `p`.

Compiled, tabulated (this machine): perft 3 of the initial position 0.38 s, perft 4 9.0 s.
Interpreted (`#guard`), tabulated: initial perft 3 8.5 s (8.0 s in Round 2), Kiwipete perft 2
1.6 s (37 s untabulated) and perft 3 92 s (compiled 4.2 s), Position 3 perft 3 2.0 s and perft 4
36 s. So the interpreter is about 20 times slower than compiled code here.

`readBoard` itself was not changed: it is untrusted reader code with proofs about it
(`readBoard_fenChars`), outside this round's scope. ROADMAP §4 records the issue and the options.

### 3. Kernel perft: what is affordable

Measured in scratch files (`decide +kernel`, `lake env lean`, `/usr/bin/time -l`):

| Check | CPU | peak memory |
|---|---|---|
| perft 1 of all six positions, one file | 21 s | 2.5 GB |
| perft 1 of Kiwipete via `fen` / via a `Board.unpack` literal | 4.7 s / 3.9 s | 1.8 / 1.6 GB |
| perft 2, initial position | 42 s (276 s wall clock, swapping) | 3.9 GB |
| perft 2, Position 3 | 13 s | 4.0 GB |
| perft 2, Position 4 | 26 s | 6.6 GB |
| perft 2, Position 5 | stopped after about 10 minutes, the process swapped out | — |

The machine was under memory pressure from other processes throughout (swap use 13 to 18 GB of
19 GB), so wall-clock times there are unreliable; CPU times are the better guide. Decision: kernel
depth 2 for the initial position and Position 3 only; `#guard`s for the rest
(`docs/spec/ChessTest.Perft.md` §3). The memory guard of the task (stop past about 9 GB) could not
see the Position 5 process, whose resident size fell as it was swapped out; it was stopped by hand.

`lake build ChessTest.Perft`: 214 s wall clock, 91 s CPU, 4.9 GB peak.
`lake build ChessTest.PerftDeep`: 263 s, single-threaded, 0.4 GB.

**The whole test library, clean** (after a clean `lake build`): 543 s wall clock, 396 s CPU;
`ChessTest.Perft` 276 s and `ChessTest.PerftDeep` 265 s (in parallel), `ChessTest.MoveGen` 15 s,
`ChessTest.ChessGame` 13 s, the rest under 5 s each; largest process 4.8 GB, sampled total of all
Lean processes at most 4.3 GB.

### 4. The axioms ledger

`ChessTest/Axioms.lean`: 125 entries, each `#guard_msgs in #print axioms X` under the expected
line. (Round 2: 126 entries, `slides_symm` added, and the eight perft entries moved to
`ChessTest/AxiomsPerft.lean`; 49 with the three axioms.) All 125 are [kernel] (48 with `propext`,
`Classical.choice`, `Quot.sound`; 44 with
`propext`, `Quot.sound`; 17 with `propext`; 16 with none). Checked that a wrong expected line fails
the build, for a one-line entry and for a wrapped (`whitespace := lax`) one. Builds in about 2 s.

### 5. The differential test against python-chess

Scripts: `scripts/perft_jobs.py` (job files: the six positions and Position 4 mirrored at given
depths; seeded random positions) and `scripts/perft_diff.py` (runs `chess-perft` and python-chess
1.11.2 on each job and compares the set of moves at the root, each move's count in the divide, the
total (Round 1 also checked that the divide adds up to the total; see Round 2), and, for inputs
written with every en passant target,
the four position fields of the FEN that `chess-perft` writes back). Run from
`~/chess-lean-research/.venv` with `python -I`. Results (this machine, 2026-11-02):

| Jobs | Positions | Depth | Leaves | Agree | Notes |
|---|---|---|---|---|---|
| `std 3`: the six positions and Position 4 mirrored | 7 | 1, 2, 3 | 287 686 | 21/21 | |
| `stdat 4`: the same | 7 | 4 | 11 168 869 | 7/7 | each equal to the published count; `chess-perft` 523 s in all (Kiwipete 190 s), python-chess 6.4 s |
| `stdat 5 initial position3` | 2 | 5 | 5 540 233 | 2/2 | 4 865 609 and 674 624, the published counts; 248 s and 27 s |
| `rand 200 2 20261102`: random play, 1 to 120 plies | 200 | 2 | 178 032 | 200/200 | the task's 200; half written with every en passant target; 10 with a target (3 capturable), 12 in check, 3 finished games |
| `rand 100 3 99` | 100 | 3 | 3 096 710 | 100/100 | |
| `ep 100 3 7`: just after a double push | 100 | 3 | 2 137 888 | 100/100 | all with a target, 42 with an en passant capture at the root |
| `special 100 3 11`: castling or promotion available | 100 | 3 | 3 795 093 | 100/100 | 78 with castling, 22 with a promotion at the root |
| `named 3`: the 16 named test positions of `ChessTest/Rules` and `MoveGen` (FEN by `toFEN`) | 16 | 3 | 32 046 | 16/16 | the bug-class positions of DESIGN §8.4 among them |

In all, 546 jobs and about 26.2 million leaf positions: no disagreement in the move sets, the
divides or the totals, and in every job the four FEN fields that `chess-perft` wrote back equal
python-chess's `board.fen(en_passant="fen")` of the input. So the reader and writer agree with
python-chess under this library's en passant convention; FENs written by python-chess's default
(`en_passant="legal"`) parsed and gave the same counts. Python-chess is about 80 times faster
than the compiled generator (Kiwipete depth 3: 0.05 s against 4.2 s; depth 4: 2.5 s against 190 s).

What this shows and what it does not: on these positions and depths, the root move sets, every
divide count and every total agree with python-chess; deeper plies are compared only through
counts, so `Position.play` is checked indirectly (and directly only through the root FEN written
back). By M4 the root move sets are the sets of `Legal` moves. The six positions reproduce the
published counts to depth 4 (two to depth 5). It is a test, not a proof; it covers
no position outside the jobs, and python-chess is itself untrusted.

To reproduce (from the repository root, with python-chess installed):

```
lake build chess-perft
python scripts/perft_jobs.py std 3 std3.tsv
python scripts/perft_jobs.py stdat 4 std4.tsv
python scripts/perft_jobs.py stdat 5 deep5.tsv initial position3
python scripts/perft_jobs.py rand 200 2 20261102 rand200.tsv
python scripts/perft_jobs.py rand 100 3 99 rand3_100.tsv
python scripts/perft_jobs.py ep 100 3 7 ep100.tsv
python scripts/perft_jobs.py special 100 3 11 special100.tsv
python scripts/perft_jobs.py named 3 bug16.tsv
for f in std3 std4 deep5 rand200 rand3_100 ep100 special100 bug16; do
  python scripts/perft_diff.py .lake/build/bin/chess-perft $f.tsv $f.jsonl
done
```

The job files are deterministic for a given seed (checked: regenerated files are byte-identical).
These are the commands of Round 2's rerun (§ Round 2); Round 1 made the depth-4, depth-5 and named
job files by hand, with the same contents.

### 6. Not done in this round

- No `_native` theorems: none was needed (DESIGN §7.3 allows them only in the test library).
- Kernel perft at depth 2 for Kiwipete and Positions 4, 5, 6: not affordable in memory on this
  machine (§3); they are checked by `#guard`.
- `readBoard` is not fixed (§2); `Position.tabulate` lives in `ChessTest`, not in `Chess.Position`.
- `legalMovesBySpec`, `agreesWithLegal` and L5.1–L5.3 stay in `Chess.MoveGen` (cheap; MoveGen
  spec open item 9 suggested moving them).
- `lake test` is not wired to the perft program; the differential test is run by hand.

---

## Round 2 (2026-11-02, review fixes)

Inputs: the review of Round 1 (one medium issue, seven low ones). All were taken except one
figure, as said below. Copies of every file before editing are in the round's scratch directory.

**`chess-perft` ran the search twice (medium).** `perftReport` computed the divide and then
`perft n p` again for the total. It now prints the sum of the divide as the total, which is
`perft n p` by `sum_perftDivide` (spec `ChessPerft.md` D1.2; the reviewer's code, unchanged). The
stated reason for the second search, "checks `sum_perftDivide` on each run", was empty: that is a
proved theorem. `scripts/perft_diff.py` dropped its "divide does not add up to the total" check,
which the new output makes true by construction; it still compares the total with python-chess's.

Every compiled time was re-measured, not halved:

| Run (compiled, this machine) | Round 1 | Round 2 |
|---|---|---|
| initial perft 3 / 4 / 5, tabulated | 0.72 s / 18.0 s / 490 s | 0.38 s / 8.9 s / 248 s |
| Kiwipete perft 3 / 4 | 8.4 s / 388 s | 4.2 s / 190 s |
| initial perft 3 / 4 from its FEN, untabulated | 20.4 s / 460 s | 10.9 s / 234 s |
| initial perft 3 / 4 from `Position.initial` | 0.75 s / — | 0.39 s / 9.4 s |
| the seven depth-4 jobs, in all | 1 057 s | 523 s |
| all 546 differential jobs, `chess-perft` time | about 2 390 s | about 1 190 s |

The untabulated and `Position.initial` rows were timed with a scratch executable (a `lake` project
in the scratch directory requiring this library by path) that prints `perft n p` once; the others
are the `lean_s` times recorded by `perft_diff.py`. Interpreted `#guard`s, re-timed: initial perft 3
8.0 s, Kiwipete perft 3 92 s. So the interpreter is about 20 times slower than compiled code (Round
1 said 12), and python-chess is about 80 times faster than `chess-perft` (Kiwipete depth 3: 0.05 s
against 4.2 s; depth 4: 2.5 s against 190 s; initial depth 5: 3.2 s against 248 s). **Disagreement
with the review on one figure:** it estimated python-chess at "about 50" times faster; the measured
ratio, on the same machine and the same jobs, is 75 to 95 (depth-4 and depth-5 jobs of the standard
positions). Corrected in `ChessPerft.md` D1.2 and choices 1 and 4, `ChessTest.Perft.md` §1, §2 and
§5 above, `ChessTest/PerftDeep.lean` and `ChessTest/Tabulate.lean` (implementation notes), ROADMAP
§4 and the MoveGen process note.

**The whole differential test was rerun with the new program.** All 546 jobs, about 26.2 million
leaves: every job agrees with python-chess 1.11.2 (move sets at the root, every divide count, every
total), every total equals Round 1's, and in all 546 jobs the four FEN fields written back equal
python-chess's `fen(en_passant="fen")`. The job files were regenerated by the commands now listed
in §5 and are byte-identical to Round 1's.

**Job files reproducible (low).** `scripts/perft_jobs.py` gained two kinds: `stdat DEPTH OUT
[LABEL…]` (the standard positions at one depth, optionally only some) and `named DEPTH OUT` (the 16
named test positions, as a list `NAMED` of the FENs that `Position.toFEN` writes for them,
regenerated by `#eval` in this round and equal to Round 1's). §5 lists every command.

**Ledger (two low items).** `ChessTest/Axioms.lean` now imports `Chess` and `ChessTest.Tabulate`
only, and builds without the perft suite (`lake build ChessTest.Axioms`: 12 jobs, 1.6 s for the
file). The eight perft entries moved to the new `ChessTest/AxiomsPerft.lean`, imported from
`ChessTest.lean`. `Chess.slides_symm` (a Main statement of `Rules`) was missing and is added. A
script checked every backquoted name in the "Main statements" of every `Chess` module against the
ledger: the only names without an entry are definitions and variables (`Legal`, `Reaches`, `p`, …).
Now 126 entries: 49 with the three axioms, 44 with `propext` and `Quot.sound`, 17 with `propext`,
16 with none. Checked again that a wrong expected line fails (`slides_symm` without
`Classical.choice`).

**Wording (low).** §5 no longer says "move for move" (only root moves are compared by move; deeper
plies by count). `ChessTest/Perft.lean` and its spec now say the counts are evidence about `Legal`
and `Position.play`.

**Stale text (low).** ROADMAP §0 size row (8 modules, about 5 000 lines, 383 theorems by a count of
`theorem` declarations, 194 `example`/`#guard` tests of which 131 in `ChessTest`, plus 126 ledger
entries) and step 2's note (thirteen test positions, fixed in step 3). MoveGen spec §6 (the 30 s
was before the move), Basic spec §11 and Position spec §7 (the tests stay; notes in their process
logs, including why Basic review C8's last bullet was not followed). DESIGN §8.4 and §8.7 rewrapped
at 100 columns.

**Checks.** `lake build`: green (11 jobs). `lake build chess-perft`: green. `lake build ChessTest`:
green, 547 s wall clock (it rebuilt `ChessTest.Perft`, 273 s, and `ChessTest.PerftDeep`, 272 s).
No `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `implemented_by` in `Chess/`,
`ChessTest/` or `ChessPerft.lean` except in comments. The docstring check (every docstring of the
touched Lean files word for word in its spec) passes.

---

## Round 3 (2026-11-02, ROADMAP step 5: the interface ledger)

Author role: overnight implementer of ROADMAP step 5 (`docs/process/Game.md` Round 5).

**New file `ChessTest/Interface.lean`** (spec `docs/spec/ChessTest.Interface.md`), imported from
`ChessTest.lean`. It records, with `#guard_msgs`, the `#check` output (binder names included) of
the 19 functions and theorems a generated certificate file may use and the `#print` output of the
three certificate types: 22 entries. The expected messages were produced by a script that ran each
command and wrapped lines over 100 characters at binder boundaries (those entries compare with
`whitespace := lax`). Checked on a scratch copy: changing the field `refBudget` in the expected
`#print Chess.OnlyMoveCert`, or the binder `c` in the expected `#check Chess.Game.checkWin`, gives
one error each.

**Axioms ledger.** Three entries added to `ChessTest/Axioms.lean` in the `Chess.Game` group:
`WinsIn.of_mated` (no axiom), `firstFailure_eq_none_iff` and `firstFailureOnlyMove_eq_none_iff`
(`propext`, `Classical.choice`, `Quot.sound`). Now 131 entries in all.

**Chess test of the diagnostics.** Three `#guard`s in `ChessTest/ChessGame.lean` run
`Game.chess.firstFailureWin` on the back-rank mate in one: the accepted certificate (`none`),
`a1a7` (legal, does not mate: `some ([a1a7], .notInTarget)`) and `a1h8` (illegal:
`some ([], .unavailable a1h8)`). `docs/spec/ChessGame.md` §6 lists them.

**Checks.** After the change every `ChessTest` target was rebuilt one at a time
(`lake build <target>` in sequence, under `/usr/bin/time -l`): `ChessTest.ChessGame` 11.5 s
(1.1 GB), `ChessTest.Axioms` 1.7 s, `ChessTest.Interface` 0.25 s once `Chess` was built,
`ChessTest.Perft` 279 s (largest resident size reported, 4.2 GB), `ChessTest.PerftDeep` 266 s,
then `ChessTest` (28 jobs) and `chess-perft`, all green with no warnings. A final
`lake build ChessTest` after the last edit (to `Chess/Puzzles.lean`) was green.

---

## Round 4 (2026-11-02, review fixes of ROADMAP step 5)

Author role: overnight implementer (`docs/process/Game.md` Round 6, `docs/process/Puzzles.md`
Round 2).

**Interface ledger.** Three entries added to `ChessTest/Interface.lean`:
`Game.Forces.forall_mem_nil` and `Game.Forces.forall_mem_cons` (the new glue for defender nodes)
and `Game.chess` (which generated files name when they call a checker or a diagnostic). Now 25
entries. The expected messages were copied from `#check` output and wrapped at binders
(`whitespace := lax`). Checked on a scratch copy: renaming the binder `t` of `forall_mem_cons`, or
changing the expected type of `Game.chess`, gives one error each.

**Axioms ledger.** `Forces.forall_mem_nil` and `Forces.forall_mem_cons` added to the `Chess.Game`
group of `ChessTest/Axioms.lean` (no axioms each). Now 133 entries (125 in `Axioms.lean`, 8 in
`AxiomsPerft.lean`).

**New file `ChessTest/Puzzles.lean`**, imported from `ChessTest.lean`: the three `#guard`s on
`Puzzles.gotham`, moved out of `Chess/Puzzles.lean` (spec `docs/spec/Puzzles.md` §2).

**Checks.** Since `Chess.Game.Cert` changed, every `ChessTest` target was rebuilt, one at a time
(`lake build <target>` in sequence, under `/usr/bin/time -l` and a 1500 s alarm):
`ChessTest.Interface` 0.25 s, `ChessTest.Puzzles` 1.4 s, `ChessTest.Axioms` 1.6 s,
`ChessTest.ChessGame` 12.0 s (1.1 GB), `ChessTest.ChessGame.Fide` 2.4 s, `ChessTest.Perft` 264 s
(largest resident size reported, 4.4 GB), `ChessTest.PerftDeep` 269 s, `ChessTest.AxiomsPerft`
0.6 s, then `ChessTest` (29 jobs), `chess-perft` and `Chess`, all green with no warnings. A clean
`lake build` of a fresh copy of the library (no `ChessTest`) took 7.7 s wall clock (14.3 s CPU,
peak 0.87 GB).

---

## Round 5 (2026-11-02, ROADMAP steps 6–7: the ledgers follow the library)

- `ChessTest/Axioms.lean`: nine entries added (R3: `reaches_symm`, `reaches_pawn_symm`,
  `Board.attacked_iff_superpiece`; M3: `Board.superpieceAttacked_iff`, `kingSafeAfter_iff`; the
  only-move root glue: `OnlyWinningMove.of_moves_eq`, `refuted_nil`, `refuted_cons_self`,
  `refuted_cons`), and the expected lines of `legalMoves_eq_filter`, `legalMoves_sound` and
  `mem_legalMoves_of_agreesWithLegal` updated: they now also use `Classical.choice` (through
  `kingSafeAfter_iff`), still [kernel]. The first build caught the last two (`#guard_msgs`). 142 entries with
  `AxiomsPerft.lean`.
- `ChessTest/Interface.lean`: five entries added (the four glue lemmas and `mem_chess_moves`),
  30 in all. `mem_legalMoves` stays recorded.
- The demo has its own ledger, `ChessDemo/Axioms.lean`; the test library does not import the demo.
- No test changed. `legalMoves_eq_filter` keeps its statement, so `legalMoves` lists the same moves
  in the same order as before (a theorem, not only a test); the perft counts and the differential
  test are unaffected by construction. The kernel perft checks of `ChessTest.Perft` got faster with
  the new king-safety filter (see the timing below).

---

## Note, 2026-11-02 (readability round): ledger names follow the renames

The axioms ledger (`ChessTest/Axioms.lean`, and its spec) now names `Board.attackedBy_iff`,
`Board.attackedBy_iff_superpiece` and `Board.superpieceAttackedBy_iff`, after Rules' rename of
`Board.Attacked` to `Board.AttackedBy` (Rules process log, Round 8). No entry was added or removed;
the moved lemmas (`CastlingRights.get_ofGet`, `rookCastleSquare_ne_kingHome`, …) kept their full
names, so their entries did not change. `lake build ChessTest`: green, 161 s, 3.4 GB maximum
resident set size.

---

## Note, 2026-11-02 (docs fix round): perft timings after step 6

The module docstring of `ChessTest/Perft.lean` and `docs/spec/ChessTest.Perft.md` §3 and design
choice 1 gave the kernel timings of Round 1 (depth 2 of the initial position 42 s and 3.9 GB),
measured before step 6's king-safety filter. Re-measured, one job at a time: depth 1 0.7–2.2 s per
position, depth 2 9.8 s (initial) and 5.6 s (Position 3), the module 39 s and 3.7 GB. The old
figures are kept, labelled "before step 6". No check changed. Details: `docs/process/Chess.md`
Round 2.

---

## Note, 2026-11-02 (docs fix round, finding docs-07): `PerftDeep` timing after step 6

The module docstring of `ChessTest/PerftDeep.lean`, `docs/spec/ChessTest.Perft.md` §4 and ROADMAP
step 3 gave the pre-step-6 time of the deep perft checks (4.4 minutes, 35 to 90 s each).
Re-measured with `set_option profiler true` in a scratch copy, one job at a time:
`lake env lean` on the module took 119 s wall clock, 0.37 GB, with the four checks at 39.3 s
(Kiwipete depth 3), 25.6 s (Position 5 depth 3), 30.1 s (Position 6 depth 3) and 23.9 s
(Position 3 depth 4). Two reviewers measured 137 to 146 s with other jobs running. The texts now
say about 2 to 2.5 minutes (about 25 to 40 s each) and keep the old figure labelled "before
step 6". No check changed. The 263 s entry of Round 1 above stays as history.

---

## Note, 2026-11-02 (ledger-coverage fix, finding trust-2)

Finding trust-2 (low): the header of `ChessTest/Axioms.lean` and `docs/spec/ChessTest.Axioms.md`
§2 said the ledger lists the "Main statements" of each module's docstring, but five named there
were missing (`forces_attacker_zero_iff`, `forces_attacker_succ_iff`, `forces_defender_iff` of
`Chess.Game.Laws`; `Forces.decidable`, `MateIn.decidable` of `Chess.Game.Search`).

Re-checking with a script that collects every backquoted name in the Main-statements section of
each file under `Chess/` and looks for it among the `#print axioms` entries of the three ledgers
found five more: `CastlingRights.get_ofGet` (`Chess.Position`) and `CastleMove.play_board_of_ne`,
`play_board_kingHome`, `play_board_kingCastleSquare`, `play_board_rookCastleSquare`
(`Chess.Rules.Castling`). The script's other hits were read one by one: they are definitions
(`legalMoves`, `IsFEN`, `Game.chess`, …), module names, variables (`p`, `s`, `t`) or the word
`decide`, none of them a theorem or instance.

- The spec first: §2 now says the source is every theorem and instance that a Main-statements
  section names, that a group mentioned without naming its members ("the other sanity theorems
  about the initial board", `Chess.Position`) is represented by its named members only, and that
  coverage is checked by the script, not by the build. The ten entries are listed under their
  modules (Position 12, Rules 33, Game 38) and §3's tally is updated.
- Then `ChessTest/Axioms.lean`: the Implementation note says the same, and the ten entries are
  added next to their neighbours (after `CastlingRights.revokeAll_le`, `CastleMove.legal_iff`,
  `wins_defender_iff` and `searchForces_iff`). The two entries with all three axioms are wrapped
  with `(whitespace := lax)`, like the others too long for one line.
- Result: 144 entries in `Axioms.lean`, 152 with `AxiomsPerft.lean`; 62 use the three axioms, 46
  `propext` and `Quot.sound`, 19 `propext` only, 25 none. All ten new ones are [kernel], so no
  trust label changes. ROADMAP §0 and §1 counts updated.
- Checks: `#print axioms` of the ten through `lake env lean` on a scratch file, then
  `lake build ChessTest.Axioms` (21 jobs, 1.8 s) green, and `lake build` green.
