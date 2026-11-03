# Verification report, night of 2026-11-01 to 2026-11-02

This report covers one night of work on the library: five build steps (ROADMAP steps 2 to 7), eight
independent audits, two skeptics per audit finding, and the fix rounds that followed. It says what
was built, what is proved and on what trust, what was only tested, and what is still open. Nothing
was committed during the night (it was committed afterwards, as `ae51012`; §9 covers 2026-11-03). Every figure below was measured on this Mac (16 GB) on 2026-11-02, one heavy Lean job
at a time, unless it is labelled otherwise.

## 1. Final state (measured after all fix rounds)

| Target | Result | Wall clock | Peak RSS |
|---|---|---|---|
| `lake build`, after `rm -rf .lake/build` | green, 20 jobs, no warnings | 7.4 s | 0.87 GB |
| `lake build ChessTest` (on that clean library build) | green, 32 jobs | 161 s | 3.5 GB |
| `lake build ChessDemo` | green, 24 jobs (`GothamCert` 163 s, `Mates` 20 s) | 165 s | 2.7 GB |
| `lake build chess-perft` | green, 34 jobs | 0.8 s | 0.39 GB |

The heavy modules of `ChessTest` are `ChessTest.Perft` (40 s) and `ChessTest.PerftDeep` (119 s).

**Counts per library.** Source counts exclude comments and docstrings. Kernel declarations include
the ones Lean generates (equation lemmas and the like).

| Library | Files | Lines | `theorem` | `example` | `#guard` | Kernel decls | `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `partial` |
|---|---|---|---|---|---|---|---|
| `Chess` | 18 | 6 047 | 415 | 52 | 23 | 1 836 | 0 each |
| `ChessTest` | 12 | 1 318 | 9 | 76 | 63 | 52 | 0 each |
| `ChessDemo` | 5 | 4 246 | 370 | 0 | 0 | 2 049 | 0 each |
| `chess-perft` | 1 | 65 | 0 | 0 | 0 | (none) | 0 each |

So no `native_decide` is used anywhere, and the rule that allows it in test or demo files whose
theorem names end in `_native` was never needed.

**Axioms.**
- **Whole-library scan.** It ran `Lean.collectAxioms` on every declaration of the three libraries
  (47 s, 1.2 GB). No declaration depends on anything beyond `propext`, `Classical.choice` and
  `Quot.sound`: no `sorryAx`, no `Lean.ofReduceBool` and no `Lean.trustCompiler`. No library
  declares an axiom or an unsafe declaration.
- **Partial declarations.** The only ones are the 10 `_unsafe_rec` auxiliaries that the compiler
  generates for well-founded definitions. They matter only for compiled and interpreted code
  (`#guard`, `#eval`, `chess-perft`), never for a kernel proof.
- **Ledgers.** Each is a `#guard_msgs` check that passes in the builds above:
  - `ChessTest/Axioms.lean`: 144 entries.
  - `ChessTest/AxiomsPerft.lean`: 8 entries.
  - `ChessDemo/Axioms.lean`: 16 entries.
  - `ChessTest/Interface.lean`: the signatures of 30 names that generated files may use.
  - Every entry in the axioms ledgers is [kernel].
- **Independent kernel replay.** All 3 937 declarations of the three libraries were replayed from
  the `.olean` files into a fresh environment that imports only `Init`, using core
  `Environment.replay` (the lean4checker method). The kernel accepted every one (255 s, 4.2 GB).
  - **Exception:** the two nested-inductive auxiliary recursors `Chess.Cert.rec_1` and `rec_2` were
    left out, because the replay's recursor comparison fails on them. Every declaration that uses
    `Cert` did replay.
  - The only module root imported from outside the libraries is `Init`.

**Docstrings.** `scripts/check_docstrings.py` reports 0 definitions whose docstring is missing from
its spec. The theorem docstrings it lists are the two documented exceptions in ROADMAP §0: lemmas
grouped in one spec table cell in `Basic` (67), and the THEOREMS-tag rule in `Game` (26).

## 2. What was built, step by step

| Step | What landed |
|---|---|
| G8 (ROADMAP step 2) | `Chess/Spec/Winning.lean` imports only `Chess.Rules`. It defines `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecMateIn` and `SpecOnlyWinningMove` from `Legal`, `Position.play` and `Checkmate`. `Chess/ChessGame/Fide.lean` proves each chess-game notion equivalent to its `Spec` version, unconditionally (`winsIn_iff_specWinsIn` and four more, plus `forces_iff_specForces` for every target). After this, `MoveGen` and `Game` are no longer in a headline's trusted base. |
| Tests and M7 (step 3) | The `ChessTest` library holds the moved tests. The perft suite has 8 kernel theorems (depth 1 for the six standard positions; depth 2 for the initial position and Position 3) and `#guard`s up to depth 4. The axioms ledger was added, along with the `chess-perft` program and `scripts/perft_diff.py`. `Position.tabulate` (with `tabulate_eq`) works around slow FEN boards in compiled code. |
| L4.11 (step 4) | `CastleMove.legal_iff`: castling is legal exactly when the king's landing square is not attacked before the move, on every board, with no one-king hypothesis. This closes the gap between the post-move test and the literal FIDE 3.8.2 text. |
| Certificates (step 5) | `Chess.Game` was split into `Defs` (trusted, 130 lines), `Laws`, `Search`, `Cert` and `Examples`. Added: `OnlyMoveCert` with a single `refBudget`; a frozen generated-file interface; the diagnostics `firstFailure*`, proved to return `none` exactly when the checkers accept; and `Puzzles.gotham`. |
| Gotham (steps 6 and 7) | `kingSafeAfter` (proved equal to the old king-safety filter, via the new attack symmetry R3) cut the kernel cost of a mate leaf from 2.0 s to 0.7 s. `scripts/gen_cert.py` was ported and is deterministic. `ChessDemo` holds the generated `GothamCert` (319 per-node theorems), `Gotham` (the headlines) and `Mates` (exact `MateIn` 1, 2 and 3). |
| Fix rounds | `Chess.Rules` was split into `Defs` (trusted definitions only, 396 lines), `Laws` and `Castling`. Renamed `Board.Attacked` → `Board.AttackedBy`. Corrected false or stale trusted text. Moved helpers to the modules where they belong. Added `scripts/check_docstrings.py`, and documentation drift was fixed across README, ROADMAP, DESIGN, THEOREMS and the specs (§5). |

## 3. What is proved, and on what trust

Every theorem in all three libraries is checked by the kernel with the standard axioms only
([kernel]). None is [native]. No headline depends on an unproved hypothesis ([hyp]).

- **Gotham.** `ChessDemo.gotham_winsIn : WinsIn .black 11 Puzzles.gotham` and
  `gotham_onlyWinningMove : OnlyWinningMove Puzzles.gotham (uci "b7b2")`.
  - Through G8 they are restated with the rules alone: `gotham_specWinsIn` and
    `gotham_specOnlyWinningMove`.
  - `gotham_refuted` and `gotham_specRefuted` add that after each of Black's other 33 moves, White
    forces mate (30 within 1, two within 2, one within 5).
  - The proof uses 964 `decide +kernel` calls, on 679 lines.
  - The claim is "within 11", not "exactly 11": `MateIn` is not claimed for Gotham. *(Superseded on
    2026-11-03: `gotham_mateIn` proves exactly 11; see §9.)*
- **Generator.** `legalMoves` is proved sound and complete (`mem_legalMoves`, M4), and so are
  `checkmate_iff` and `stalemate_iff` (M6). That it lists no move twice (M5) is **tested only**. *(Proved on 2026-11-03,
  `legalMoves_nodup`; see §9.)*
- **Game layer.** Proved:
  - search correctness (`searchForces_iff`);
  - checker soundness (`checkWin_sound`, `checkOnlyMove_sound`);
  - win-checker completeness (`checkWin_complete`). `checkOnlyMove` has no completeness theorem.
    It cannot certify a claim in which some alternative only draws.
- **Exact mates.** `Mates` proves `MateIn` 1 and 2 by search. For `MateIn` 3, the win is proved
  by a certificate and minimality by search.
- **Trusted base of a headline.** A reader must trust:
  - the kernel;
  - the English and Lean of `Basic`, `Position`, `Rules/Defs` and `Spec/Winning`;
  - the notation of `ChessGame`: the writers, `IsNumeral`, `ClockFields`, `IsFEN`,
    `Position.Sane`, and the statements of `fen_eq_iff` and `uci_eq_iff`;
  - the FEN string in `Chess/Puzzles.lean`.

  A closure scan of the three `spec` Gotham statements reached no `MoveGen` or `Game` constant.
- **Caveats on that reading.**
  - FIDE's draw rules (50/75 moves, repetition) are not modelled, and FEN clocks are ignored (G15).
  - `Position.Sane` admits positions no game can reach, for example a pawn on its first rank.
  - `Spec/Winning` has had only a self-review.

## 4. Differential and cross-checks (tested, not proved)

Because M4 is proved, `legalMoves` equals the moves allowed by `Legal`. Agreement of the generator
with python-chess is therefore also a test of the trusted rules. The FIDE audit (row 3) tested the
rules directly as well, without the generator.

| Check | Size | Result |
|---|---|---|
| Step 3: `chess-perft` vs python-chess 1.11.2 (standard positions to depth 4, two to depth 5, random, en passant, castling/promotion, 16 named positions) | 546 jobs, about 26.2 million leaves | 0 disagreements |
| Perft audit: deep totals vs published counts (7 positions, depths 4 to 6); random-play positions at depth 2 to 3 vs python-chess; depth-3 divides vs Stockfish; targeted castling/en passant/promotion cases vs Stockfish up to depth 7 | about 18 600 random positions; 240 vs Stockfish; 66 targeted | 0 mismatches |
| Perft audit: 400 random games replayed through `parseUCI`, `legalMoves` and `Position.play`, FEN compared each ply | 30 578 plies | identical |
| FIDE audit: compiled spec-only `legalMovesBySpec`, `InCheck` and `Board.AttackedBy` vs python-chess (legal moves, check, attacked squares), generator not used | 7 992 positions | 0 mismatches |
| FIDE audit: hand-worked `#guard`s and kernel examples on castling, en passant, promotion, pins, mates and stalemates | 89 guards, 7 kernel | all pass |
| Notation audit: `readFEN`/`parseFEN` vs a python-chess model (accept or reject, board, turn, castling, en passant, `Sane`) | 7 205 strings | 0 mismatches |
| Notation audit: `play` then `toFEN` vs python-chess; the UCI writer on all 20 480 moves; `parseUCI` on 3 105 strings; legal-move sets on 1 500 FENs | as stated | agree, except where python-chess itself flags the input invalid (an en passant target with no victim pawn, which the library rightly refuses) |
| Gotham audit: the 314 certificate checkpoints vs python-chess (moves, check); the certificate re-verified under python-chess rules; Stockfish 19 mate distances | 314 positions; 33 refutations | all agree; every refutation budget equals Stockfish's mate count |
| Game audit: exhaustive small certificates on three toy games | 19 593 certificates | 0 accepted for a false claim |
| **Final pass, after all fixes**: `perft_diff` on the standard positions at depth 3, the 16 named positions, `rand 200 2 20261102`, and fresh seeds `ep 50 3 31337` and `special 50 3 2718` | 337 jobs | 0 disagreements |
| **Final pass**: `gen_cert.py` rerun into scratch | 319 nodes | byte-identical to `ChessDemo/GothamCert.lean`; `--check` reports `none` |

Not run: Kiwipete at depth 5 (estimated at about an hour). Only 4 en passant captures occurred in
the 30 578 replayed plies; en passant is covered mainly by the divide tests.

## 5. Verification dimensions

Each audit edited nothing in the repository and wrote its scratch work under
`scratchpad/overnight/<dimension>/`.

| Dimension | What it checked | Outcome |
|---|---|---|
| gotham | The FEN against the prototype and python-chess; the headline statements and their `#print axioms`; re-elaborating `GothamCert` (197 s, 1.0 GB); regeneration from `gen_cert.py`; the 314 checkpoints; Stockfish 19 mate distances | No defect; 2 low documentation findings |
| readability | Read every file in `Chess/` top down; docstring/spec match; fragility experiments (adding a conjunct to a rule); duplicated concepts | No correctness defect; 5 medium and 11 low findings on layout, names and stale text (4 of the low ones disputed) |
| game | `Forces`, `WinsIn`, `MateIn` and `OnlyWinningMove` hold in some toy games and fail in others; stalemate and endless play are not wins; bogus certificates rejected (toy and chess); the budget convention matches Stockfish; G8 is unconditional | No soundness defect; 4 low documentation findings |
| docs | 542 backticked names resolved by a Lean meta script; signatures of about 80 cited theorems; counts, paths, cross-references and timings re-measured | 22 findings (21 confirmed), all documentation drift or overclaims, no false theorem |
| trust | Axiom scan; kernel replay from `Init`; closure of the headline statements; ledger counts; lakefile and import graph; forbidden constructs | Core trust claims hold; 7 low documentation findings |
| notation | The FEN/UCI read and write differential tests of §4; `fen_eq_iff`, `uci_eq_iff` and `IsFEN.unique` say what the docs claim | No soundness or meaning defect; 4 low findings |
| fide | `Rules` against the FIDE Laws (2023), Articles 3, 5.1.1 and 5.2.1, line by line, plus the spec-only differential test of §4 | No rule admits an illegal move or forbids a legal one in any reachable position tested; 4 low findings |
| perft | The deep, random, targeted and replay tests of §4; edge behaviour of `chess-perft` | No generator defect |

## 6. Confirmed findings and their disposition

A finding counted as confirmed when both skeptics reproduced it. 54 findings were confirmed. As
filed, 11 were medium and 43 low; the skeptics rated most of the mediums low. **None is a false
theorem or a soundness defect.** All concern documentation, naming or layout.

| Findings | What was wrong | How it was handled |
|---|---|---|
| readability-trusted-interleaved | The trusted rule definitions were spread through 1 280 lines of lemmas | **Fixed**: `Chess/Rules/Defs.lean` holds only definitions and instances, in reading order; `Laws` and `Castling` hold the proofs; `ChessGame`'s trusted predicates now come before the parsers |
| readability-readme-reading-path, trust-5, trust-6 | The README sent readers to untrusted files and omitted `Spec/Winning`, and did not disclose the self-review | **Fixed**: the README is now an audit path through the trusted base; `Chess.lean` has a module docstring; the self-review is stated |
| readability-castling-rights-docstring-false, fide-3 | Trusted text said rights change only through `revoke` and `revokeAll` | **Fixed**: the text now names `Move.castlingAfter`, R8 now refers to `castling_play_le`, and `ofGet` moved to `Position` |
| readability-ofcode-stale-docstring, docs-01 | The `Piece.ofCode` notes described the search it no longer uses | **Fixed** |
| readability-attacked-colour-role | `Attacked c` named the attacker; `KingAttacked c` named the victim | **Fixed**: renamed to `Board.AttackedBy` and `superpieceAttackedBy` |
| readability-misplaced-helpers, readability-duplicated-concepts | Geometry helpers sat in `Rules`, some of them private; there were two copies of `squaresOf` | **Fixed**: the helpers moved to `Basic` and `Position`; `kingSquares` was removed |
| readability-agreesWithLegal-superseded | A per-position M4 was advertised although full M4 is proved | **Fixed** in the docs (only the M5 half informs); the code stays in the library |
| readability-zero-based-relrank, readability-checkmate-citation, readability-minor-doc-drift | 0-based ranks not flagged; Checkmate cited the wrong FIDE article; five small items | **Fixed**; Checkmate now cites FIDE 1.4 and 1.4.1 |
| notation-2 | The `fen` docstring did not warn about the en passant convention | **Fixed**: the docstring now warns (spec first); the inequality was kernel-checked |
| docs-02, -03, -04, -05, -06, -07, -08, -09, -10, -11, -12, -13, -14, -15, -16, -17, -18, -19, -20, -22; gotham-1, gotham-2; game-1 to game-4; trust-1, -2, -3, -4, -7; notation-1, notation-3; fide-1, fide-2 | Stale timings, statuses and signatures; overclaims (`checkOnlyMove` "complete", the mate in 3 "by search", the "unique optimal move"); incomplete trust and interface lists; wrong FIDE numbers; parser description | **Fixed**. Timings were re-measured, not halved or guessed. trust-2 added 10 ledger entries, all standard. trust-1 now describes the ledgers rather than adding labels to docstrings. |
| readability-winsIn-naming | The plain name `WinsIn` belongs to the generator-based notion | **Deferred**: owner decision (ROADMAP step 7a, open owner decisions) |
| notation-4 | Spec §7 plans to change what `fen` means in Stage 2; review C4 says not to | **Deferred**: recorded as an open owner decision in the spec, THEOREMS M11 and ROADMAP step 8 |
| fide-4 | `Position.Sane` admits a pawn on its own first rank | **Deferred** to Stage 2's `WellFormed` (ROADMAP step 7a) |

Not done within these fixes:
- the optional `docs/TRUSTED.md` index;
- the namespace rule from Rules review C5;
- the `Game/Defs` module docstring still opens "The trusted part of `Chess.Game`", which is true
  inside `Chess.Game`;
- several pending THEOREMS edits from DESIGN §12 (the `§0.5` renames, R7, R9.4, G9/O6, G15);
- the dated review `docs/reviews/Position.md` still describes the old `ofCode`.

## 7. Disputed findings (one skeptic only), for the owner to judge

None of these was acted on.

| Finding | Claim | For | Against |
|---|---|---|---|
| readability-positional-destructuring | Proofs take rules apart by position; three positional projections into `CastleMove` remain next to the new accessor | Reproduced: putting `True ∧` in front of `PushMove` breaks 10 proofs | Deliberate: the process log keeps single-use projections; owner choice 14 keeps conjunctions; a break shows at build time, never silently |
| readability-unused-trusted-defs | `Move.IsCapture` and `Board.HasKing` are in trusted text but unused by definitions; `Attacked` has an extra layer | `IsCapture` is unused, and the Lean docstring does not say so (the spec does) | `HasKing` names trusted theorem statements; `AttacksFrom` is a recorded design choice (64 reads, not 64 × 12) and appears in `PseudoLegal.attacksFrom_dst`; `IsCapture` is reserved for R7 |
| readability-stalemate-hypotheses | `Chess.not_wins_of_stalemate` takes generator terms, not `Stalemate p` | The `Stalemate p` form is one line away (checked) | It mirrors `Game.not_wins_of_stalemate`; its docstring points to `stalemate_iff`; the spec records it as not restated |
| readability-flexible-simp | 13 non-terminal plain `simp` calls in `Basic` before `omega`/`decide` | `simp only` works for six of the lemmas; Basic spec's own style rule prefers `simp only` | The toolchain is pinned; omega and decide do not depend on the goal's exact shape; the claimed `simp only` proof of `dir_eq_of_shift_eq` fails as written |

## 8. What remains open

- ~~An independent review of `Spec/Winning` and `ChessGame/Fide`.~~ Done 2026-11-02 in a separate
  session: `docs/reviews/G8_REVIEW.md`. It found no soundness defect, and no finding affects Gotham.
  F1 (the definitions are meant for positions where the side not to move is not in check) and the
  F4 nits are now documented. Still open from it: F2, a parser-free statement of the Gotham board,
  and F3, the kernel stalling on `∀ r, Legal p r → …`. `Chess.Puzzles` has no file-level review.
- ~~M5 (`legalMoves` has no duplicates) is tested only.~~ Proved 2026-11-03: `legalMoves_nodup` (§9). M4 and M6 are proved.
- **Owner decisions:**
  - the `WinsIn`/`SpecWinsIn` naming;
  - whether `fen`'s filter stays `Sane` or gains `WellFormed` (notation-4);
  - the en passant convention sign-off (ROADMAP open owner decisions);
  - the four disputed findings above.
- **Stage 2:** `WellFormed`, including no pawn on a back rank and castling rights that match the
  rooks (fide-4).
- **Kernel perft gaps:**
  - depth 2 of Kiwipete and Positions 4 to 6 (only `#guard`ed);
  - an optional retry of depth 3 of the initial position (ROADMAP step 8).
- **Performance:** a board read from a FEN re-reads the text on every square in compiled code. It
  is worked around by `Position.tabulate`; the options are in ROADMAP §4.

Scratch logs of this final pass were kept outside the repository (build logs and timings, `Scan.lean`, `count.py`, `Replay.lean`, the perft job files and results,
and the regenerated certificate).

## 9. Addendum (2026-11-03): mate in exactly 11

**What is proved.** `ChessDemo.gotham_not_winsIn_ten : ¬ WinsIn .black 10 Puzzles.gotham`,
`ChessDemo.gotham_mateIn : MateIn .black 11 Puzzles.gotham` and `ChessDemo.gotham_specMateIn :
SpecMateIn .black 11 Puzzles.gotham`, in `ChessDemoBound/GothamMateIn.lean`, each with
`#print axioms` = `[propext, Classical.choice, Quot.sound]` checked by `#guard_msgs`. The lower half
is the generated certificate `ChessDemoBound/Gotham10/` (159 files, 24,994 node theorems over
21,417 checkpoints), chained by the glue of `Chess.Game.Cert` section `Bounds` (THEOREMS C9).

**How it was checked.**

* *Build.* `lake build ChessDemoBound`: 178 jobs, 46 min wall on 10 cores, 4.5 CPU-hours, peak
  0.9 GB per process.
* *Bug check 1, three independent reviewers on the diff.*
  * **Lean soundness:** no defect. The definitions mean mate in 11 as a chess player means it. The
    ten C9 lemmas are proved from existing laws and add no hypothesis. A search for trust leaks
    (`sorry`, `native_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `set_option`,
    `opaque`, `macro`/`elab`/`#eval`, …) over the library and all generated files found none.
    `root_eq` ties the certificate to `Puzzles.gotham`. Spot checks of every node kind passed. A
    `leanchecker` kernel replay passed on `GothamMateIn`, `Claim`, `Moves` and 11 node modules (not
    all 159).
  * **Python tooling:** no soundness issue, since Lean checks everything. The search's semantics
    match `Forces`, its memos are sound, and the certificate is acyclic. Regenerating `--budget 10`
    reproduces `ChessDemoBound/Gotham10` byte for byte, and `chess-perft --moves` handles its edge
    cases. Two defects, both fixed:
    * the measurement reused one Stockfish hash table across budgets, so the documented n = 10
      statistics described a different certificate from the proved one; each budget now starts
      fresh, and the numbers match the proof;
    * `gen_bound.py` left stale files of an earlier run in its output directory; they are now
      removed.
  * **Docs against code:** 11 inaccuracies, all fixed. The most serious were:
    * Stockfish was called optional, but without it the search does not finish;
    * the file and equation counts were wrong;
    * a White node's closings were described incompletely;
    * the checkmate cost contradicted the total;
    * a stale "no lower bound" line and a wrong theorem name remained in THEOREMS;
    * the viewer's counter read "Move 21 of 21" under "mate in 11" (it now counts half-moves).
* *Outside cross-check (not part of the proof).* Stockfish 19, searching the root alone at depths
  20, 26 and 32, and with a `mate 10` search to depth 40, reports mate in 11 with 1…Rxb2+ and no
  shorter mate.

**M5 proved.** `Chess.legalMoves_nodup : ∀ p, (legalMoves p).Nodup` (`Chess/MoveGen.lean`, section
`NoDuplicates`), standard axioms. The geometric facts it needs (rays in different directions are
disjoint, knight jumps, king steps and pawn targets from one square are distinct, a castling
destination is not adjacent to the king's home) are decided by the kernel once over all 64 squares
(about 6 s of the library's build); the rest is about lists. With it, M8 is proved too:
`perft_eq_length_lines : perft n p = (lines n p).length`, where `lines n p` lists exactly the legal
lines of `n` moves (`mem_lines`), none twice (`lines_nodup`). So every kernel-checked perft count in
`ChessTest.Perft` is a theorem about the number of legal move sequences.

**Not covered.** Two generator paths are not exercised by the Gotham certificate: a defender
stalemated inside the certificate, and an attacker with no legal move. They are tested on two small
generated certificates, `ChessDemoBound/Tests/NoMoves` and `ChessDemoBound/Tests/Stalemate`
(`ChessDemoBound/Tests.lean`), which build with the standard axioms. The build-time figures are
from one machine.

**Full rebuild after the fixes.** `lake build Chess ChessTest ChessDemo ChessDemoBound chess-perft`
after `Chess.ChessGame` stopped importing `Chess.Game.Examples` (which rebuilt everything): 216
jobs, 38 min wall, 3.5 CPU-hours, peak 3.4 GB (the test library), no errors, no warnings.

