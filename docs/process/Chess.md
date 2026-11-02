# Process log: the root `Chess` and the README

The record of changes to the library's root file (`Chess.lean`) and to its entry documentation
(`README.md`). The root has no declarations, so it has no specification in `docs/spec/`; its module
docstring repeats the trusted base stated in `docs/ROADMAP.md` §2.

---

## Round 1: the reading path follows the trusted base

Date: 2026-11-02. Author role: overnight fixer, finding `readability-readme-reading-path` (medium;
reproduced by two skeptics, one of whom rated it low).

**The finding.** The README's "What to read first" sent a newcomer from `Chess/Rules/Defs.lean` to
`Chess/Game/Defs.lean` ("what `WinsIn`, `MateIn` and `OnlyWinningMove` mean") and then to
`Chess/ChessGame.lean`, and never named `Chess/Spec/Winning.lean`. Since G8, ROADMAP §2 says that
the section "Games" of `Game`, `Game.chess` and the four abbreviations are not in the trusted base
of a chess headline, which is read as `SpecWinsIn` or `SpecOnlyWinningMove` through
`Chess.ChessGame.Fide`. The file map also called `Game/Defs` "trusted" and `MoveGen` only "proved
sound", although M4 (`legalMoves_complete`, `mem_legalMoves`) is proved. `Chess.lean` said only
"Root of the `Chess` library".

**What changed.**
- README, "What to read first": rewritten as an audit path. ROADMAP, then `Basic`, `Position`,
  `Rules/Defs`, `Spec/Winning`, and the notation of `ChessGame` (writers, `IsNumeral`,
  `ClockFields`, `IsFEN`, `Position.Sane`, the statements of `fen_eq_iff` and `uci_eq_iff`), then
  the FEN string of `Puzzles.gotham`. These items, with the kernel, are called the trusted base, and
  the two caveats of ROADMAP §2 (no draw rules, G15; `Position.Sane` admits unreachable positions)
  are repeated. A paragraph says how a headline stated with the abbreviations is read through G8.
  A second list, "How claims are computed, not what they mean", holds `MoveGen` (sound and
  complete, M4), `Game/Defs` and the rest of `Chess/Game/`, `Game.chess` with the abbreviations, and
  `ChessGame/Fide`. The pointer to headline-style tests now names `ChessTest/ChessGame.lean`, where
  they are (they are no longer at the bottom of `Chess/ChessGame.lean`).
- README, file map: `MoveGen` is "proved sound and complete, M4"; `Game/Defs` is "the meaning for
  an abstract game, not trusted for chess headlines since G8"; the `ChessGame` row says which part
  is trusted; the `Chess.lean` row says its docstring repeats the map.
- `Chess.lean`: a module docstring with the trusted base, the untrusted parts and the caveats, in
  the same terms as ROADMAP §2 and the docstring of `ChessDemo/Gotham.lean`. No declaration
  changed.

**Not changed.** `Chess/Game/Defs.lean` still opens "The trusted part of `Chess.Game`". Within
`Chess.Game` that is accurate (it is what an abstract-game claim means), and its last
implementation note already says a chess headline can be read without the file, so it was left
alone.

**Checked.** `lake build` green; `scripts/check_docstrings.py` reports no missing docstring (no
declaration was touched). Every file and name the new text cites was checked to exist:
`Chess/Spec/Winning.lean` (five definitions, 124 lines in all), `mem_legalMoves` and
`legalMoves_complete` in `Chess/MoveGen.lean`, `Puzzles.gotham` in `Chess/Puzzles.lean`, Fool's mate
in `ChessTest/ChessGame.lean`.

---

## Round 2 (2026-11-02): THEOREMS.md and the perft timings follow the code

Fixes for six documentation findings of an independent review, each reproduced by two skeptics
(all rated low by them). No Lean declaration changed; the only Lean edit is the module docstring
of `ChessTest/Perft.lean`.

- `docs/THEOREMS.md`:
  - §1: the headline is `Chess.OnlyWinningMove gotham (uci "b7b2") ∧ Chess.WinsIn .black 11
    gotham` (it said `.white`; Gotham is Black to move), with a pointer to the two theorems the
    demo proves. The goal sentence no longer claims "unique optimal move"; that is O2, Stage 3
    (DESIGN §12's wording).
  - G1: `turn_play` and `moves_eq_nil_of_mated` take implicit binders, as in `Chess/Game/Defs.lean`.
  - G2: `not_wins_of_stalemate (hnm : ¬ G.Mated x) (hl : G.moves x = [])`, with no turn
    hypothesis, as in `Chess/Game/Laws.lean`; the stronger statement is noted.
  - C3: the "Realized" note no longer says the six step-5 lemmas are the whole glue. It names the
    step-7 additions (`OnlyWinningMove.of_moves_eq`, `.refuted_nil`, `.refuted_cons_self`,
    `.refuted_cons`, and `mem_chess_moves`) and points to Game spec §4.3, `scripts/README.md` and
    `ChessTest/Interface.lean` for the complete list.
  - C7: the sketch concludes `WinsIn (G.turn x) n x`, and the "Realized" note says the budget is
    counted at `x`, before the best move (DESIGN §7.2).
  - M2, M4, M6: status lines (done, `section Completeness` of `Chess/MoveGen.lean`, MoveGen spec
    L7.2–L7.4, L7.6–L7.7). M4's says the sketched `Decidable (Legal p m)` instance was not added
    (Rules' `Legal.decidable` is used) and that `legalMoves_eq_filter` ties the `kingSafeAfter`
    filter to `Legal`. M6's names `Checkmate.decidableByGen` and `Stalemate.decidableByGen`.
  - M7: the "out of reach" note for `perft_initial_3` is dated to step 3 and given the new
    figures; whether depth 3 now fits is left open.
  - §7: the Stage 2 headline paragraph says M4 and G8 are proved. §8: the dependency map shows
    `M3 kingSafeAfter_iff` instead of "(M3 deferred)".
- `ChessTest/Perft.lean` (module docstring) and `docs/spec/ChessTest.Perft.md` §3 and design
  choice 1: kernel timings re-measured after step 6, the old ones labelled "before step 6".
- `docs/ROADMAP.md`: the test-memory risk row carries the new figures (severity lowered to low);
  the document-drift row lists what was applied; step 8 gains an optional item, a retry of
  `perft_initial_3` in the kernel. `docs/DESIGN.md` §12 records which of its edits were made.

**Measured** (this machine, no other Lean job running): `lake env lean -Dprofiler=true
ChessTest/Perft.lean`, 38.9 s wall clock, 3.7 GB maximum resident set size (`/usr/bin/time -l`).
Type checking: depth 1, 0.7 s (initial), 2.2 s (Kiwipete), 0.8 s (Position 3), 1.5 s (Position 4),
1.8 s (Position 5), 1.8 s (Position 6); depth 2, 9.8 s (initial) and 5.6 s (Position 3). The
profiler does not name declarations; the attribution assumes its lines follow the file's order,
after the five position definitions (each 0.4–0.7 s, measured separately in a scratch file).

**Not done.** The rest of DESIGN §12 (the §0.5 renames, R4, R7, R9.4, M3's `inCheck_eq_true_iff`,
G9, O6, G15, the `G.` prefix throughout, M7's bug-class positions, and §7's "exactly 11", which
already carries a dated note) is still for the theorem architect; ROADMAP §7's name map covers it.
`perft_initial_3` in the kernel was not tried.

## Round 3 (2026-11-02): README and ROADMAP §1 say only what is proved

Fixes for four documentation findings of an audit, each reproduced by two skeptics (all low or
medium, none in Lean). No Lean file of `Chess/` changed.

- **`Cert` overclaimed (docs-04).** The README file map said `Cert` and `OnlyMoveCert` come "with
  checkers proved sound and complete". Only `checkForces` and `checkWin` have completeness theorems;
  `checkOnlyMove` has only `checkOnlyMove_sound`, and a completeness theorem would be false (an
  alternative that only draws can never be refuted by a win certificate; ROADMAP §4). Now: "proved
  sound, the win checker also complete".
- **Test layout and the mate in 3 (docs-16).** The README said `ChessTest/` has "one file per
  library module". It has the tests of `Rules`, `MoveGen`, `ChessGame`, `ChessGame/Fide` and
  `Puzzles`; `Basic` and `Position` keep a `## Tests` section, and `Game` has
  `Chess/Game/Examples.lean`. The README now says so, and its file map names `Tabulate.lean`. The
  README, ROADMAP §1 (module table and closing-demo row) and THEOREMS §7 said the three exact mates
  are proved by search; the mate in 3 proves its win by a certificate (`rookMate3_winsIn`) and only
  its minimality by search (`rookMate3_not_winsIn_two`), as `ChessDemo/Mates.lean` already said in
  its implementation notes. All four places now say this (the module docstring of `Mates` and the
  root docstring of `ChessDemo`: see `docs/process/ChessDemo.md`, Round 3).
- **`Game/Defs` called trusted (trust-5).** The README part was already fixed by an earlier round
  (its file map and reading list follow G8). ROADMAP §1's module table still said "`Game/Defs`
  (trusted)"; it now says that since G8 it is not in a chess headline's trusted base unless the
  headline is read as `Chess.WinsIn` itself (DESIGN §7.3).
- **Review status of `Spec/Winning` (trust-6).** ROADMAP step 7 requires every summary for the
  owner to say that the trusted file under the G8 headlines has had only a self-review. The README
  status paragraph and the ROADMAP §1 closing-demo row now say it.

**Checks.** `lake build` green (no Lean change in `Chess/`); `lake build ChessDemo` green (19 s,
2.77 GB maximum resident set size); `scripts/check_docstrings.py` exit 0 with the same theorem
paraphrase reports as before; a scan of `Chess/` and `ChessDemo/` finds no `sorry`, `admit`,
`native_decide`, `axiom`, `unsafe` or `implemented_by` outside comments and docstrings.

## Round 4 (2026-11-02): DESIGN and THEOREMS caught up with steps 1–7

Fixes for eight documentation findings of an audit, each reproduced by two skeptics (one medium,
seven low; both skeptics rated the medium one low). No Lean file changed.

- **The generator's filter (docs-02).** DESIGN §5.7 and THEOREMS M4 ("Forces") gave `legalMoves` as
  `(pseudoMoves p).filter` of `¬ … KingAttacked …`; since ROADMAP step 6 it is
  `(pseudoMoves p).filter (kingSafeAfter p)`. Both now state the current definition, with
  `kingSafeAfter_iff` and `legalMoves_eq_filter` as the link to `Legal`, and say what it was before
  step 6. DESIGN §5.7 no longer says "M4 will relate" (M4 is proved) and says that M5
  (`legalMoves_nodup`) is still planned. THEOREMS M4's "Meta" no longer says it does not depend on
  M3. The MoveGen spec's design choice 7 is fixed in the same way (`docs/process/MoveGen.md`).
- **Toy games (docs-10).** DESIGN §6.1 and THEOREMS G1 named a subtraction game and tic-tac-toe in
  `test/`. There is no tic-tac-toe and no `test/`; both now name the take-away games
  `Game.Toy.takeAway` and `Game.Toy.takeAwayStalemate` in `Chess/Game/Examples.lean`.
- **Passages written before steps 1 and 6 (docs-13).** DESIGN §2 (the super-piece test "may be
  added later"), §5.6 (the cheap decision of `Checkmate` "goes through the generator in Stage 2")
  and §6.1 (the `isLegal` option "waits for Stage 2") each keep their text and gain a dated
  *Outcome* note, as §7.4 has: `Board.superpieceAttackedBy_iff` and `kingSafeAfter_iff`;
  `Checkmate.decidableByGen` and `Stalemate.decidableByGen`; attacker nodes decide `Legal p m`
  through `mem_chess_moves`, with no `isLegal` field. §10's "bridged to `Checkmate` in Stage 2"
  now says it is done.
- **Decisions taken (docs-14).** DESIGN §10's open question on one refutation budget or one per
  alternative is struck through and marked decided (one, `refBudget`, Game spec choice 24). §11's
  C1 row says it was adopted in substance in step 6, and the `Game`/`Certificate` row names
  `Chess/Game/Cert.lean` instead of a planned `Chess.Game.Certificate`.
- **DESIGN §12 (docs-15).** Every item of the list was checked against THEOREMS today and marked
  *Made*, *In part* (saying which part) or *Pending*. Made: §1's sentence, R4, R6, R8, M3 with G1
  and M4, C7. In part: §0.5 (pending: the sentence on authoritative names, `Reach`, `searchWin`,
  `Cert.mate`), §1 and §7 (G5 and C4 not changed), the G-tier prefix, M7. Pending: R7, R9.4, G9
  and O6, G15.
- **Where trust labels live (trust-1).** DESIGN §7.3 and THEOREMS §0.4 said every headline theorem's
  docstring states its label; only the eight perft theorems of `ChessTest/Perft.lean` do. Of the
  two fixes offered, the cheaper one was taken: both documents now say the label is recorded and
  checked by the three axioms ledgers (`ChessTest/Axioms.lean`, `AxiomsPerft.lean`,
  `ChessDemo/Axioms.lean`), and that every theorem listed there is [kernel]. No docstring changed.
- **`Chess.Puzzles` in the trusted base (trust-4).** DESIGN §7.3, the layer diagram of DESIGN §3
  and ROADMAP §2 now list the definitions of the named positions a headline mentions. The README's
  reading list and `Chess.lean` already did; the README's file map now labels `Chess/Puzzles.lean`
  trusted, as `docs/spec/Puzzles.md` does.
- **DESIGN §8.7 (trust-7).** The closing-demonstration bullet keeps its plan and gains an *Outcome*
  note describing the library `ChessDemo` (four modules, its ledger of 16 entries, all [kernel], no
  `native_decide`). The `ChessTest` bullet now names the tests of `Puzzles` and the interface
  ledger `ChessTest/Interface.lean`.

**Checked against the code** (by reading it, this round): `legalMoves`, `kingSafeAfter`,
`legalMoves_eq_filter` and `kingSafeAfter_iff` in `Chess/MoveGen.lean`; `mem_chess_moves` in
`Chess/ChessGame/Fide.lean`; `OnlyMoveCert.refBudget` in `Chess/Game/Cert.lean`; the module
docstring of `Chess/Game/Examples.lean`; the entry counts of the three ledgers (134, 8 and 16
`#guard_msgs` entries); a scan of `Chess/`, `ChessTest/`, `ChessDemo/` and the root files with
comments removed finds no `native_decide`, `sorry`, `admit`, `axiom`, `unsafe` or
`implemented_by`.

**Checks.** `lake build` green; `scripts/check_docstrings.py` as before (no docstring changed).

## Round 5 (2026-11-02): stale figures and "not yet" passages in ROADMAP

Audit findings docs-06, docs-08, docs-17, docs-18, docs-19 and docs-20, each reproduced by two
skeptics. Only `docs/ROADMAP.md` changed; no Lean, spec or docstring changed.

- **docs-06** (risk table, kernel perft memory). Already fixed before this round: the row now gives
  the pre-step-6 figures as such and the post-step-6 ones (39 s, 3.7 GB), and
  `docs/spec/ChessTest.Perft.md` §3 labels its measurements "before step 6" and "after step 6".
  Nothing to do.
- **docs-08** (`Checkmate foolsMate` in the kernel). §1 said 1.7 s, §3 item 6 and step 1 said
  about 3 s. Re-measured today (`theorem t_cm : Checkmate foolsMate := by decide +kernel`,
  importing `ChessTest.Rules` and `Chess.MoveGen`, `lake env lean` under `/usr/bin/time -l`):
  type checking 0.77 s, 0.66 GB maximum resident set size. Each passage now gives about 0.8 s and
  labels the older figure with when it was measured.
- **docs-17.** Step 5's "there is no such README yet" gains "(done in step 7: `scripts/README.md`)";
  the risk row on slow FEN reads says `scripts/`, not "the future `scripts/`".
- **docs-18.** The `sq!e4` owner decision no longer says it blocks step 3 (done without it); it
  blocks no step and is optional, for readable tests.
- **docs-19.** §3 item 1's "56-line cover lemma" was the review appendix's draft. The landed
  `PseudoLegal.mem_candidates` is about 25 lines with its docstring, about 45 with its three helpers
  (`Chess/MoveGen.lean`, section `Completeness`). The §1 table's Rules row now names R3
  (`reaches_symm`, `reaches_pawn_symm`, `Board.attackedBy_iff_superpiece`, in `Chess/Rules/Laws.lean`)
  and its MoveGen row names the completeness results (cover, M2, M4, M6, the generator-backed
  instances) and `kingSafeAfter`/`kingSafeAfter_iff`.
- **docs-20.** The docstring half was already fixed (the eight instance docstrings of Basic are
  quoted in full, and `scripts/check_docstrings.py` reports no missing docstring; re-run today). The
  review half: ROADMAP said every module has `docs/reviews/<Module>.md`. It now says the six
  original modules and `Chess.Spec.Winning` do, `Chess.ChessGame.Fide` is reviewed inside
  `docs/reviews/Spec.Winning.md`, and `Chess.Puzzles` has no review yet.

**Checks.** `lake build` green; `scripts/check_docstrings.py` reports nothing missing.

## Round 6 (2026-11-02): DESIGN's parser, promotion and en passant passages; the Stage 2 filter

Audit findings gotham-2, notation-3, notation-4, fide-1 and fide-2 (each low, each reproduced by two
skeptics). Changed: `docs/DESIGN.md`, `docs/THEOREMS.md`, `docs/ROADMAP.md`; the spec side
(notation-1, notation-4) is in `docs/process/ChessGame.md` Round 8. No Lean changed.

- **gotham-2** (THEOREMS §1 said `WinsIn .white 11`). Already fixed by Round 2 of this log: §1 reads
  `Chess.OnlyWinningMove gotham (uci "b7b2") ∧ Chess.WinsIn .black 11 gotham`. §7's plan text
  (`MateIn .white 11 gotham`) stays under its dated note, as Round 4 decided. Nothing to do.
- **fide-2.** DESIGN §4.4 and §5.4 cited promotion as FIDE 3.7.5; the pinned 2023 Laws (Basic spec)
  number it 3.7.3.3, as the Lean does. Both changed.
- **fide-1.** DESIGN §5.4 said a hand-written en passant target "cannot produce a capture FIDE
  forbids". False (Rules review C7; a stale target, or one no legal double push explains, still
  allows the capture). Replaced by the Rules spec D4.5 wording, plus a sentence that the FEN target
  is trusted as history and checked only for its rank.
- **notation-3.** DESIGN §6.4 named two sanity rejections, §6.5's table said `parseFEN` "rejects the
  two cases of Section 6.4", and §8.6 said it reads "the two clock fields" and rejects "a string
  that is not valid FEN". Now: canonical FEN only, four or six fields, clocks as two numerals not
  read (so a move number of `0` is accepted), and the three conditions of `Position.Sane`.
- **notation-4.** THEOREMS M11's status line now says M11.1 also waits for an owner decision (review
  C4), with a string today's parser accepts that no `WellFormed` would. ROADMAP step 8 says not to
  change `parseFEN`'s filter until that decision, with evidence: the three strings of the finding are
  accepted (`#eval`), and of the 26 distinct FEN strings in the library's `.lean` files, the 18 that
  `parseFEN` accepts are all valid for python-chess 1.11.2 (`Board.is_valid()`). The decision is
  added to ROADMAP's open owner decisions.

**Checks.** `lake build` green; no docstring changed.

## Round 7 (2026-11-02): the final verification pass and `docs/VERIFICATION.md`

- **Clean builds, one at a time.** `rm -rf .lake/build`, then `lake build` (green, 20 jobs, 7.4 s,
  0.87 GB), `lake build ChessTest` (green, 32 jobs, 161 s, 3.5 GB), `lake build ChessDemo` (green,
  24 jobs, 165 s, 2.7 GB) and `lake build chess-perft` (green, 0.8 s).
- **Axioms.**
  - A `collectAxioms` scan over every declaration of the three libraries found only `propext`,
    `Classical.choice` and `Quot.sound`.
  - No library declares an axiom or an unsafe declaration. The only partial declarations are 10
    compiler-generated `_unsafe_rec` auxiliaries.
  - A kernel replay from `Init` accepted all 3 937 declarations (255 s, 4.2 GB). The two auxiliary
    recursors of `Cert` were excluded, as in the trust audit.
  - The ledgers passed in the builds: 144 + 8 + 16 axioms entries and 30 interface entries.
- **Counts.**
  - Source `theorem` declarations: `Chess` 415, `ChessTest` 9, `ChessDemo` 370.
  - `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` and
    `partial`: 0 in every library (comments excluded).
- **Regression checks after the fix rounds.**
  - 337 `perft_diff` jobs against python-chess: 0 disagreements.
  - `gen_cert.py` regenerates `ChessDemo/GothamCert.lean` byte for byte.
  - `scripts/check_docstrings.py`: 0 definitions missing.
- **Docs.**
  - New `docs/VERIFICATION.md`: the night's report.
  - README: the status paragraph now gives these figures and a link to the report, and the file
    map has a row for it.
  - ROADMAP §0: the three build rows now give the final-pass figures.
  - No Lean file changed in this round.
