# Roadmap for `Chess`

Author role: library reviewer. Date: 2026-11-01, updated through 2026-11-03 (§0 and steps 7b, 8). Read for this document: all of `Chess/*.lean`,
`Chess.lean`, `docs/THEOREMS.md`, `docs/DESIGN.md`, and the specs, process logs, reviews and research
under `docs/`. This file summarizes where the library stands and what to do next. Where it disagrees
with an older document, the code is the reference, and this file says which document is stale.

---

## 0. Status at a glance

| Check | Result |
|---|---|
| `lake build` (clean, Lean 4.28.0, core only) | **green**, 20 jobs; **7.4 s** from clean, peak 0.87 GB, in the final pass of 2026-11-02 (`docs/VERIFICATION.md`), after the fix rounds. Earlier: 17 jobs; **8.7 s** from clean after steps 6–7 (`rm -rf .lake/build`, wall clock with parallel jobs, 14 s of CPU, peak 0.84 GB; 2026-11-02). Step 5 had measured 7.7 s, step 3 about 8 s (36.3 s before step 3, on the same machine). |
| `lake build ChessTest` (not a default target) | **green**: the moved tests, the perft suite, the axioms ledger, the interface ledger. **161 s** and 3.5 GB in the final pass (32 jobs). Earlier: **160 s** after a clean library build, peak 3.7 GB (after step 6; `ChessTest.Perft` 39 s and `ChessTest.PerftDeep` 119 s, against 276 s and 265 s before it: the king-safety change of step 6 speeds up the generator in the kernel and in the interpreter). Before step 6: about 9 minutes, 4.8 GB. |
| `sorry` / `admit` | **0** |
| `TARGET` markers | **0**. [later] lemmas are kept in the specs, not as `sorry` stubs in the Lean. |
| `axiom` declarations, `native_decide`, `partial`, `unsafe` | **0** |
| `#print axioms` | Checked on every build of `ChessTest` for 152 headline theorems (`ChessTest/Axioms.lean`, 144, and `ChessTest/AxiomsPerft.lean`, the 8 kernel perft counts; since the ledger-coverage fix of 2026-11-02 every theorem and instance named in a `Chess/` module's Main statements is among them, checked by a scripted name comparison, not by the build), and on every build of `ChessDemo` for its 16 theorems (`ChessDemo/Axioms.lean`): all [kernel], none beyond `propext`, `Classical.choice`, `Quot.sound`. |
| `lake build ChessDemoBound` (not a default target, 2026-11-03) | **green**: mate in exactly 11 for Gotham (`gotham_mateIn`, `gotham_specMateIn`), from the generated lower-bound certificate `ChessDemoBound/Gotham10` (24,994 node theorems), and two small generated test certificates. About 45 min on 10 cores, under 1 GB per process (`docs/research/minimality.md`). Its 3 headline theorems and the 2 tests have their axioms checked by `#guard_msgs`. |
| `lake build ChessDemo` (not a default target, since step 7) | **green**: the Gotham demonstration and small mates. **165 s** and 2.7 GB in the final pass (24 jobs). Earlier: **162 s** after a clean library build, peak 2.8 GB (`GothamCert` 160 s and 1.1 GB alone; `Mates` 19 s). No `native_decide`. |
| Generated-file interface | Since step 5: the names a generated certificate file may use (Game spec §4.3) have their signatures recorded by `ChessTest/Interface.lean` (`#guard_msgs` over `#check`/`#print`): 25 at step 5, 30 since step 7 (the only-move root glue and `mem_chess_moves`), 41 since 2026-11-03 (the C9 lower-bound glue and `Forces.mono`, used by `ChessDemoBound/Gotham10`). The first generated file, `ChessDemo/GothamCert.lean`, uses only these. |
| Size | 17 files in `Chess/` since the readability round (`Chess.Game` is an umbrella over five files since step 5, `Chess.Rules` over three since the readability round; about 6 000 lines, about 400 `theorem` declarations); about 215 `example`/`#guard` tests, about two thirds of them in `ChessTest`, plus the 152 entries of the axioms ledger, the 30 of the interface ledger and the 16 of the demo ledger |

Every definition in `Chess/` has a docstring that appears word for word in its `docs/spec/<Module>.md`
(checked by `scripts/check_docstrings.py` since the readability round; before it, eight instance
docstrings of `Basic` were abbreviated in its spec, and no checker was in the repository).
Lemma docstrings follow two documented exceptions, and no other: where a spec table cell groups
several lemmas, each lemma's docstring is the part of the cell's sentence about it, reworded to
stand alone (Basic spec §0; 67 lemmas of `Basic`), and in `Game` a leading tag such as "(G3)"
becomes a trailing "THEOREMS G3." (Game spec §0; 26 lemmas on 2026-11-02, 37 since the C9 lemmas and their tests of 2026-11-03). Every lemma alone in its table cell
has its English column as its docstring, word for word, after the `Game` tag rule (checked by
script on 2026-11-02).
Each module went through four rounds: English spec, critique, Lean translation, critique of the Lean
and revision of the English. Each round is logged in `docs/process/<Module>.md`. The six original
modules and `Chess.Spec.Winning` each have a file-level review in `docs/reviews/<Module>.md`;
`Chess.ChessGame.Fide` is reviewed inside `docs/reviews/Spec.Winning.md`, and `Chess.Puzzles` has
no review yet.

**Fixed in this review (trivial, comment and spec only).** `Chess/Basic.lean` and
`Chess/Position.lean` labelled the piece letters, square names, `Move.toUCI` and
`CastlingRights.letters` as "Display (untrusted: nothing in the specification reads it)". That was
false: the FEN/UCI guards of `ChessGame` compare against exactly these functions, so they are part
of what `fen "…"` and `uci "…"` mean. They are now under "Notation (trusted: …)". `Color.name` moved
down into a separate "Display (untrusted)" section in `Position`, together with the diagrams.
`docs/spec/Basic.md` §8 and `docs/spec/Position.md` §6 and choice 13 now say the same
(ChessGame review C1). No declaration or docstring changed. The build is still green.

---

## 1. What exists now

```
Basic ──► Position ──► Rules ──► MoveGen ──┐
  │                      │                  ├──► ChessGame ──┬──► ChessGame/Fide
  └──► Game ─────────────┼──────────────────┘                │        ▲
                         └──► Spec/Winning ──────────────────┼────────┘
                                                              └──► Puzzles
```

(`ChessDemo`, steps 6–7, imports `ChessGame/Fide` and `Puzzles`; nothing imports it.
`Spec/Winning` and `ChessGame/Fide` were added on 2026-11-02 for G8, step 2 of §5. Step 3 added
the test library `ChessTest` beside these, which imports them and which nothing imports, and the
program `chess-perft`. Step 5 split `Game` into `Game/Defs → Game/Laws → {Game/Search, Game/Cert}
→ Game/Examples` under the umbrella `Chess/Game.lean`, and added `Puzzles`.)

| Module | What it is | Headline content |
|---|---|---|
| `Chess.Basic` | Finite vocabulary and board geometry | `Square` as two `Fin 8`. One geometric primitive, `Square.offset`, with one characterizing lemma (`offset_eq_some_iff`). Every proof goes through it and ends with `omega`. Shifts, rays, knight jumps, relative ranks, castling squares. R1 and R2. |
| `Chess.Position` | Data of the move layer | `Board := Square → Option Piece` with `set` as its only writer. `Board.pack`/`unpack` (hex-nibble `Nat` literals for kernel checkpoints, `unpack_pack`). `Move` in UCI form. `CastlingRights` as four flags behind `get` (a move changes them through `CastlingRights.ofGet`). `Position` (no clocks, no history). |
| `Chess.Rules` | **The trusted FIDE specification** | `Reaches`/`Slides` (geometry that reads only squares strictly between), `AttackedBy`, `InCheck`. Six named rule predicates joined into `PseudoLegal`. `Position.play` as six named steps over write lists. `Legal`, `Checkmate`, `Stalemate`. Frame lemmas (R4), R5, R8, R11. R3 (step 6: `reaches_symm`, `reaches_pawn_symm`, `Board.attackedBy_iff_superpiece`). L4.11 (`CastleMove.legal_iff`): castling's landing-square test after the move agrees with FIDE's test before it. |
| `Chess.MoveGen` | Executable generator | **Propose and dispose**: geometry proposes `candidates`, and the generator keeps those that `PseudoLegal`/`Legal` accept. Soundness (`legalMoves_sound`) is one line. Completeness (step 1): the cover `PseudoLegal.mem_candidates`, M2 (`mem_pseudoMoves`), M4 (`legalMoves_complete`, `mem_legalMoves`), M6 (`checkmate_iff`, `stalemate_iff`) and the generator-backed `Checkmate`/`Stalemate` instances. King safety by the Boolean `kingSafeAfter`, proved equal to `Legal`'s test (`kingSafeAfter_iff`, step 6). M1 (`mem_slideTargets`, `mem_reachTargets`). Perft. A spec-only oracle `legalMovesBySpec` with `agreesWithLegal`, a Boolean test that becomes a per-position theorem. |
| `Chess.Game` | Abstract two-player game theory, chess-free; since step 5 five files under one umbrella | `Game/Defs` (the meaning for an abstract game; since G8, step 2, not in a chess headline's trusted base, unless the headline is read as `Chess.WinsIn` itself rather than through G8, DESIGN §7.3): `Forces a T n x` (three rules), `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`. `Game/Laws`: G2–G4, G6, O2, O8. `Game/Search`: a bounded search proved correct (`searchForces_iff`, so `Forces`/`MateIn` are decidable). `Game/Cert`: `Cert` and `OnlyMoveCert` with structural checkers, sound (C1), complete (C2), `checkOnlyMove_sound` (C7), per-node glue lemmas (C3), and the diagnostics `firstFailureWin`/`firstFailureOnlyMove`, proved to agree with the checkers; the frozen interface of generated files. `Game/Examples`: a toy take-away game exercises all of it. |
| `Chess.ChessGame` | Chess as a game, plus notation | `Game.chess` (moves = `legalMoves`, mated = in check with no listed move). `Chess.WinsIn`/`Wins`/`MateIn`/`OnlyWinningMove`. `fen "…"` and `uci "…"` take a proof argument that is discharged automatically. The parsers are untrusted: their meaning is pinned by `fen_eq_iff` and `uci_eq_iff` against the trusted writers and `IsFEN`/`Position.Sane`. A round trip is proved for every position (`readFEN_toFEN`). |
| `Chess.Spec.Winning` | **Trusted** winning, from the rules alone (G8) | `SpecForces` (the three rules of `Game.Forces`, with `Legal` and `Position.play`), `SpecWinsIn` (target: the defender to move and `Checkmate`), `SpecWins`, `SpecMateIn`, `SpecOnlyWinningMove`. Imports `Rules` only. Sanity: `specWinsIn_zero_iff`, `not_specWins_of_stalemate`, proved without the generator. |
| `ChessTest` (library, not a default target) | Tests, perft suite, axioms ledger (step 3) | `ChessTest/Rules`, `MoveGen`, `ChessGame`, `ChessGame/Fide`: the modules' former test sections, verbatim. `Tabulate`: `Position.tabulate` (a board read once into an array; `tabulate_eq`). `Perft`, `PerftDeep`: the six chessprogramming.org positions with published counts. `Axioms`, `AxiomsPerft`: `#guard_msgs` over `#print axioms` for 152 headline theorems (the perft ones apart, so the rest builds without the perft suite). `Interface` (step 5): the signatures of the generated-file interface. `Puzzles` (step 5): the tests of `Chess.Puzzles`. Program `chess-perft` (`ChessPerft.lean`): FEN and depth in, divide and perft out. |
| `ChessDemo` (library, not a default target) | The Stage 1 closing demonstration (steps 6–7) | `GothamCert` (generated by `scripts/gen_cert.py`: 319 per-node theorems, the `Cert`/`OnlyMoveCert` values), `Gotham` (`gotham_winsIn`, `gotham_onlyWinningMove`, their G8 readings `gotham_specWinsIn`, `gotham_specOnlyWinningMove`, `gotham_not_wins_white`, and the refutations behind the only move, `gotham_refuted` and its G8 reading `gotham_specRefuted`), `Mates` (exact `MateIn` 1 and 2 by search; 3 by a certificate for the win and a search for minimality), `Axioms`. Kernel only. |
| `Chess.Puzzles` | Named headline positions (step 5) | `Puzzles.gotham := fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"`, checked against the prototype and python-chess (34 legal moves; the `-` en passant field reads the same under this library's convention and Stockfish's). |
| `Chess.ChessGame.Fide` | G8, proofs only | `mem_chess_moves`, `chess_mated_iff_checkmate`, `forces_iff_specForces`, then `winsIn_iff_specWinsIn`, `wins_iff_specWins`, `mateIn_iff_specMateIn`, `onlyWinningMove_iff_specOnlyWinningMove`, from `mem_legalMoves` and `checkmate_iff` only. |

### Stage 1 (★) milestone, item by item (THEOREMS §7)

| ID | Status | Lean name(s) |
|---|---|---|
| R1 | done | `Square.ofIndex_index`, `Square.index_ofIndex` |
| R2 | done | `mem_all`/`all_nodup` for every finite type; whole-type quantifiers at `priority := low` |
| R4 | done | `play_board_of_not_mem`, `play_board_src/dst/epVictim/rookHome/rookCastleSquare`, `play_turn` |
| R5 | done | `PseudoLegal.isLight_dst_iff_of_bishop`, `…_of_knight` |
| R11 | done | `checkmate_or_stalemate`, `not_checkmate_and_stalemate` |
| L4.11 (Rules fidelity, not a THEOREMS item) | done (2026-11-02) | `CastleMove.legal_iff`: castling's landing square read as FIDE 3.8.2.2 says, before the move |
| M7 | done (2026-11-02) | `ChessTest/Perft.lean`: the six standard positions, depth 1 of all and depth 2 of two in the kernel (`perft_initial_1`, … , `perft_position6_1`), depths 2–4 by `#guard`; 17 regression positions with `agreesWithLegal` in `ChessTest/MoveGen.lean`. Differential test against python-chess in `docs/process/ChessTest.md`. |
| G1 | done | `Game`, `Game.chess` |
| G2, G3, G4, G6 | done | `winsIn_zero_iff`, `not_wins_of_stalemate`, `Forces.mono`, `WinsIn.not_both`, `Wins.not_both`, `MateIn.unique`, `Wins.exists_mateIn` |
| G5 | done | `searchForces_iff` (THEOREMS still calls it `searchWin_iff`) |
| C1, C2, C3, C7 | done | `checkWin_sound`, `checkWin_complete`, `Forces.move_of_play_eq`/`replies_of_moves_eq`/`of_play_eq`, `WinsIn.of_mated` (step 5), `checkOnlyMove_sound` (with an `OnlyMoveCert` since step 5) |
| O2 | done | `OnlyWinningMove.wins_iff`, `.unique`, `.of_refuted`, `.winsIn_play` |
| O8 (bonus) | done | `Forces.trans` |
| **Closing demo** | **done** (2026-11-02, steps 6–7); the trusted file under the G8 readings, `Spec/Winning`, and `ChessGame/Fide` were reviewed independently on 2026-11-02 (`docs/reviews/G8_REVIEW.md`: no soundness defect) | `ChessDemo.gotham_winsIn : WinsIn .black 11 Puzzles.gotham`, `ChessDemo.gotham_onlyWinningMove : OnlyWinningMove Puzzles.gotham (uci "b7b2")`, and through G8 `gotham_specWinsIn`, `gotham_specOnlyWinningMove`; the refutations behind the only move (a forced mate for White after each other move), `gotham_refuted` and `gotham_specRefuted`; [kernel], standard axioms only (`ChessDemo/Axioms.lean`). Exact `MateIn`: `ChessDemo.foolsMate_mateIn` (1) and `rookMate2_mateIn` (2) by search, `rookMate3_mateIn` (3) by a certificate for the win (`rookMate3_winsIn`) and a search for minimality (`rookMate3_not_winsIn_two`). |
| R3 (Stage 2, brought forward) | done (2026-11-02, step 6) | `reaches_symm`, `reaches_pawn_symm`, `Board.attackedBy_iff_superpiece` |

Stage 2 items already reached: M1 (target lists), M2, M4 (both halves), M6 and **G8** (step 2
below, 2026-11-02), so the **Stage 2 headline (M4 + G8) is reached**. **Update: step 1
below has landed** (section `Completeness` of `Chess/MoveGen.lean`: `PseudoLegal.mem_candidates`,
`mem_pseudoMoves`, `legalMoves_complete`, `mem_legalMoves`, `checkmate_iff`, `stalemate_iff`, and
the generator-backed `Checkmate`/`Stalemate` instances; `decide +kernel` proves
`Checkmate foolsMate` in about 0.8 s, 0.66 GB, re-measured 2026-11-02 after steps 6–7 and the readability round; about 1.7 s when step 1 landed). Original note: The 56-line cover proof in `docs/reviews/MoveGen.md` (Appendix) elaborates against
today's build in about 2 s, with standard axioms only. I re-checked it in a scratch file for this
review and added `stalemate_iff` the same way. See step 1.

---

## 2. How faithfully English and Lean match

**Method.** Each definition is written in English first, then translated. The Lean docstring is
the English sentence, verbatim. A reader can check FIDE against the English, and the English
against the Lean, one definition at a time. The process logs show this loop catching real
problems. Examples: castling candidates needed a king-on-home guard, or a queen on e1 would propose
e1g1 twice. The derived `CastleMove` instance was 80× slower than a hand-guarded one. Bounded
quantifiers were being decided by sweeping the whole type until the low-priority fix (Basic
review C1).

**Assessment by module.**

- `Basic`, `Position`: faithful by construction. Each notion is a small total function or structure
  with a characterizing lemma. Nothing to flag.
- `Rules`: faithful, with three readings a chess player should know about:
  1. **Castling's landing square is tested after the move, through `Legal`, not before it as FIDE
     3.8.2.2 literally says.** `CanCastle` tests the right, the rook, the empty squares between, "not
     in check" and "crossed square not attacked". The landing square falls to `Legal`'s
     king-safety test on the board after castling. Since step 4 (2026-11-02) the two readings are
     proved to agree: `CastleMove.legal_iff` (spec L4.11), on every board, with no one-king
     hypothesis. So this is no longer a gap in the trusted text, only a choice of how to say the
     rule, with a theorem saying it means FIDE's sentence.
  2. **En passant target convention.** `play` sets `epTarget` after every double push, whether or
     not a capture is possible. This is the PGN convention, not Stockfish's or Lichess's. Two
     positions that FIDE 9.2.3 counts as identical can therefore differ as `Position` values. This
     is harmless for `WinsIn`. It matters for repetition (Stage 4, G16 `normalize`) and for any FEN
     copied from Stockfish or Lichess right after a double push (ChessGame review C6).
  3. `Reaches` deliberately ignores pins and what stands on the source square (FIDE 3.9.1: check is
     geometric). `EnPassantMove` adds plausibility conditions (target on the sixth rank, the
     victim's origin square empty). They are implied in any reachable position, and they make
     arbitrary FEN input safe.
- `MoveGen`: before step 1, `legalMoves` was the one trusted claim of the library: "available" in
  `Game.chess` meant "listed by `legalMoves`", so every `Chess.WinsIn` statement was about
  *generator chess*. Step 1 proved completeness (M4), and G8 removed `Game.chess` from the reading
  of a headline (`Chess/ChessGame/Fide.lean`), so this gap is closed.
- `Game`: the definitions say what the English says, including the two traps that most
  formalizations fall into. A stalemated defender has not lost (the `replies` rule demands a move),
  and budgets count attacker moves only, the mating move included. `MateIn` is "exactly n".
  `OnlyWinningMove` counts a slow win by another move, or a different promotion piece, as another
  winning move, so it is a demanding notion.
- `ChessGame`: the best-guarded layer. Readers propose, writers dispose, and `fen_eq_iff`/`uci_eq_iff`
  state the meaning. **Things a headline reader must know:** clocks in a FEN are parsed and ignored,
  so `WinsIn` is a G∞ claim that may still be a 50/75-move draw (G15). `Position.Sane` checks
  only one king per side, the side not to move not in check, and the ep-target rank. It accepts
  unreachable positions (pawns on the back rank, castling rights with no rook). That is harmless
  for `WinsIn`, because the rules re-check everything, but it is not `WellFormed`.

**Trusted base for a chess headline today (after steps 1 and 2):** the kernel; the English and Lean
of `Basic`, `Position`, the definitions of `Rules` (`Chess/Rules/Defs.lean` alone, since the
readability round) and `Spec/Winning` (five definitions, about 45 lines with docstrings); and the
notation of `ChessGame`: the writers, `IsNumeral`, `ClockFields`, `IsFEN`,
`Position.Sane`, and the statements of `fen_eq_iff` and `uci_eq_iff`; and the definitions in
`Chess.Puzzles` of the named positions a headline mentions (one FEN string each, such as
`Puzzles.gotham`, since step 5). A headline
`WinsIn a n (fen "…")` or `OnlyWinningMove (fen "…") (uci "…")` is read as `SpecWinsIn` or
`SpecOnlyWinningMove` through the proved equivalences of `ChessGame/Fide`. `MoveGen`, the section
"Games" of `Game`, `Game.chess` and the four abbreviations are no longer in the trusted base.
(Before step 1, `legalMoves` was the meaning of "legal"; before step 2, `Game`'s definitions,
`Game.chess` and the abbreviations were trusted.) Caveats that remain: FIDE's draw rules are absent
(clocks ignored, G15), and `Position.Sane` admits unreachable positions.

---

## 3. The design decisions that matter most

1. **Spec and implementation are separate, and the implementation only filters.** `legalMoves` never
   re-implements a rule. It filters geometric candidates by the `Rules` predicates. This is why
   soundness is one line and completeness rests on a cover lemma of about 25 lines (about 45 with its
   three helpers, docstrings included) with no pin or check reasoning.
   Keep this pattern for the bitboard layer. A fast generator should also be linked by a refinement
   or membership theorem, never trusted.
2. **`Board` is a function, `Square` is two `Fin 8`.** The result is the most readable statements
   and proofs (`set_ne` frame rewrites, `omega` geometry), paid for in speed (§4). The prototype's
   nibble `Nat` survives only as `Board.unpack` checkpoint literals, proved equal (`unpack_pack`).
   A function board must never be the result of a `Board`-valued `if`/`match`: compiled code then
   re-evaluates the condition on every square read and becomes exponential (Position review C1).
   `play` follows this rule by building lists of writes and applying them once with
   `Board.setMany`.
3. **`PseudoLegal` is six named decidable predicates joined by `∨`, with shared shape predicates**
   (`IsEnPassant`, `IsCastle`, `IsDoublePush`) used by both the rules and `play`. One FIDE clause
   maps to one Lean conjunct. The cost: proofs destructure with positional `rcases` patterns. Rules
   review C1 proposes Prop-valued structures with named fields. Decide this before more proofs
   (M5, invariants) depend on conjunct order. **Decided in step 4: not adopted** (Rules spec design
   choice 14 has the reasons); the six rules stay conjunctions.
4. **The game semantics are inductive (`Forces`), and the search and certificates are executable
   Booleans proved against it.** The trusted part is three inference rules. Everything Stockfish
   produces lands as a `Cert` (data) checked by `checkForces`, whose soundness theorem is the only
   bridge. No engine number ever appears in a statement.
5. **No clocks or history in `Position`.** `WinsIn` lives in the game without draw rules (G∞).
   The FIDE game with clocks is planned as a second `Game` instance on the same states (G12–G15),
   not as an edit to this one.
6. **`Game.chess.Mated` is executable** (`InCheck p ∧ legalMoves p = []`). Kernel-checking
   `Checkmate` through `Legal` directly over 20 480 candidate moves did not finish in 500 s; through
   the generator `Checkmate foolsMate` takes about 0.8 s (re-measured 2026-11-02; about 3 s before
   step 6). G8 bridges the two.
7. **Notation is proved, not trusted.** `fen`/`uci` carry their parse proof, and the parsers are
   characterized by `iff` lemmas. Copy this pattern for any future input format (PGN, EPD, Syzygy
   probes).
8. **Budgets are counted at the claim's state, attacker moves only.** The only-move checker uses
   the same convention (`WinsIn .black 11 gotham`, with no off-by-one).

---

## 4. Risks

| Risk | Severity | Evidence | Mitigation |
|---|---|---|---|
| ~~Kernel cost per certificate node~~ **Reduced in step 6** (2026-11-02): mate leaves and defender nodes 2.0 s → 0.7 s, attacker nodes 0.1 s by `Legal`; the 319-node Gotham certificate checks in 165 s and 1.1 GB. Still about 2× the prototype's time (its packed `Nat` board), for a fifth of its memory. | low-medium | `docs/process/MoveGen.md` Round 5, `docs/spec/ChessDemo.GothamCert.md` §3 | What is left of a node is mostly `pseudoMoves` (Rules' `PseudoLegal` instance per candidate). Certificates ten times larger would want the bitboard layer (step 10b) or a faster `PseudoLegal` decision proved equal. |
| ~~The Stage 1 demonstration has not been attempted~~ **Done in step 7** (2026-11-02) | — | `ChessDemo/` | — |
| **Search in the kernel is memory-hungry.** `decide` on `WinsIn`/`MateIn` through `searchForces` keeps every evaluated position: a mate in 2 whose search visits about 300 defender nodes took 7.2 GB and 408 s; a mate in 3 visiting 184 took 5.9 GB. | medium (for "exact `MateIn`" claims) | `docs/spec/ChessDemo.Mates.md` §3 | Prove the win by a certificate and only the minimality (`¬ WinsIn (n-1)`) by search (`mateIn_succ_iff`); choose positions with a cost model. A per-node survival certificate (C4, step 9) would replace the search for minimality: done for Gotham on 2026-11-03 (step 7b, C9 glue, 45 min of build for mate in exactly 11). |
| ~~Tests live inside library modules~~ **Resolved by step 3** (2026-11-02): the clean library build went from 36.3 s to 8.1 s. | — | ChessGame review C3, MoveGen review C4 | Keep new tests in `ChessTest`; keep only cheap `#guard`s in library modules. |
| **A board read from a FEN is slow to read in compiled and interpreted code.** The code for `readBoard cs` re-reads the FEN text at every square read (profiled: the time of an untabulated perft is in `splitOn`, `readBoard`, `Piece.ofLetter?`). Compiled perft 3 of the initial position read from its FEN: 10.9 s, against 0.38 s tabulated. Any untrusted tool that runs the generator on `fen "…"` or `parseFEN` output (`scripts/`, `firstFailure`) meets it. Not seen in the kernel to the same degree (Kiwipete perft 1: 4.7 s via `fen`, 3.9 s via a packed literal). | medium | `docs/process/ChessTest.md` | Use `Position.tabulate` (`ChessTest/Tabulate.lean`, proved equal), or move it into `Chess.Position` with its lemma, or make `readBoard` build its board from a computed array, which changes untrusted reader code and its proofs (`readBoard_fenChars`). Owner's choice. |
| Test-library memory. Before step 6, kernel perft at depth 2 cost 3.9–6.6 GB per position, `ChessTest.Perft` peaked near 5 GB, and, under swap pressure from other processes, depth 2 of Position 5 did not finish in 10 minutes. Since step 6 (re-measured 2026-11-02): `ChessTest.Perft` takes 39 s with a 3.7 GB peak; depth 2 of the initial position 9.8 s, of Position 3 5.6 s; depth 2 of Positions 4, 5, 6 and Kiwipete not re-measured. | low | `docs/spec/ChessTest.Perft.md` §3 | Kernel depth 2 kept only where it costs at most 4 GB; deeper counts by `#guard` and by the compiled program. |
| Positional `rcases` over the six rules is brittle under any change to rule conjuncts | low | Rules review C1, MoveGen review C1 | Decided in step 4: the rules stay conjunctions (Rules spec design choice 14). A break shows at build time, never silently. Revisit if L4.6 (M5) is painful; the migration can go rule by rule. |
| ~~L4.11 (castling landing square) unproved inside trusted text~~ **Resolved by step 4** (2026-11-02): `CastleMove.legal_iff`. | — | Rules spec §7a | — |
| Document drift: THEOREMS.md still uses pre-design names (`searchWin`, `Reach`, `Cert.mate`, `Chess.game`; "exactly 11" for Gotham was drift until 2026-11-03, when it was proved). | low-medium | DESIGN §12 lists the edits | The theorem architect applies DESIGN §12. The name map in §7 below covers the gap until then. Applied so far (2026-11-02, docs fix round, `docs/process/Chess.md`): §1's headline and goal sentence, C7's conclusion, the G1 binders and the G2 `not_wins_of_stalemate` signature, C3's glue list, status lines for M2, M4 and M6, the M3 entry of the dependency map, and M7's timing. |
| ~~`Game.lean` is 748 lines~~ **Resolved by step 5** (2026-11-02): split into `Game/Defs` (the trusted part, 130 lines), `Laws`, `Search`, `Cert`, `Examples`. | — | Game review C2 | — |
| ~~`Rules.lean` interleaves its 37 trusted definitions with about 700 lines of lemmas~~ (`Legal`, `Checkmate`, `Stalemate` at lines 820–841 of 1280) **Resolved by the readability round** (2026-11-02): split into `Rules/Defs` (definitions and instances only, 396 lines), `Laws`, `Castling`. | — | Rules spec design choice 15 | — |
| `OnlyWinningMove` can only be certified when every alternative *loses* | known limit | Game spec, `checkOnlyMove` docstring | Stage 3 trap (draw) certificates (step 9). |
| Python-chess FEN default drops ep targets that no pawn can use, which breaks checkpoint equality after double pushes | low, and no longer silent | DESIGN §7.4 | Handled in step 7: `scripts/gen_cert.py` computes the target itself after every double push, and `chess-perft` reads back unchanged the FEN of every position whose moves it lists; a wrong checkpoint fails the build (each `p.play m = q` is decided by the kernel). |

---

## 5. Next steps, ordered toward the THEOREMS milestones

Each step goes through the same loop as the existing modules: English spec, then critique, then
Lean, then critique, then a file review. Steps 1–7 close **Stage 1**, and on the way steps 1–2
deliver the **Stage 2 headline** (M4 and G8). Step 8 completes Stage 2, and steps 9–10 open
Stages 3–5.

1. ✅ **(Done.) Land generator completeness (M4, M6; THEOREMS ★★).** Add a section `Completeness` to
   `Chess/MoveGen.lean` with `PseudoLegal.mem_candidates` (the cover), `mem_pseudoMoves`,
   `mem_legalMoves`, `checkmate_iff` and `stalemate_iff`, from the MoveGen review appendix
   (verified against today's build). Use `CastleMove.eq_castle` in the castling bullet. Register
   `Checkmate.decidable` through `checkmate_iff` (about 3 s in the kernel at the time instead of more
   than 500 s; about 0.8 s since step 6). Restore the plain docstrings ("the legal moves of `p`"), and drop "trusted until M4"
   from DESIGN §3 and §7.3 and from the module header. Effect: `Chess.WinsIn` is about FIDE-legal
   moves from Stage 1 on.
2. ✅ **(Done, 2026-11-02.) G8 in its own files (Stage 2 headline, now cheap).**
   `Chess/Spec/Winning.lean` (imports `Rules` only) defines `SpecForces`/`SpecWinsIn`/
   `SpecOnlyWinningMove` from `Legal`, `play` and `Checkmate`. `Chess/ChessGame/Fide.lean` proves
   `Chess.WinsIn a n p ↔ SpecWinsIn a n p` and the same for the only-move notion, from
   `mem_legalMoves` and `checkmate_iff`. After this, a headline reader's trusted base is `Rules`
   plus `Spec/Winning` plus notation; `MoveGen` and `Game` are no longer trusted (ChessGame review
   C2).
   **What landed.** `Chess/Spec/Winning.lean` (imports `Chess.Rules` only): `SpecForces`,
   `SpecWinsIn`, `SpecWins`, `SpecMateIn`, `SpecOnlyWinningMove`, and the sanity lemmas
   `specWinsIn_zero_iff`, `not_specWins_of_stalemate`. `Chess/ChessGame/Fide.lean`:
   `mem_chess_moves`, `chess_mated_iff_checkmate`, `forces_iff_specForces`, `winsIn_iff_specWinsIn`,
   `wins_iff_specWins`, `mateIn_iff_specMateIn`, `onlyWinningMove_iff_specOnlyWinningMove`, all with
   standard axioms only, plus two tests (a certificate carried to `SpecWinsIn`; a stalemate that is
   no `SpecWins`). Specs `docs/spec/Spec.Winning.md`, `docs/spec/ChessGame.Fide.md`; process logs of
   the same names; ChessGame spec §7 and open item 2, ChessGame's implementation notes, DESIGN §1,
   §3, §6.4, §7.3, §8 and THEOREMS G8 updated. ChessGame review C2 is carried out as recommended
   (with no `MoveGen/Correct` file, since M4 lives in `MoveGen`). Not done: no file review
   (`docs/reviews/`) for the two new modules yet; it is scheduled at the start of step 7.
   **Found on the way** (whole-library docstring check, `docs/process/ChessGame.Fide.md`): the
   `candidates` docstring in `MoveGen` kept a fragment of its pre-M4 wording; repaired to the spec's
   text. The §0 claim "every definition … word for word" holds except for the thirteen
   test-position `def`s of `Rules` (the spec describes them instead of quoting them); 98 lemma
   docstrings of `Basic` and `Game` are paraphrased in their specs' tables. Left for the owner.
   (Fixed in step 3: Rules §10 now quotes the thirteen test-position docstrings word for word.
   Update, 2026-11-02: `Game` now follows its spec's tag convention exactly, and the remaining
   `Basic` differences are the 67 grouped-cell lemmas that Basic spec §0 describes; the four
   single-lemma cells that differed were brought into line. See the paragraph after the status
   table.)
3. ✅ **(Done, 2026-11-02.) Test library and M7.** Create `ChessTest` (second `lean_lib`, not a
   default target). Move the `## Tests` sections there and keep only cheap `#guard`s as
   documentation in the modules. Add the six standard perft positions (chessprogramming.org) at
   depths 1–2 in the kernel, deeper by `#eval`/`#guard` (time compiled `perft 3`/`perft 4` first),
   plus the two bug-class positions of DESIGN §8.4. Add a `#print axioms` ledger file for every
   headline theorem, so that trust labels are checked, not claimed.
   **What landed** (details and every measurement in `docs/process/ChessTest.md`).
   - `lakefile.toml`: `lean_lib ChessTest` (not default) and `lean_exe chess-perft`.
   - The tests of `Rules`, `MoveGen`, `ChessGame` and `ChessGame/Fide` moved verbatim to
     `ChessTest/<same name>.lean`; each module keeps a few cheap `#guard`s. `Basic`, `Position` and
     `Game` keep their tests (1.7 s, 0.14 s, 0.05 s). Clean `lake build`: **36.3 s → 8.1 s**.
   - `ChessTest/Perft.lean`: the six positions (`Position.initial`, `Perft.kiwipete`,
     `Perft.position3` … `Perft.position6`, by `fen`); eight [kernel] theorems (depth 1 for all
     six, depth 2 for the initial position and Position 3); `#guard`s at depth 2 for the other
     four and depth 3 for three. `ChessTest/PerftDeep.lean`: depth 3 of Kiwipete and Positions 5
     and 6, depth 4 of Position 3 (`#guard`, 4.4 minutes then; about 2 to 2.5 minutes after
     step 6). No `native_decide`.
   - `ChessTest/Tabulate.lean`: `Position.tabulate` and `tabulate_eq` (see §4, the FEN-board risk).
   - `ChessTest/Axioms.lean`: 118 `#guard_msgs`-checked `#print axioms` entries, and
     `ChessTest/AxiomsPerft.lean` 8 more for the kernel perft counts; all 126 [kernel].
   - `ChessPerft.lean`: `chess-perft <FEN> <depth>` prints the FEN as read, the divide and perft.
     `scripts/perft_jobs.py` and `scripts/perft_diff.py` run it against python-chess.
   - Differential test against python-chess 1.11.2, all agreeing: the six positions (and Position 4
     mirrored) to depth 4, the initial position and Position 3 to depth 5 (all equal to the
     published counts), 200 random positions to depth 2, 300 more (random, just after a double
     push, castling or promotion available) to depth 3, and the 16 named test positions to depth 3:
     546 jobs, about 26 million leaves, every move's divide count equal, and every FEN written
     back equal to python-chess's.
   - The bug-class positions of DESIGN §8.4 were already named test positions (`promoPos`,
     `promoKnightPos`, `epPinPos`, `epCheckPos`, `pinPos`); they moved with the tests and also
     agree with python-chess to depth 3.
   **Not done.** Kernel depth 2 for Kiwipete and Positions 4–6 (memory: 6.6 GB for Position 4;
   Position 5 did not finish in 10 minutes on this machine, which was swapping). `readBoard` is
   not fixed and `Position.tabulate` stays in the test library (owner's choice, §4). No `lake test`
   driver. No file review of the test library.
   **Review fixes** (Round 2, `docs/process/ChessTest.md`): `chess-perft` searches once (it ran
   perft twice; every compiled time was re-measured and is about half the Round 1 figure); the
   ledger is split so that `ChessTest.Axioms` builds without the perft suite, and `slides_symm` is
   added (126 entries); `perft_jobs.py` regenerates every job file; the differential test was
   rerun in full, all 546 jobs agreeing.
4. ✅ **(Done, 2026-11-02.) Prove L4.11:** `CastleMove p w m → (Legal p m ↔ ¬ p.board.AttackedBy
   p.turn.other (kingCastleSquare p.turn w))`, by `reaches_congr` plus edge-square arithmetic (Rules
   review C2). This closes the one place the Rules spec flagged (D4.6 note) where the Lean does
   not say literally what FIDE 3.8.2.2 says; the en passant readings in the fidelity assessment
   are separate. Decide Rules review C1 (structures) and C5 (`StepMove` → `PieceMove`) at the same
   time, before more proofs depend on them.
   **What landed** (details in `docs/process/Rules.md` Round 5 and `docs/spec/Rules.md` §7a).
   - `CastleMove.legal_iff` in a new section of `Chess/Rules.lean`, exactly the statement above,
     on every board: **no one-king hypothesis**, no `WellFormed`. The proof shows more: the landing
     square is attacked after castling exactly when it was before, without `¬ InCheck p`; that
     hypothesis is used only against a second king of the mover. Standard axioms only; in the
     axioms ledger.
   - Supporting lemmas: `reaches_of_clear` (a reach transfers between boards when every line clear
     on the first is clear on the second; `reaches_congr` does not apply, since the boards differ
     between attacker and target), `CastleMove.pseudoLegal`, `CastleMove.play_board_of_ne`, and
     what the four castling squares hold after the move. In `Chess/Basic.lean`, four geometry
     lemmas: `Direction.eq_or_eq_opposite_of_dr_eq_zero`, `Square.dr_eq_zero_of_between`,
     `Square.df_eq_zero_of_between`, `Square.shift_one_of_between`.
   - Review fixes (`docs/process/Rules.md` Round 6): spec wording corrected (where `decide` is
     used, the axioms' sources, the length of L4.11's proof, "step" → "piece move" in four proof
     notes); two named accessors replace inline facts in the castling proofs,
     `Color.homeRank_eq_zero_or_seven` (Basic B6.3a) and `Position.CanCastle.not_inCheck` (Rules
     L7a.1a).
   - **Rules review C5 adopted (the rename only):** `StepMove` → `PieceMove`,
     `PseudoLegal.stepMove_of_kindAt` → `pieceMove_of_kindAt`; six Lean occurrences, all in
     `Rules`; current docs renamed. The rest of C5 (namespace rule in DESIGN §2, moving helpers,
     Position's `CastlingRights` docstring) is not done (Rules spec §12 item 9).
   - **Rules review C1 not adopted:** the rules stay conjunctions. Patterns on a structure are
     positional too, seven hand-written instances would restate trusted text, and M2, M4 and L4.11
     went through without it. Revisit at L4.6/M5 if positional patterns hurt (Rules spec design
     choice 14).
   - **Basic review C2 not adopted:** pawn moves stay `offset df (dr * c.forward)`. The predicted
     cost (`cases c` in every pawn proof) never appeared, and captures would stay offsets anyway
     (Rules spec §12 item 3).
   - Checks: clean `lake build` green (11 jobs, 6.8 s, 0.8 GB peak); `lake build ChessTest` green
     after the change (every target rebuilt, one at a time; wall time and peak memory of that run
     were not captured), plus two new tests in `ChessTest/Rules.lean` that decide e1g1 through
     `CastleMove.legal_iff` (incremental rebuild 28 s, 1.2 GB). Axioms ledger 128 entries.
5. ✅ **(Done, 2026-11-02.) Freeze the certificate interface before anything generates Lean.**
   Split `Chess/Game.lean`
   into `Game/Defs`, `Laws`, `Search`, `Cert` (Game review C2). (Since step 2, `Game/Defs` is no
   longer in a chess headline's trusted base; the split is now about build cost and the interface,
   not trust.) Generated files call
   only `checkWin`, `checkOnlyMove` and the glue lemmas, never `Forces` constructors. Decide
   whether `checkOnlyMove` takes an `OnlyMoveCert` structure. Add an untrusted `firstFailure`
   diagnostic that returns the path to the first rejecting node (Game review C3). Name headline
   positions once (`def gotham := fen "…"`).
   **What landed** (details in `docs/process/Game.md` Round 5, `docs/process/Puzzles.md`,
   `docs/process/ChessTest.md` Round 3).
   - **Split, as review C2 proposed.** `Chess/Game/Defs.lean` (trusted, 130 lines),
     `Laws.lean`, `Search.lean`, `Cert.lean` (both import `Laws`, neither imports the other),
     `Examples.lean` (the toy games and tests, still in the library), and the umbrella
     `Chess/Game.lean`, so every `import Chess.Game` is unchanged. Declarations moved verbatim; no
     name changed. Each file has a module docstring in the library's format; the `Laws` one now
     names `Forces.trans`, `OnlyWinningMove.of_refuted` and `.winsIn_play` (review C9). One spec,
     `docs/spec/Game.md`, covers the six files.
   - **`OnlyMoveCert`: adopted.** `checkOnlyMove n x best oc`, where the arguments are the claim and
     `oc : OnlyMoveCert G.Move` is the evidence (`next`, `refBudget`, `refs`). A generated call
     reads `checkOnlyMove 11 gotham (uci "b7b2") { next := …, refBudget := 10, refs := […] }`.
     The owner decision "one refutation budget or one per alternative" was taken: **one**, now the
     field `refBudget` (Game spec choice 24); a per-alternative field can be added later without
     breaking old files.
   - **Interface frozen.** Game spec §4.3: a generated file states claims with `Defs` (or the
     chess abbreviations), writes `Cert`/`OnlyMoveCert` values, and proves claims only through
     `checkWin_sound`, `checkOnlyMove_sound`, the glue lemmas and `OnlyWinningMove.of_refuted`;
     never a `Forces` constructor. New glue lemma `WinsIn.of_mated` for mate leaves. (The round
     reported mate leaves as the only gap; its review found a second, at defender nodes, closed by
     the review fixes below.) `ChessTest/Interface.lean` records the signatures with
     `#guard_msgs` (22 in the round, 25 after the review fixes), so a change fails
     `lake build ChessTest` (checked by mutating two expected lines). The name `Cert` is kept
     (review C3.2).
   - **Diagnostics.** `Cert.Rejection` (eight reasons, one per checker condition),
     `Game.firstFailure` (mirrors `checkForces`), `firstFailureWin`, `firstFailureOnlyMove`: the
     path of moves to the first rejecting node and the reason. Not trusted, but proved to agree with
     the checkers (`firstFailure_eq_none_iff`, `firstFailureOnlyMove_eq_none_iff`). Tested on the
     toy game (T15–T19, every reason) and on chess (three `#guard`s in `ChessTest/ChessGame.lean`).
   - **`Puzzles.gotham`** in the new module `Chess/Puzzles.lean` (imported by `Chess.lean`):
     the prototype's FEN, checked with python-chess (valid, Black to move, 34 legal moves, `b7b2`
     legal). Its `-` en passant field reads the same under this library's convention as under
     Stockfish's: the only candidate double push, `e2e4`, would have allowed `f4xe3` en passant, so
     every convention would have written `e3`. Tests in the module (three `#guard`s, about 1.4 s):
     the FEN written back, 34 legal moves, `b7b2` among them.
   - Ledgers: axioms 131 entries (`WinsIn.of_mated`, the two agreement theorems added).
   - **Review fixes** (same day; `docs/process/Game.md` Round 6, `docs/process/Puzzles.md` Round 2,
     `docs/process/ChessTest.md` Round 4). The interface was not self-sufficient at defender
     nodes: discharging the hypothesis of `Forces.replies_of_moves_eq` needed core's
     `List.forall_mem_cons`/`List.forall_mem_nil`. New glue `Forces.forall_mem_nil` and
     `Forces.forall_mem_cons` (Game spec L4.17, L4.18), and a toy test T20 that proves a win node
     by node with the glue alone. The interface ledger also records `Game.chess`, which generated
     files name when they call a checker: 25 entries. Axioms ledger: 133. Game spec choice 25 no
     longer overclaims: the agreement theorems prove that a diagnostic returns `none` exactly when
     its checker accepts; that its path and reason are right is tested, not proved. The three
     `#guard`s on `Puzzles.gotham` moved to `ChessTest/Puzzles.lean` (step 3's convention), so
     `Chess/Puzzles.lean` builds in about 0.6 s. The `move` case of `firstFailure` builds its path
     with a `match`, as `firstFailureReplies` does. THEOREMS C3 and C7 say how they were realized.
     The deadline of the owner's sign-off on the ep convention moved from step 5 to step 7 in this
     step, since `Puzzles.gotham` reads the same under either convention and the first checkpoints
     that depend on it are generated in step 7.
   **Not done.** Review C3.1's sentence "in the `scripts/` README": there is no such README yet (done in step 7: `scripts/README.md`);
   the rule is in Game spec §4.3, `Cert`'s module docstring and step 7 below. Game spec open item 2
   (the `replies` case reads the move list twice; review C6 measured that the kernel shares it) is
   still open for the owner to close.
6. ✅ **(Done, 2026-11-02.) Kernel cost, measured, then cut** (MoveGen review C2). Benchmark one Gotham-like node. Use
   `decide (Legal p m)` at attacker nodes and a proved-equal `kingSafeAfter` at defender nodes,
   swap a ray-walk `Slides` instance into `Rules` in place, and re-measure. If the projected
   320-node total is still more than a few minutes, schedule the bitboard layer (step 10b)
   before the demo instead of after it.
   **What landed** (`docs/process/MoveGen.md` Round 5, `Rules.md` Round 7, `Position.md` Round 5).
   - Measured on the real certificate (15 sampled nodes of each kind, `decide +kernel`): mate leaf
     2.0 s, defender move list 2.0 s, `m ∈ legalMoves p` 1.5 s, `Legal p m` 0.12 s, checkpoint
     0.11 s. Taking a mate leaf apart showed where: per pseudo-legal move, finding the king on the
     board after the move (about 28 ms) and `Board.AttackedBy`'s 64-square scan (60–80 ms).
   - Attacker nodes decide `Legal p m` (through `mem_chess_moves`), as planned.
   - **`kingSafeAfter`** (MoveGen D3.4, `kingSafeAfter_iff`): the super-piece test from the squares
     where the mover's king can stand, with the kings listed from the position *before* the move.
     The timings indicate that the kernel evaluates this list once per position, not once per
     move: they suggest that it reuses the evaluation of a repeated closed term within a
     declaration (its whnf cache), which would be how a precomputed fact reaches the kernel without
     a `let`. The speed-up was measured; the mechanism was not checked against the kernel's
     code. The proof of `kingSafeAfter_iff` needed **R3** (Rules L2.10–L2.12), now done.
     `legalMoves_eq_filter` keeps its statement, so nothing downstream changed.
   - `Piece.ofCode` as a table (Position spec §8 item 4's fallback, proved equal to the search).
   - **Not adopted:** the ray-walk `Slides` instance in Rules (measured about 15 % in a scratch copy;
     it would move `upToBlocker`, `slideTargets` and M1 into the trusted file).
   - After: mate leaf 0.68 s, defender move list 0.72 s, `Legal` 0.09 s, checkpoint 0.04 s. The
     Gotham certificate: about 430 s and 4.3 GB before, **165 s and 1.1 GB** after. The bitboard
     layer is not needed for Stage 1.
7. ✅ **(Done, 2026-11-02.) `scripts/` and the Stage 1 closing demo, where Stockfish enters.** **First, a strict file
   review of `Spec/Winning`** (and of `ChessGame/Fide`), in the format of `docs/reviews/`. Since G8,
   `Spec/Winning` is in the trusted base of every chess headline and has had no independent review.
   The review compares `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecMateIn` and
   `SpecOnlyWinningMove` with FIDE 3.9, 5.1.1 and 5.2.1 and with `Game.Forces`, rule for rule, and
   must be done before the demo's headline is stated. Then port the prototype's `gen_cert.py`.
   Stockfish (with python-chess) proposes attacker moves, orders defender replies, and finds
   refutations of alternatives. The script emits only what the frozen interface of step 5 allows
   (Game spec §4.3: `Cert`/`OnlyMoveCert` values, the checkers, their soundness theorems and the
   glue lemmas, never a `Forces` constructor or a lemma of core), states its claims about
   `Puzzles.gotham`, and on a rejection prints `firstFailureWin`/`firstFailureOnlyMove`. A
   `scripts/README.md` should repeat the interface rule (Game review C3.1). The script emits `Cert`
   values and literal checkpoints (`p.play m = ⟨Board.unpack 0x…, …⟩`) that follow this library's ep
   convention. Then prove `WinsIn .black 11 gotham` and `OnlyWinningMove gotham (uci "b7b2")`
   [kernel], and exact `MateIn` for a few mates in at most 3 by `searchForces`. Record
   `#print axioms`. **Stage 1 is closed.**
   **What landed** (`docs/process/ChessDemo.md`).
   - The review of `Spec/Winning` and `ChessGame/Fide`: `docs/reviews/Spec.Winning.md` (written by
     the demo's session, so not independent; verdict: no change needed; three low concerns: the
     draw rules left out, positions no game reaches until R9/R10, the open ep sign-off).
   - `scripts/gen_cert.py` (and `scripts/README.md` with the interface rule): Stockfish proposes,
     python-chess plays, `chess-perft` gives every move list in `legalMoves` order, the script writes
     checkpoints in this library's conventions, `Cert`/`OnlyMoveCert` values and one theorem per
     node; `--check` runs `firstFailureOnlyMove`. Deterministic (one thread, fixed depths): three
     runs gave the same tree.
   - The interface gained the only-move root (Game L4.19–L4.22: `OnlyWinningMove.of_moves_eq`,
     `refuted_nil`, `refuted_cons_self`, `refuted_cons`) and uses `mem_chess_moves` instead of
     `mem_legalMoves` (an elaboration issue, Game spec §4.1); the interface ledger records them.
   - The library `ChessDemo` (not a default target; `Elab.async = false`): `GothamCert` (generated,
     319 nodes, 165 s, 1.1 GB), `Gotham` (the headlines, plain and through G8, and
     `gotham_not_wins_white`), `Mates` (exact `MateIn` 1, 2, 3 by search; the mate in 3 proves its
     win by a certificate and its minimality by search), `Axioms` (`#print axioms` of every demo
     theorem: standard axioms only). No `native_decide` anywhere.
   - Measured and not used: the whole `OnlyMoveCert` checked at once (`decide +kernel` on
     `checkOnlyMove 11 p0 b7b2 cert = true`) did not finish in 30 minutes (stopped; about 2 GB):
     without checkpoints every board read goes down the chain of moves from the root. The per-node
     file is the only affordable kernel route, as in the prototype.
   - Review of step 7, fixed the same day (`docs/process/ChessDemo.md`, Round 2): the docstring of
     `gotham_onlyWinningMove` claimed forced mates after the alternatives, which `OnlyWinningMove`
     does not say; it now says only what the statement says, and the forced mates are a theorem
     of their own (`GothamCert.refutations`, generated, restated as `gotham_refuted` and, through
     G8, `gotham_specRefuted`). Game spec §4.3 now allows literal moves in a generated file, with
     the `uci "…" = lit` bridge in the restating file; the demo ledger has 16 entries.
   **Done afterwards** (2026-11-02): an independent review of `Spec/Winning` and `ChessGame/Fide`
   by a separate reviewer session, `docs/reviews/G8_REVIEW.md`. It found no soundness defect, and
   its F1 and F4 docstring notes are applied.
   **Not done.** The owner's ep sign-off (Rules review C4), now overdue; a `_native` variant (not
   needed: the kernel version is affordable).
7a. ✅ **(Done, 2026-11-02.) Readability round.** Fixes for the findings of an independent
   readability and fidelity audit, each reproduced by two skeptics. Details in the process logs:
   `Rules.md` Round 8, `Position.md` Round 6, `MoveGen.md` Round 6, `ChessGame.md` Round 7, and
   notes in `Basic.md`, `ChessTest.md`, `Spec.Winning.md`.
   - **Trusted definitions in one file.** `Chess.Rules` is an umbrella over `Rules/Defs` (every
     definition and instance, in reading order, nothing else), `Rules/Laws` and `Rules/Castling`
     (L4.11), as step 5 did for `Game`. In ChessGame's section "Accepting" the four trusted
     predicates now come before the parsers.
   - **False or stale trusted text fixed.** Position's `CastlingRights` docstring (it said rights
     change only through `revoke`/`revokeAll`; a move changes them through `ofGet` in
     `Move.castlingAfter`); Position's notes on `Piece.ofCode` (a table since step 6, not a search);
     `Checkmate` cites FIDE 1.4 and 1.4.1 (5.1.1 only states the result); the three rules that
     compare `relRank` give the 0-based value beside the rank's name; the `fen` docstring warns that
     the en passant field must follow this library's convention (ChessGame review C6 (a)).
   - **Names and homes.** `Board.Attacked` → `Board.AttackedBy` (the argument is the attacking
     colour; in `KingAttacked c` it is the king's), with its lemmas and MoveGen's
     `superpieceAttackedBy`. Rules review C5's helper moves: four `private` lemmas and
     `rookCastleSquare_ne_kingHome` to Basic, `CastlingRights.ofGet` to Position.
     `Board.squaresOf` and `CastlingRights.all` moved from ChessGame to Position (ChessGame review
     C5); MoveGen's duplicate `Board.kingSquares` is gone.
   - **Docs.** `agreesWithLegal`'s docstrings say that since M4 only its M5 half tests anything;
     MoveGen spec no longer speaks as if M4 were unproved. The eight abbreviated instance docstrings
     of Basic's spec are quoted in full. `scripts/check_docstrings.py` (Rules review C8) is in the
     repository and reports no missing definition docstring. DESIGN §5.5's `IsCapture`, the Rules
     module docstring's note on instances, and this file's trusted-base sentence are corrected.
   - Checks: `lake build`, `lake build ChessTest` (161 s, 3.4 GB), `lake build ChessDemo`
     (`GothamCert` 164 s, unchanged within noise; 2.8 GB) and `lake build chess-perft` all green;
     axioms ledger unchanged in size (names follow the rename).
   **Not done, on purpose** (each needs the owner or is larger than a fix):
   - **The three `WinsIn`s** (audit finding, low). `Chess.Game.WinsIn` (any game), `Chess.WinsIn`
     (the chess game, through the generator) and `SpecWinsIn` (the rules alone, the trusted
     reading since G8) share a name, and the plain name belongs to the generator's notion; "Spec"
     also names `docs/spec/`. A rename (for example `Chess.Fide.WinsIn` for the rules-only notions,
     in `Chess/Fide/Winning.lean`, or the rules-only notions as the plain `Chess.WinsIn` and the
     abbreviations as `GameWinsIn`) touches every headline, the demo, the interface ledger and the
     generated certificate's script. Listed under the owner decisions below.
   - **`Position.Sane` and pawns on the back ranks** (audit finding, low). `fen` accepts positions
     no game reaches (a pawn on its own first rank, which `PushMove` then lets step forward). This is
     documented (§2, ChessGame spec D4.5) and belongs to `WellFormed` (step 8), not to `Sane`,
     whose three conditions are chosen to be cheap at every `fen` literal.
   - The namespace rule of Rules review C5 (write it in DESIGN §2) and a one-page
     `docs/TRUSTED.md` listing, per trusted module, the definitions an auditor reads. Optional.
   - `docs/reviews/Spec.Winning.md` cites "FIDE 1.4.2 / 5.1.1" for checkmate; it is a dated review
     and was left as written (the definition is 1.4 and 1.4.1).
7b. ✅ **(Done, 2026-11-03.) The exact distance of the Gotham puzzle.** `MateIn .black 11
   Puzzles.gotham` and `SpecMateIn` (`ChessDemoBound/GothamMateIn.lean`), kernel only. The lower
   half, `¬ WinsIn .black 10 Puzzles.gotham`, is a generated certificate (`scripts/gen_bound.py`,
   `ChessDemoBound/Gotham10/`, 24,994 node theorems) that refutes every Black move at every Black
   turn, with new per-node glue in `Chess.Game.Cert` section `Bounds` (THEOREMS C9, toy tests
   T21–T25, signatures in `ChessTest.Interface`). Method and measurements:
   `docs/research/minimality.md`. Reviewed by three independent reviewers (Lean soundness, the
   Python tooling, the docs against the code): no soundness defect; the documentation and
   measurement errors they found are fixed (`docs/VERIFICATION.md` §9). `Chess.ChessGame` now imports
   the parts of `Chess.Game` it uses, not its examples, so editing a test no longer rebuilds the
   certificates. Open: checkmate checks are about 40% of the 4.5 CPU-hours of the build (a faster
   pseudo-legality filter, minimality.md "Next steps").
8. **Stage 2 remainder.** ~~M5 (`legalMoves` `Nodup`)~~ done 2026-11-03 (`legalMoves_nodup`,
   MoveGen section `NoDuplicates`); M8, perft as a counting theorem, can now use it. R3 attack
   symmetry (done in step 6). R6 colour flip and M9. `Chess/Invariants.lean` with `WellFormed`, `Reachable`, R7
   (material) and R9/R10 (invariants of legal play).
   - **Do not change `parseFEN`'s filter** while doing this, until the owner decides between
     ChessGame spec §7's Round 2 plan (filter `p.Sane ∧ WellFormed p`, M11.1 as stated) and
     ChessGame review C4 (filter stays `p.Sane` for good; `WellFormed (fen "…")` checked per
     literal; M11.1 dropped or restated). See the open owner decisions below. Evidence, gathered
     2026-11-02: today `parseFEN` accepts `4k3/8/8/8/8/8/8/4K3 w KQkq - 0 1`,
     `k7/8/8/8/8/8/8/K6P w - - 0 1` and `4k3/8/8/8/8/8/8/4K3 w - e6 0 1` (by `#eval`; an audit's
     differential run reported 94 accepted strings that python-chess rejects, not re-run here).
     Which library literals would fail under the strengthened filter cannot be checked until
     `WellFormed` exists. As a proxy, the 26 distinct FEN strings in the library's `.lean` files
     (all of them, outside `.lake`) were compared: `parseFEN` (by `#eval`) accepts 18, and
     python-chess 1.11.2's `Board.is_valid()` accepts all 18. The other 8 are negative tests that
     `parseFEN` already rejects; python-chess rejects 7 of them and accepts the eighth, the start
     position with a trailing space.
   - Optional, cheap to try: THEOREMS M7's `perft_initial_3` in the kernel. It was judged out of
     reach in step 3, when depth 2 of the initial position took 42 s and 3.9 GB; after step 6 it
     takes 9.8 s (re-measured 2026-11-02, `docs/spec/ChessTest.Perft.md` §3), and depth 3 has
     about 22 times as many leaves. Not tried: memory is the unknown. Try it alone, under
     `/usr/bin/time -l` and a timeout, in a scratch file first, and keep it only if it stays well
     under 9 GB.
9. **Stage 3, the approximation ladder.** Survival certificates (C4: "no forced mate within k";
   one kind exists since 2026-11-03, the per-node C9 glue and `scripts/gen_bound.py`, step 7b),
   the dual of win trees, same `Cert` shape) give **no-blunder within a horizon** (O5) and
   **only mate within N** (O4). These are honest, decidable approximations of "this move is
   optimal" for middlegames. Then traps (G9/C5: closed sets the defender can stay in), which let
   `checkOnlyMove` accept alternatives that only *draw*. Then the game value (G10) and `Optimal`
   (O0). O2 is already stated, so "only winning move ⇒ unique optimal move" is a short corollary.
   Stockfish's role here: choose which rung to attempt (a mate score suggests a win certificate,
   a drawish endgame score suggests a trap or tablebase, otherwise a bounded horizon) and supply
   the refutation lines.
10. **Later stages, shaped now.** (a) Stage 4: the clocked game `Clocked L` (G12–G15) as a second
   `Game` on positions plus a halfmove clock, and the corollary "a `WinsIn` win with clock headroom
   is a FIDE win". (b) Stage 5: the bitboard fast layer (`BitVec 64`/`Nat`, which the kernel
   accelerates) in `Chess/Fast/`, with a refinement theorem per step of `play` and against
   `Board.attackedBy_iff`, and a game morphism (G7) that moves certificates between layers. Ranked-set
   (tablebase) certificates (C6, O9), with Syzygy entering only as an explicit hypothesis, never
   an `axiom`.

**Open owner decisions** (each blocks the step in brackets): (Rules as structures or disjunction,
`StepMove` → `PieceMove` and Basic's pawn direction were decided in step 4, with reasons in the
Rules spec; the one refutation budget of `checkOnlyMove` was decided in step 5 (Game spec choice
24); the owner can still reverse any of them.) `CastlingRights.none` → `.empty` (Position review C2)
[any time, cheaper now]; sign-off on the ep convention (Rules review C4) [**overdue**: step 7 generated its checkpoints
in this library's convention; `Puzzles.gotham` reads the same under either, and the convention
does not change which moves are `Legal` (docs/reviews/Spec.Winning.md C3)];
`sq!e4` square literals (Basic review C4) [blocks no step now: step 3 finished without them;
optional, for readable tests]; the names of the three `WinsIn`
notions (step 7a) [before more headlines are stated]; whether `fen`'s filter stays `Sane` for good
(ChessGame review C4) or becomes `Sane ∧ WellFormed` (ChessGame spec §7, Round 2 plan), which
decides whether M11.1 is a theorem about the parser or a per-literal check [before step 8's
`WellFormed` touches `parseFEN`].

---

## 6. Where Stockfish fits

```
 Stockfish + python-chess (+ Syzygy)          untrusted, scripts/
   │ picks attacker moves, orders defender replies, finds refutations,
   │ chooses the rung of the ladder (win / survival / trap / tablebase)
   ▼
 generated .lean: Cert values + checkpoint literals    data, never trusted
   ▼
 checkWin / checkOnlyMove / (later) checkSurvival, checkTrap = true    kernel evaluation
   ▼  *_sound theorems
 Chess.WinsIn / OnlyWinningMove / (later) NoLossWithin, Holds    the game's vocabulary
   ▼  winsIn_iff_specWinsIn, onlyWinningMove_iff_specOnlyWinningMove (G8, ChessGame/Fide)
 SpecWinsIn / SpecOnlyWinningMove                                 statements about Rules alone
```

An engine evaluation never becomes a hypothesis or a conclusion. "Stockfish thinks m is best"
turns into the strongest game-theoretic statement its output lets us certify (research
`game-theory.md` §5–6): an R1 win, an R4 only winning move, or an R6/R7 horizon statement.

---

## 7. Name map: THEOREMS.md sketches → Lean

| THEOREMS.md | Lean |
|---|---|
| `Reach` | `Game.Forces` |
| `searchWin`, `searchWin_iff` | `Game.searchForces`, `Game.searchForces_iff` |
| `WinsIn.mono` | `Game.Forces.mono` (it applies to `WinsIn` by dot notation) |
| `Cert.mate` | `Cert.goal` |
| `Chess.game` | `Game.chess` |
| `pawnCapture`, inductive `PseudoLegal` | `PawnCaptureMove`; `PseudoLegal` as a disjunction of six predicates |
| `Castling`, `get c side` | `CastlingRights`, `get c w` |
| `inCheck p = true` | `InCheck p` (a decidable `Prop`) |
| `Attacked b c t`, `Board.Attacked` | `Board.AttackedBy b c t` (since the readability round) |
| `MateIn .white 11 gotham` | `WinsIn .black 11 Puzzles.gotham` (Gotham is Black to move), and since 2026-11-03 `MateIn .black 11 Puzzles.gotham` (`ChessDemo.gotham_mateIn`, lower half by a generated certificate) |
| `checkOnlyMove n x best c refs` (and DESIGN's earlier `n k x best c refs`) | `checkOnlyMove n x best oc` with `oc : OnlyMoveCert` (`next`, `refBudget`, `refs`), since step 5 |
