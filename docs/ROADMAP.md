# Roadmap for `Chess`

Author role: library reviewer. Date: 2026-11-01. Read for this document: all of `Chess/*.lean`,
`Chess.lean`, `docs/THEOREMS.md`, `docs/DESIGN.md`, and the specs, process logs, reviews and research
under `docs/`. This file summarizes where the library stands and what to do next. Where it disagrees
with an older document, the code is the reference, and this file says which document is stale.

---

## 0. Status at a glance

| Check | Result |
|---|---|
| `lake build` (clean, Lean 4.28.0, core only) | **green**, 9 jobs, about 33 s. Most of the time is the test sections of `MoveGen` (12 s) and `ChessGame` (12 s). |
| `sorry` / `admit` | **0** |
| `TARGET` markers | **0**. [later] lemmas are kept in the specs, not as `sorry` stubs in the Lean. |
| `axiom` declarations, `native_decide`, `partial`, `unsafe` | **0** |
| `#print axioms` sample (`mem_legalMoves`, checked in scratch) | `propext`, `Classical.choice`, `Quot.sound` |
| Size | 6 modules, about 4 900 lines, about 365 theorems, about 165 `example`/`#guard` tests |

Every definition in `Chess/` has a docstring that appears word for word in its `docs/spec/<Module>.md`.
Each module went through four rounds: English spec, critique, Lean translation, critique of the Lean
and revision of the English. Each round is logged in `docs/process/<Module>.md`, and each module has
a file-level review in `docs/reviews/<Module>.md`.

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
  │                                         ├──► ChessGame
  └──► Game ────────────────────────────────┘
```

| Module | What it is | Headline content |
|---|---|---|
| `Chess.Basic` | Finite vocabulary and board geometry | `Square` as two `Fin 8`. One geometric primitive, `Square.offset`, with one characterizing lemma (`offset_eq_some_iff`). Every proof goes through it and ends with `omega`. Shifts, rays, knight jumps, relative ranks, castling squares. R1 and R2. |
| `Chess.Position` | Data of the move layer | `Board := Square → Option Piece` with `set` as its only writer. `Board.pack`/`unpack` (hex-nibble `Nat` literals for kernel checkpoints, `unpack_pack`). `Move` in UCI form. `CastlingRights` as four flags behind `get`/`revoke`. `Position` (no clocks, no history). |
| `Chess.Rules` | **The trusted FIDE specification** | `Reaches`/`Slides` (geometry that reads only squares strictly between), `Attacked`, `InCheck`. Six named rule predicates joined into `PseudoLegal`. `Position.play` as six named steps over write lists. `Legal`, `Checkmate`, `Stalemate`. Frame lemmas (R4), R5, R8, R11. |
| `Chess.MoveGen` | Executable generator | **Propose and dispose**: geometry proposes `candidates`, and the generator keeps those that `PseudoLegal`/`Legal` accept. Soundness (`legalMoves_sound`) is one line. M1 (`mem_slideTargets`, `mem_reachTargets`). Perft. A spec-only oracle `legalMovesBySpec` with `agreesWithLegal`, a Boolean test that becomes a per-position theorem. |
| `Chess.Game` | Abstract two-player game theory, chess-free | `Forces a T n x` (three rules), `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`. Laws G2–G4 and G6. A bounded search proved correct (`searchForces_iff`, so `Forces`/`MateIn` are decidable). `Cert` with a structural checker: sound (C1), complete (C2), plus `checkOnlyMove_sound` (C7) and per-node glue lemmas (C3). A toy take-away game exercises all of it. |
| `Chess.ChessGame` | Chess as a game, plus notation | `Game.chess` (moves = `legalMoves`, mated = in check with no listed move). `Chess.WinsIn`/`Wins`/`MateIn`/`OnlyWinningMove`. `fen "…"` and `uci "…"` take a proof argument that is discharged automatically. The parsers are untrusted: their meaning is pinned by `fen_eq_iff` and `uci_eq_iff` against the trusted writers and `IsFEN`/`Position.Sane`. A round trip is proved for every position (`readFEN_toFEN`). |

### Stage 1 (★) milestone, item by item (THEOREMS §7)

| ID | Status | Lean name(s) |
|---|---|---|
| R1 | done | `Square.ofIndex_index`, `Square.index_ofIndex` |
| R2 | done | `mem_all`/`all_nodup` for every finite type; whole-type quantifiers at `priority := low` |
| R4 | done | `play_board_of_not_mem`, `play_board_src/dst/epVictim/rookHome/rookCastleSquare`, `play_turn` |
| R5 | done | `PseudoLegal.isLight_dst_iff_of_bishop`, `…_of_knight` |
| R11 | done | `checkmate_or_stalemate`, `not_checkmate_and_stalemate` |
| M7 | **partial** | perft 2 of the initial position = 400; 17 regression positions with `agreesWithLegal`. The six standard perft positions are not in yet. |
| G1 | done | `Game`, `Game.chess` |
| G2, G3, G4, G6 | done | `winsIn_zero_iff`, `not_wins_of_stalemate`, `Forces.mono`, `WinsIn.not_both`, `Wins.not_both`, `MateIn.unique`, `Wins.exists_mateIn` |
| G5 | done | `searchForces_iff` (THEOREMS still calls it `searchWin_iff`) |
| C1, C2, C3, C7 | done | `checkWin_sound`, `checkWin_complete`, `Forces.move_of_play_eq`/`replies_of_moves_eq`/`of_play_eq`, `checkOnlyMove_sound` |
| O2 | done | `OnlyWinningMove.wins_iff`, `.unique`, `.of_refuted`, `.winsIn_play` |
| O8 (bonus) | done | `Forces.trans` |
| **Closing demo** | **not started** | Gotham `WinsIn .black 11` and `OnlyWinningMove … (uci "b7b2")`, [kernel] |

Stage 2 items already reached: M1 (target lists) and M4 soundness. **M4 completeness is proved but
not landed.** The 56-line cover proof in `docs/reviews/MoveGen.md` (Appendix) elaborates against
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
     king-safety test on the board after castling. The informal argument that the two agree is
     sound (Rules review C2 sketches a proof via `reaches_congr`), but it is not a theorem yet
     (spec L4.11). **This is the one place where the trusted Lean does not say literally what FIDE
     says.**
  2. **En passant target convention.** `play` sets `epTarget` after every double push, whether or
     not a capture is possible. This is the PGN convention, not Stockfish's or Lichess's. Two
     positions that FIDE 9.2.3 counts as identical can therefore differ as `Position` values. This
     is harmless for `WinsIn`. It matters for repetition (Stage 4, G16 `normalize`) and for any FEN
     copied from Stockfish or Lichess right after a double push (ChessGame review C6).
  3. `Reaches` deliberately ignores pins and what stands on the source square (FIDE 3.9.1: check is
     geometric). `EnPassantMove` adds plausibility conditions (target on the sixth rank, the
     victim's origin square empty). They are implied in any reachable position, and they make
     arbitrary FEN input safe.
- `MoveGen`: until completeness lands, `legalMoves` is the one trusted claim of the library:
  "available" in `Game.chess` means "listed by `legalMoves`". So today every `Chess.WinsIn`
  statement is about *generator chess*. The soundness direction is proved. The completeness
  direction is tested on 17 positions, proved on one (`kingsPos`), and proved in general in the
  review appendix, waiting to be pasted in. Step 1 closes this gap.
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

**Trusted base for a Stage 1 chess headline today:** the kernel; the English and Lean of `Basic`,
`Position`, `Rules`; the section "Games" of `Game` (under 100 lines); `Game.chess` with the four
abbreviations; the writers and `IsFEN`/`Sane` in `ChessGame`; and `legalMoves` as the meaning of
"legal". The last item disappears with step 1, and the rest of `MoveGen` drops out after step 2.

---

## 3. The design decisions that matter most

1. **Spec and implementation are separate, and the implementation only filters.** `legalMoves` never
   re-implements a rule. It filters geometric candidates by the `Rules` predicates. This is why
   soundness is one line and completeness is a 56-line cover lemma with no pin or check reasoning.
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
   (M5, invariants) depend on conjunct order.
4. **The game semantics are inductive (`Forces`), and the search and certificates are executable
   Booleans proved against it.** The trusted part is three inference rules. Everything Stockfish
   produces lands as a `Cert` (data) checked by `checkForces`, whose soundness theorem is the only
   bridge. No engine number ever appears in a statement.
5. **No clocks or history in `Position`.** `WinsIn` lives in the game without draw rules (G∞).
   The FIDE game with clocks is planned as a second `Game` instance on the same states (G12–G15),
   not as an edit to this one.
6. **`Game.chess.Mated` is executable** (`InCheck p ∧ legalMoves p = []`). Kernel-checking
   `Checkmate` through `Legal` directly over 20 480 candidate moves did not finish in 500 s; through
   the generator it takes about 3 s. G8 bridges the two.
7. **Notation is proved, not trusted.** `fen`/`uci` carry their parse proof, and the parsers are
   characterized by `iff` lemmas. Copy this pattern for any future input format (PGN, EPD, Syzygy
   probes).
8. **Budgets are counted at the claim's state, attacker moves only.** The only-move checker uses
   the same convention (`WinsIn .black 11 gotham`, with no off-by-one).

---

## 4. Risks

| Risk | Severity | Evidence | Mitigation |
|---|---|---|---|
| **Kernel cost per certificate node.** `legalMoves` costs about 3.2 s per node in the kernel (initial position), about 13× the prototype's packed board (about 0.25 s). A Gotham-sized certificate (about 320 nodes) would take about 9 min or more and several GB. | **high** | MoveGen review C2; Rules review C3 | In order: `decide (Legal p m)` at attacker nodes (0.27 s); a local `kingSafeAfter` Boolean with an `_iff` lemma at defender nodes (about 2×); a ray-walk `Slides` instance swapped in place inside `Rules` (about 3×). Faster instances declared *after* `Rules` do **not** propagate into its composite instances. If that is still not enough, bring the bitboard fast layer (with a game morphism, G7) forward from Stage 5. |
| The Stage 1 demonstration has not been attempted on the new definitions | high | no `scripts/`, no certificate files | Steps 5–7 below. Measure before deciding on the fast layer. |
| Tests live inside library modules: 26 of `ChessGame`'s 29.5 s, most of `MoveGen`'s 12 s. Every edit rebuilds all dependents, including future generated certificate files. | medium-high | ChessGame review C3, MoveGen review C4 | Create a `ChessTest` `lean_lib` outside `defaultTargets` (step 3). |
| Positional `rcases` over the six rules is brittle under any change to rule conjuncts | medium | Rules review C1, MoveGen review C1 | Decide the structures question once, before M5 and the invariants. |
| L4.11 (castling landing square) unproved inside trusted text | medium | Rules spec §12 | Step 4. |
| Document drift: THEOREMS.md still uses pre-design names (`searchWin`, `Reach`, `Cert.mate`, `Chess.game`, "exactly 11" for Gotham). DESIGN §3 still has a "trusted UNTIL STAGE 2" box that step 1 makes obsolete. | low-medium | DESIGN §12 lists the edits | The theorem architect applies DESIGN §12. The name map in §7 below covers the gap until then. |
| `Game.lean` is 748 lines, while the trusted section "Games" is under 100 | low-medium | Game review C2 | Split at the trust boundary before generated files import it (step 5). |
| `OnlyWinningMove` can only be certified when every alternative *loses* | known limit | Game spec, `checkOnlyMove` docstring | Stage 3 trap (draw) certificates (step 9). |
| Python-chess FEN default drops ep targets that no pawn can use, which breaks checkpoint equality after double pushes | low, but silent | DESIGN §7.4 | `scripts/` must use `board.fen(en_passant="fen")`. Better: generate checkpoints with Lean's own `toFEN`/`pack`. |

---

## 5. Next steps, ordered toward the THEOREMS milestones

Each step goes through the same loop as the existing modules: English spec, then critique, then
Lean, then critique, then a file review. Steps 1–7 close **Stage 1**, and on the way steps 1–2
deliver the **Stage 2 headline** (M4 and G8). Step 8 completes Stage 2, and steps 9–10 open
Stages 3–5.

1. **Land generator completeness (M4, M6; THEOREMS ★★).** Add a section `Completeness` to
   `Chess/MoveGen.lean` with `PseudoLegal.mem_candidates` (the cover), `mem_pseudoMoves`,
   `mem_legalMoves`, `checkmate_iff` and `stalemate_iff`, from the MoveGen review appendix
   (verified against today's build). Use `CastleMove.eq_castle` in the castling bullet. Register
   `Checkmate.decidable` through `checkmate_iff` (about 3 s in the kernel instead of more than
   500 s). Restore the plain docstrings ("the legal moves of `p`"), and drop "trusted until M4"
   from DESIGN §3 and §7.3 and from the module header. Effect: `Chess.WinsIn` is about FIDE-legal
   moves from Stage 1 on.
2. **G8 in its own files (Stage 2 headline, now cheap).** `Chess/Spec/Winning.lean` (imports `Rules`
   only) defines `SpecForces`/`SpecWinsIn`/`SpecOnlyWinningMove` from `Legal`, `play` and
   `Checkmate`. `Chess/ChessGame/Fide.lean` proves `Chess.WinsIn a n p ↔ SpecWinsIn a n p` and
   the same for the only-move notion, from `mem_legalMoves` and `checkmate_iff`. After this, a
   headline reader's trusted base is `Rules` plus `Spec/Winning` plus notation; `MoveGen` and
   `Game` are no longer trusted (ChessGame review C2).
3. **Test library and M7.** Create `ChessTest` (second `lean_lib`, not a default target). Move the
   `## Tests` sections there and keep only cheap `#guard`s as documentation in the modules. Add
   the six standard perft positions (chessprogramming.org) at depths 1–2 in the kernel, deeper by
   `#eval`/`#guard` (time compiled `perft 3`/`perft 4` first), plus the two bug-class positions of
   DESIGN §8.4. Add a `#print axioms` ledger file for every headline theorem, so that trust labels
   are checked, not claimed.
4. **Prove L4.11:** `CastleMove p w m → (Legal p m ↔ ¬ p.board.Attacked p.turn.other
   (kingCastleSquare p.turn w))`, by `reaches_congr` plus edge-square arithmetic (Rules review C2).
   This removes the last literal-fidelity gap in `Rules`. Decide Rules review C1 (structures)
   and C5 (`StepMove` → `PieceMove`) at the same time, before more proofs depend on them.
5. **Freeze the certificate interface before anything generates Lean.** Split `Chess/Game.lean`
   into `Game/Defs` (trusted), `Laws`, `Search`, `Cert` (Game review C2). Generated files call
   only `checkWin`, `checkOnlyMove` and the glue lemmas, never `Forces` constructors. Decide
   whether `checkOnlyMove` takes an `OnlyMoveCert` structure. Add an untrusted `firstFailure`
   diagnostic that returns the path to the first rejecting node (Game review C3). Name headline
   positions once (`def gotham := fen "…"`).
6. **Kernel cost, measured, then cut** (MoveGen review C2). Benchmark one Gotham-like node. Use
   `decide (Legal p m)` at attacker nodes and a proved-equal `kingSafeAfter` at defender nodes,
   swap a ray-walk `Slides` instance into `Rules` in place, and re-measure. If the projected
   320-node total is still more than a few minutes, schedule the bitboard layer (step 10b)
   before the demo instead of after it.
7. **`scripts/` and the Stage 1 closing demo, where Stockfish enters.** Port the prototype's
   `gen_cert.py`. Stockfish (with python-chess) proposes attacker moves, orders defender replies,
   and finds refutations of alternatives. The script emits `Cert` values and literal
   checkpoints (`p.play m = ⟨Board.unpack 0x…, …⟩`) that follow this library's ep convention.
   Then prove `WinsIn .black 11 gotham` and `OnlyWinningMove gotham (uci "b7b2")` [kernel], and
   exact `MateIn` for a few mates in at most 3 by `searchForces`. Record `#print axioms`.
   **Stage 1 is closed.**
8. **Stage 2 remainder.** M5 (`legalMoves` `Nodup`; needed only for M8, perft as a counting
   theorem, if G7 morphisms are stated by membership, as Game review C4 recommends). R3 attack
   symmetry. R6 colour flip and M9. `Chess/Invariants.lean` with `WellFormed`, `Reachable`, R7
   (material) and R9/R10 (invariants of legal play).
9. **Stage 3, the approximation ladder.** Survival certificates (C4: "no forced mate within k",
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
   `Board.attacked_iff`, and a game morphism (G7) that moves certificates between layers. Ranked-set
   (tablebase) certificates (C6, O9), with Syzygy entering only as an explicit hypothesis, never
   an `axiom`.

**Open owner decisions** (each blocks the step in brackets): Rules as structures or disjunction,
and `StepMove` → `PieceMove` [4]; `CastlingRights.none` → `.empty` (Position review C2) [any time,
cheaper now]; sign-off on the ep convention (Rules review C4) [5]; one refutation budget `k` or one
per alternative in `checkOnlyMove` [5]; `sq!e4` square literals (Basic review C4) [3, for readable
tests].

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
 Chess.WinsIn / OnlyWinningMove / (later) NoLossWithin, Holds    statements about Rules (after G8)
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
| `MateIn .white 11 gotham` | `WinsIn .black 11 gotham` (Gotham is Black to move; exact `MateIn` only for short mates) |
