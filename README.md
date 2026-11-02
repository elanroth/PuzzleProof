# Chess: a Lean 4 library for proving chess facts

The goal is to prove statements such as

```lean
OnlyWinningMove gotham (uci "b7b2") ∧ WinsIn .black 11 gotham
```

with the Lean kernel as the checker. Stockfish is only an untrusted source of certificates.
The rules of chess are written as a readable specification. Every definition has an English
docstring, and that docstring also appears in `docs/spec/`. Executable code (the move generator,
the search, the certificate checkers) is linked to the specification by proved theorems.

Lean 4.28.0, core and Std only (no Mathlib). Status: `lake build` is green, with no `sorry`, no
`axiom` and no `native_decide`. See [`docs/ROADMAP.md`](docs/ROADMAP.md) for where things stand
and what comes next.

## Build

```sh
cd chess-library
lake build        # about 30 s from clean; most of it is the test sections
```

In VS Code, install the **lean4** extension (`leanprover.lean4`) and open the `chess-library`
folder itself, not the repository root, so that the extension finds `lakefile.toml`. Run
`lake build` once before opening files, so that imports load from `.lake/` instead of being
rebuilt in the editor. Put the cursor on a theorem to see its goal in the Infoview. `#guard` and
`example` lines at the bottom of each file are the tests.

## What to read first

1. **`docs/ROADMAP.md`**: current state, how faithful the English↔Lean match is, risks, and the
   next steps.
2. **`Chess/Rules.lean`**, next to **`docs/spec/Rules.md`**: the trusted heart, meaning what
   "attacks", "check", "legal move", "checkmate" and "playing a move" mean. Every docstring there is
   meant to be checked against the FIDE Laws by a chess player.
3. **`Chess/Game.lean`**, section "Games" (under 100 lines): what `WinsIn`, `MateIn` and
   `OnlyWinningMove` mean for any two-player game. The rest of the file is proofs, the bounded
   search and the certificate checker.
4. **`Chess/ChessGame.lean`**: chess as a game, and the `fen "…"`/`uci "…"` notation. The tests at
   the bottom show headline-style statements (a mate in 1, Fool's mate, a stalemate).
5. `docs/DESIGN.md` (architecture and the reasons for it) and `docs/THEOREMS.md` (the target
   theorems, tiers R/M/G/C/O, stages 1–5). THEOREMS predates some renames. The name map at the
   end of the roadmap covers them.

## File map

| Path | Contents |
|---|---|
| `Chess.lean` | Root; imports the six modules. |
| `Chess/Basic.lean` | Colours, kinds, pieces, squares (`Fin 8 × Fin 8`), offsets, directions, rays, castling squares. |
| `Chess/Position.lean` | `Board` (a function from squares), packed board literals, `Move` (UCI shape), `CastlingRights`, `Position`. |
| `Chess/Rules.lean` | **Trusted FIDE spec**: `Reaches`, `Attacked`, `InCheck`, the six move rules, `PseudoLegal`, `Position.play`, `Legal`, `Checkmate`, `Stalemate`. |
| `Chess/MoveGen.lean` | `legalMoves` (geometry proposes, the rules dispose; proved sound), perft, and agreement tests against the spec. |
| `Chess/Game.lean` | Abstract games: `Forces`, `WinsIn`, `MateIn`, `OnlyWinningMove`, their laws, a search proved correct, and `Cert` with checkers proved sound and complete. |
| `Chess/ChessGame.lean` | `Game.chess`, the `Chess.WinsIn`/… abbreviations, and FEN/UCI read and write with proved round trips. |
| `docs/spec/<Module>.md` | English specification of each module, definition by definition. |
| `docs/process/<Module>.md` | Log of the English↔Lean rounds: what changed and why. |
| `docs/reviews/<Module>.md` | File-level design reviews: verdicts, concerns, measurements. |
| `docs/research/*.md` | Background: prior formal work, game theory and Stockfish's role, board representations, Lean engineering, the theorem landscape. |
| `docs/THEOREMS.md`, `docs/DESIGN.md`, `docs/ROADMAP.md` | Target theorems, architecture, plan. |

The throwaway prototype that preceded this library is in `../chess-lean`. It has a nibble-packed
board and a kernel-checked mate in 11. It is kept for its certificate generator
(`scripts/gen_cert.py`) and its measurements, not for its design.
