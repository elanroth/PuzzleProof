# ChessProof: certified forced mates in Lean 4

Exploratory prototype. The goal is to prove claims like "this is the only move that wins"
about concrete chess positions, with an untrusted engine doing the search and a small
verified checker doing the trusting.

## Layout

| File | What it is |
|---|---|
| `ChessProof/Basic.lean` | Kernel-friendly model: the board is one `Nat` (64 nibbles); legal moves incl. castling, en passant, promotion |
| `ChessProof/Fen.lean` | FEN and UCI parsing over `List Char`, so `fen "..."` reduces in the kernel |
| `ChessProof/Cert.lean` | `WinsIn` semantics, `Cert`, `check`, `check_sound`, `not_both`, `onlyMove_sound` |
| `ChessProof/Gotham.lean` | The GothamChess mate-in-11 position: mate in 11 and the only-move theorem (`native_decide`) |
| `ChessProof/GothamKernel.lean` | Same two theorems, kernel-only: 320 generated per-node theorems (~80 s, ~6 GB) |
| `ChessProof/Line.lean` | Only-move theorems for later Black moves along the main line (`native_decide`) |
| `ChessProof/Certs/*.lean` | Generated certificates (Stockfish + python-chess, untrusted) |
| `Perft.lean` | `lake exe perft [divide] <depth> <fen>` for differential testing |
| `Flatten.lean` | `lake exe flatten > ChessProof/GothamKernel.lean` regenerates the kernel-only file |
| `scripts/gen_cert.py` | Certificate generator |
| `artifact/` | The research write-up page |

## Commands

```bash
lake build                                  # model, certs, native_decide theorems, perft
lake build ChessProof.GothamKernel          # kernel-only proofs (slow, memory heavy)
python -I scripts/gen_cert.py OUT.lean NAME "<fen>" <mate-depth> --only-move
```

`gen_cert.py` needs `python-chess` and a `stockfish` binary on `PATH`.

## What is and isn't trusted

Trusted: the Lean kernel, and `ChessProof/Basic.lean` as the definition of chess. The move
generator matches python-chess perft counts on the standard chessprogramming suite but is not
proved against a declarative rule set. The 50-move and repetition rules are not modelled.
Theorems in `Gotham.lean` and `Line.lean` additionally trust the compiler (`native_decide`).
