# Specification of `ChessDemo.Mates`

Role: demo implementer (one overnight round, ROADMAP step 7).
Date: 2026-11-02.
Status: Round 1 (cost table of §3 corrected after review, 2026-11-02), matched to `ChessDemo/Mates.lean` (see `docs/process/ChessDemo.md`). Every
theorem below is proved, kernel only, with no `sorry`.

Library: `ChessDemo`. File: `ChessDemo/Mates.lean`. Imports: `Chess.ChessGame`.

ROADMAP step 7 asks for "exact `MateIn` for a few mates in at most 3 by `searchForces`". `MateIn a n
x` is `WinsIn a n x ∧ ∀ k < n, ¬ WinsIn a k x`: the second half, that no shorter mate exists, is
the half that needs a search; a certificate cannot show it.

## 0. How to read this document

The conventions of `docs/spec/ChessGame.md` §0 apply: each definition and theorem has an ID, an
English statement that is its Lean docstring word for word, and its Lean statement. Everything lives
in `namespace ChessDemo`, with `open Chess`.

### The module docstring, word for word

```
# Small exact mates

Exact `MateIn` claims about three small positions. That no shorter mate exists is decided by the
bounded search of `Chess.Game.Search` (`searchForces`, through the instances `Forces.decidable` and
`MateIn.decidable`) and evaluated by the kernel; so is the mate itself in 1 and in 2, while the
mate in 3 is proved by a checked certificate. Specification: `docs/spec/ChessDemo.Mates.md`;
every definition and theorem below carries the docstring given there.

## Main definitions

* `foolsMate`, `rookMate2`, `rookMate3`: the three positions.

## Main statements

* `foolsMate_mateIn`: after 1. f3 e5 2. g4, Black mates in exactly 1 (`Qh4#`).
* `rookMate2_mateIn`: White mates in exactly 2 (1. Rc6 Kh8 2. Rh6#).
* `rookMate3_mateIn`: White mates in exactly 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#).

## Implementation notes

* The search tries every move at every attacker node, in the order of `legalMoves`, and its kernel
  cost and memory grow quickly with the number of nodes it visits (measured: a mate in 2 whose
  search visits about 300 defender nodes took 7 GB). The positions were chosen, with a cost model
  that replays the search in this order, so that it visits few nodes.
* `rookMate3_mateIn` is split by `Game.mateIn_succ_iff` into a win within 3, proved by a
  certificate (`Game.checkWin_sound`), and no win within 2, proved by search. Deciding
  `MateIn .white 3 rookMate3` by search alone also works but took 48 s and 5.9 GB.
* Kernel only (`decide +kernel`); no `native_decide`.
```

## 1. Positions

| ID | Docstring | Lean |
|---|---|---|
| DM1 | The position after 1. f3 e5 2. g4, Black to move. The en passant target `g3` is written, as this library writes it after every two-square advance. | `def foolsMate : Position := fen "rnbqkbnr/pppp1ppp/8/4p3/6P1/5P2/PPPPP2P/RNBQKBNR b KQkq g3 0 2"` |
| DM2 | White: king f7, rook f6, pawn b4; Black: king h7. White to move. | `def rookMate2 : Position := fen "8/5K1k/5R2/8/1P6/8/8/8 w - - 0 1"` |
| DM3 | White: king f8, rook e2, pawn h6; Black: king h8, pawn h7. White to move. | `def rookMate3 : Position := fen "5K1k/7p/7P/8/8/8/4R3/8 w - - 0 1"` |

Each was confirmed by Stockfish 19 (mate in 1, 2 and 3, with the lines in the docstrings below) and
python-chess; the kernel proofs do not depend on that.

## 2. Theorems

| ID | English (= Lean docstring) | Lean |
|---|---|---|
| DM4 | **Fool's mate.** After 1. f3 e5 2. g4, Black mates in exactly 1 (`Qh4#`). | `theorem foolsMate_mateIn : MateIn .black 1 foolsMate := by decide +kernel` |
| DM5 | **A mate in 2.** White mates in exactly 2 (1. Rc6 Kh8 2. Rh6#), and not in 1. | `theorem rookMate2_mateIn : MateIn .white 2 rookMate2 := by decide +kernel` |
| DM6 | White mates within 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#), by a checked certificate. | `theorem rookMate3_winsIn : WinsIn .white 3 rookMate3 := Game.checkWin_sound (c := .move (uci "f8e8") (.replies [(uci "h8g8", .move (uci "e2f2") (.replies [(uci "g8h8", .move (uci "f2f8") .goal)]))])) (by decide +kernel)` |
| DM7 | White cannot mate within 2, by search. | `theorem rookMate3_not_winsIn_two : ¬ WinsIn .white 2 rookMate3 := by decide +kernel` |
| DM8 | **A mate in 3.** White mates in exactly 3 (1. Ke8 Kg8 2. Rf2 Kh8 3. Rf8#), and not in 2. | `theorem rookMate3_mateIn : MateIn .white 3 rookMate3 := Game.mateIn_succ_iff.mpr ⟨rookMate3_winsIn, rookMate3_not_winsIn_two⟩` |

Notes.
- DM4, DM5 and DM7 are decided by `searchForces` (THEOREMS G5): `MateIn.decidable` checks
  `WinsIn n` and `¬ WinsIn k` for each `k < n`, each by `Forces.decidable`, which is
  `decidable_of_iff _ searchForces_iff`.
- DM6's certificate lists one reply per defender node because the defender has one legal move
  there (after 1. Ke8 only Kg8; after 2. Rf2 only Kh8); `checkWin` would reject it otherwise
  (`missingReply`).
- DM8 uses G6 (`mateIn_succ_iff`): mating in exactly `n + 1` is winning within `n + 1` and not within
  `n`, since `WinsIn` is monotone in the budget.

## 3. Cost (kernel, sequential, 2026-11-02)

| Claim | Time | Peak memory |
|---|---|---|
| DM4 `MateIn .black 1 foolsMate` | 4.0 s | 1.6 GB (DM4 alone, in a file holding only it) |
| DM5 `MateIn .white 2 rookMate2` | 3.3 s | 1.5 GB (DM5 alone, likewise) |
| DM6 + DM7 | 19 s for `lake build ChessDemo.Mates` with them (clean build, in parallel with `GothamCert`) | |
| The whole file, sequential (`lake env lean -DElab.async=false ChessDemo/Mates.lean`) | 18 s | 2.7 GB |
| `MateIn .white 3 rookMate3` by search alone (not used) | 48 s | 5.9 GB |
| `WinsIn .white 3 rookMate3` by search (not used) | 19.7 s | 5.7 GB |
| `¬ WinsIn .white 2 rookMate3` by search (DM7) | 7.6 s | |
| `MateIn .white 2 (fen "7k/8/5K2/8/8/8/8/6R1 w - - 0 1")` by search (rejected) | 408 s | 7.2 GB |

How the positions were chosen: a Python model of the search (`attackerForces`/`defenderStep`, with
their short-circuits, in the order of `legalMoves`, which it gets from `chess-perft`) counts the
defender nodes the search decides. The rejected mate in 2 above visits 294 of them; DM5 visits 21,
DM3's mate in 3 184. Random positions with a few pieces were sampled and the cheapest kept.
