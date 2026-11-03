# Is 11 the minimum? The proof of "no mate within 10"

2026-11-02. Script: `scripts/measure_minimality.py`. Data: `docs/research/data/minimality-gotham.json`.

## The claim and its two halves

`MateIn .black 11 Puzzles.gotham` says Black mates in exactly 11. Its two halves need different
kinds of proof:

* **Black mates within 11** (`gotham_winsIn`, proved). This is an existence claim, so one good Black
  move per position is a complete proof. Stockfish's choice of that move is checked, never trusted.
* **Black does not mate within 10** (`gotham_not_winsIn_ten`, proved 2026-11-03). This is a
  claim about every possibility.
  At each Black turn, *every* legal Black move must be answered: White escapes with one reply,
  White forces mate itself, White is stalemated, or Black has no moves left in the budget. No
  engine choice can narrow the Black side.

## How the second half is searched

For a budget n, the script builds a certificate for `¬ WinsIn .black n Puzzles.gotham`, reading
`WinsIn` exactly as `Chess.Game.Forces` does:

* **Black to move, budget n.** Every legal Black move is searched, each with budget n − 1 at the
  White node it reaches. With budget 0 there is nothing left to refute.
* **White to move, budget k.** If White is checkmated, Black has won and the branch fails.
  Otherwise one of these closes it:
  * White is stalemated, or k = 0;
  * White forces mate within 4 moves, with every Black reply searched. No position is a forced win
    for both sides (`Game.not_wins_of_winsIn_other`), so Black then has no forced win at all;
  * one White reply, after which Black, to move with budget k, is refuted again.

Stockfish guides the White side only: it orders White's candidate replies, and its mate score
(searched to depth 12) says whether, and within how many moves, to try a White forced mate of 2 to 4
moves. It cannot make anything pass, because a suggested reply is kept only if the search then
refutes every Black move after it, and a forced mate is kept only if it is found with every Black
reply searched. It is not optional in practice: with no engine (`--stockfish` left out) only White
mates in 1 are tried as shortcuts and White's checks are tried first, which is the failed first
attempt described below (872,826 nodes at n = 8, n = 9 unfinished). A different Stockfish version
can give different hints and so a different, equally valid, certificate.

Positions are shared: a position refuted with budget n is refuted for every smaller budget, so
the certificate is a DAG. One Lean theorem per DAG node would be enough.

## Results

All on this machine (10 cores, one Python process); times are the search only. A certificate node
is a (position, budget) pair with its own proof; a position can need several budgets.

| n | refuted | nodes | positions | of which White-mate nodes | written out as a tree | Black moves checked | search |
|---:|:---:|---:|---:|---:|---:|---:|---:|
| 1 | yes | 35 | 35 | 0 | 35 | 34 | 0.0 s |
| 2 | yes | 131 | 99 | 34 | 131 | 96 | 0.0 s |
| 3 | yes | 314 | 224 | 163 | 314 | 219 | 0.1 s |
| 4 | yes | 560 | 398 | 233 | 579 | 404 | 0.2 s |
| 5 | yes | 1,054 | 797 | 491 | 1,079 | 803 | 0.3 s |
| 6 | yes | 2,170 | 1,654 | 1,178 | 2,329 | 1,704 | 0.8 s |
| 7 | yes | 3,462 | 2,584 | 1,994 | 5,226 | 2,900 | 1.3 s |
| 8 | yes | 5,985 | 4,478 | 3,394 | 16,563 | 5,265 | 2.5 s |
| 9 | yes | 8,297 | 6,391 | 4,124 | 142,210 | 7,502 | 3.7 s |
| **10** | **yes** | **16,388** | **12,836** | **8,851** | **4,474,564** | **16,200** | **8.2 s** |
| 11 | **no** | | | | | | 7.1 s |

"Positions" counts distinct positions as python-chess writes them (en passant only when a capture
is legal); the Lean files distinguish en passant targets and add the position after each White
mating move, hence their 21,417 checkpoints. The n = 10 row is exactly the certificate proved in
Lean: its 8,851 White-mate nodes, and the closings below, match the generated theorems.

"Black moves checked" counts the moves listed at Black-to-move nodes, including those inside
White's forced-mate subproofs; each is one `decide +kernel` fact in Lean. How the White nodes
close at n = 10:

| closed by | count |
|---|---:|
| White mates in 1 | 2,149 |
| White mates in 2 | 354 |
| White mates in 3 | 250 |
| White mates in 4 | 202 |
| one White reply, Black refuted again | 614 |
| budget used up | 3,397 |

**n = 11 fails, as it must.** The search tries every White reply before giving up, so finding no
refutation at 11 matches the proved mate in 11.

**Two corrections.** The first version of this note (commit `fabab72`) reported 20,948 nodes and a
tree of 66,249 at n = 10. That search kept one proof per position and overwrote it when it later
proved a larger budget, so a stored proof could end up depending on itself, and the tree counts
were wrong; writing the certificate out as Lean exposed it (the generator recursed forever). The
search now keeps one proof per (position, budget), never changed, each referring only to proofs
finished before it, so the certificate is acyclic by construction. The second version (commit
`4a7880f`) measured all budgets with one Stockfish process, whose hash table carried hints from the
smaller budgets into n = 10 (21,756 nodes), so its n = 10 row described a different certificate
from the one `gen_bound.py` wrote and Lean proved. Each budget now starts Stockfish with an empty
hash table, and the table above matches the proved certificate. Both errors were in counting only;
neither touched the Lean proof.

## What the numbers say

* **The tree stays small because White is the one with the attack.** After almost any quiet Black
  move, White mates within one to four moves, which closes the branch with a small subproof. Only
  Black's checks keep a line alive, and there are few of them.
* **Repeated positions are what make it feasible.** At n = 10, proving each (position, budget)
  once instead of once per path cuts the certificate from 4,474,564 nodes as a tree to 16,388, a
  factor of about 270. The most shared nodes are White's mates in 1 with the knight on f6 and the
  queen on g6 (`…/p2p1NQp/4pP2/…/K3R3 w`), each reached from 11 to 14 different parents.
* **The first attempt shows why the search order matters.** Without the forced-mate shortcut, and
  with White trying checks first, White kept sacrificing its queen and rook, so Black got huge free
  subtrees. That version needed 872,826 positions at n = 8 and did not finish n = 9 in 14 minutes,
  about 100 times the size above.

## The proof in Lean

Proved on 2026-11-03, kernel only, standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem gotham_not_winsIn_ten : ¬ WinsIn .black 10 Puzzles.gotham
theorem gotham_mateIn : MateIn .black 11 Puzzles.gotham
theorem gotham_specMateIn : SpecMateIn .black 11 Puzzles.gotham   -- the rules alone (G8)
```

in `ChessDemoBound/GothamMateIn.lean`. The lower half is the generated certificate
`ChessDemoBound/Gotham10/`, written by `scripts/gen_bound.py` from the search above:

| | |
|---|---:|
| node theorems | 24,994 (571 Black-to-move refutations, 6,966 White escapes or closings, 8,851 White forced-mate moves, 8,606 Black-reply nodes inside them) |
| checkpoint positions | 21,417 |
| White-to-move closings | 3,397 budget used up, 614 one escape, 2,955 White's own forced mate |
| kernel facts | 6,762 checkmates, 2,415 full move lists, 24,436 `play` equations, 9,465 legality checks, 4,011 "not mated" |
| Lean files | 159 (moves, 11 checkpoint files, 146 node files grouped by height, the claim); 178 build jobs with the library modules |
| build | 46 min wall, 4.5 CPU-hours, peak 0.9 GB per process (`lake build ChessDemoBound`, 10 cores) |

Each node theorem uses the glue of `Chess.Game.Cert` (sections `PerNode` and `Bounds`, THEOREMS C3
and C8), `Game.Forces.mono` (3,229 times, to use a forced mate found with a smaller budget),
`mem_chess_moves`, literal facts about one position proved by `decide +kernel`, and side
conditions `k ≤ n` on numbers proved by plain `decide` (74 times). All of it is checked by the
kernel; there is no `native_decide`. The checkmate checks are the most expensive kind: about 1.0 s
each on an idle machine, so about 1.9 of the 4.5 CPU-hours (the 2.4 s timed earlier was under load).

To regenerate (about 30 s; needs python-chess, `lake build chess-perft`, and Stockfish, whose
version affects which valid certificate comes out):

```
python -I scripts/gen_bound.py --fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1" \
  --budget 10 --root Puzzles.gotham --module ChessDemoBound.Gotham10 --out ChessDemoBound/Gotham10 \
  --stockfish /opt/homebrew/bin/stockfish
```

**An outside check, not part of the proof.** Stockfish 19, asked about the root position on its
own (depth 20, 26, 32, and a `mate 10` search to depth 40, on 2026-11-03), reports mate in 11 with
1…Rxb2+ every time and finds no shorter mate. The proof does not depend on this; it is a
differential check that the proved distance matches the engine's.

## Cost in Lean (the estimate made before the proof)

The facts are of the same kinds as in `ChessDemo/GothamCert.lean`: a position's complete move
list, one `play` equation per move, and "checkmated" at mate leaves. Two measurements:

* `GothamCert.lean`, built clean on an unloaded machine: 964 `decide +kernel` facts in about
  160 s, so about 0.17 s per fact.
* Timed here while the search ran: the 34-move list of the Gotham position took about 2.3 s, and
  a `play` equation about 1 s each.

At n = 10 there are about 19.5k `play` facts and about 21k move-list or position facts, so about
40k kernel facts. At 0.17–1 s each, that is about 2 to 11 CPU hours. Split into files of a few
hundred theorems each, so `lake` builds them in parallel on 10 cores, that is roughly 15 minutes
to an hour and a half of build time. Memory per file stays like `GothamCert`'s (about 1 GB).

## Next steps

1. **Cheaper checkmate checks.** Measured on a typical mate leaf of the certificate (2026-11-03,
   unloaded machine): `Game.chess.Mated p` takes about 1.0 s in the kernel. Of that, listing the 79
   candidate moves takes 0.04 s, `InCheck` 0.1 s, and filtering the candidates through
   `PseudoLegal` about 0.7 s (about 9 ms per candidate): the generator decides each candidate
   against the rules themselves (`decide (PseudoLegal p m)`), by design, so that its correctness
   proof stays short. A faster filter that uses what geometry already guarantees (for a
   non-pawn candidate, only "the destination does not hold a piece of the mover's colour" is left
   to test) would roughly halve every move list and checkmate check, at the price of re-proving
   `PseudoLegal.mem_candidates`/`mem_pseudoMoves` for the new filter. The mate leaves also took about
   2.4 s each under the parallel build's load, so that figure, used in the estimate above, is
   pessimistic for an idle machine.
2. **Other puzzles.** `gen_bound.py` takes any FEN, root and budget.
