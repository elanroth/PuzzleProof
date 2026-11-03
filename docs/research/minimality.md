# Is 11 the minimum? The proof of "no mate within 10"

2026-11-02. Script: `scripts/measure_minimality.py`. Data: `docs/research/data/minimality-gotham.json`.

## The claim and its two halves

`MateIn .black 11 Puzzles.gotham` says Black mates in exactly 11. Its two halves need different
kinds of proof:

* **Black mates within 11** (`gotham_winsIn`, proved). This is an existence claim, so one good Black
  move per position is a complete proof. Stockfish's choice of that move is checked, never trusted.
* **Black does not mate within 10** (`gotham_not_winsIn_ten`, proved 2026-11-03). This is a
  claim about every possibility.
  At each Black turn, *every* legal Black move must be answered: either White escapes with one
  reply, or White forces mate itself. No engine choice can narrow the Black side.

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

Stockfish only does two things: it orders White's candidate replies, and it says where to try a
White forced mate. It cannot make anything pass, because a suggested reply is kept only if the
search then refutes every Black move after it. With no engine (`--stockfish` left out) the search
is the same, only slower.

Positions are shared: a position refuted with budget n is refuted for every smaller budget, so
the certificate is a DAG. One Lean theorem per DAG node would be enough.

## Results

All on this machine (10 cores, one Python process); times are the search only. A certificate node
is a (position, budget) pair with its own proof; a position can need several budgets.

| n | refuted | nodes | positions | of which White-mate nodes | written out as a tree | Black moves checked | search |
|---:|:---:|---:|---:|---:|---:|---:|---:|
| 1 | yes | 35 | 35 | 0 | 35 | 34 | 0.0 s |
| 2 | yes | 131 | 99 | 34 | 131 | 96 | 0.1 s |
| 3 | yes | 314 | 224 | 163 | 314 | 219 | 0.3 s |
| 4 | yes | 538 | 400 | 256 | 557 | 408 | 0.3 s |
| 5 | yes | 1,041 | 785 | 450 | 1,066 | 790 | 0.5 s |
| 6 | yes | 2,143 | 1,617 | 1,104 | 2,446 | 1,681 | 1.2 s |
| 7 | yes | 3,474 | 2,577 | 1,853 | 5,199 | 2,957 | 2.4 s |
| 8 | yes | 8,422 | 6,687 | 4,186 | 164,963 | 7,821 | 7.3 s |
| 9 | yes | 10,128 | 7,703 | 5,073 | 139,691 | 9,528 | 9.7 s |
| **10** | **yes** | **21,756** | **16,912** | **12,221** | **1,645,064** | **21,019** | **20.3 s** |
| 11 | **no** | | | | | | 17.9 s |

"Black moves checked" counts the moves listed at Black-to-move nodes, including those inside
White's forced-mate subproofs; each is one `decide +kernel` fact in Lean. How the White nodes
close at n = 10:

| closed by | count |
|---|---:|
| White mates in 1 | 2,796 |
| White mates in 2 | 546 |
| White mates in 3 | 409 |
| White mates in 4 | 213 |
| one White reply, Black refuted again | 751 |
| budget used up | 4,126 |

**n = 11 fails, as it must.** The search tries every White reply before giving up, so finding no
refutation at 11 matches the proved mate in 11.

**A correction.** The first version of this note (commit `fabab72`) reported 20,948 nodes and a
tree of 66,249 at n = 10. That search kept one proof per position and overwrote it when it later
proved a larger budget, so a stored proof could end up depending on itself, and the tree counts
were wrong. The search now keeps one proof per (position, budget), never changed, each referring
only to proofs finished before it, so the certificate is acyclic by construction. Writing the
certificate out as Lean exposed the bug: the generator recursed forever on the cyclic version.

## What the numbers say

* **The tree stays small because White is the one with the attack.** After almost any quiet Black
  move, White mates within one to four moves, which closes the branch with a small subproof. Only
  Black's checks keep a line alive, and there are few of them.
* **Repeated positions are what make it feasible.** At n = 10, proving each (position, budget)
  once instead of once per path cuts the certificate from 1,645,064 nodes as a tree to 21,756, a
  factor of 75. The most shared nodes are White's positions after the knight lands on c7
  (`…/2N…/…/2K4P/6R1 w`), each reached from 9 or 10 different parents.
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
| kernel facts | 6,762 checkmates, 2,415 full move lists, 24,421 `play` equations, 9,465 legality checks, 4,011 "not mated" |
| Lean files | 178 (moves, 11 checkpoint files, 165 node files grouped by height, the claim) |
| build | 46 min wall, 4.5 CPU-hours, peak 0.9 GB per process (`lake build ChessDemoBound`, 10 cores) |

Each node theorem uses only the glue of `Chess.Game.Cert` (sections `PerNode` and `Bounds`, THEOREMS
C3 and C8), `mem_chess_moves`, and literal facts proved by `decide +kernel`. The checkmate checks
are the most expensive kind (about 2.4 s each, more than half of the build).

To regenerate (about 30 s; needs python-chess, `lake build chess-perft`, and optionally Stockfish):

```
python -I scripts/gen_bound.py --fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1" \
  --budget 10 --root Puzzles.gotham --module ChessDemoBound.Gotham10 --out ChessDemoBound/Gotham10 \
  --stockfish /opt/homebrew/bin/stockfish
```

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

1. **Cheaper checkmate checks.** They are more than half of the kernel time.
2. **Other puzzles.** `gen_bound.py` takes any FEN, root and budget.
