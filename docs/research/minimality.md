# Is 11 the minimum? Measuring the proof of "no mate within 10"

2026-11-02. Script: `scripts/measure_minimality.py`. Data: `docs/research/data/minimality-gotham.json`.

## The claim and its two halves

`MateIn .black 11 Puzzles.gotham` says Black mates in exactly 11. Its two halves need different
kinds of proof:

* **Black mates within 11** (`gotham_winsIn`, proved). This is an existence claim, so one good Black
  move per position is a complete proof. Stockfish's choice of that move is checked, never trusted.
* **Black does not mate within 10** (not yet proved). This is a claim about every possibility.
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

All on this machine (10 cores, one Python process); times are the search only.

| n | refuted | DAG nodes | of which White-mate nodes | written as a tree | Black moves checked | search |
|---:|:---:|---:|---:|---:|---:|---:|
| 1 | yes | 35 | 0 | 35 | 34 | 0.0 s |
| 2 | yes | 131 | 34 | 131 | 96 | 0.2 s |
| 3 | yes | 314 | 163 | 314 | 219 | 0.3 s |
| 4 | yes | 538 | 256 | 555 | 408 | 0.4 s |
| 5 | yes | 1,041 | 450 | 1,064 | 790 | 0.9 s |
| 6 | yes | 2,143 | 1,104 | 2,248 | 1,681 | 1.5 s |
| 7 | yes | 3,412 | 1,853 | 3,798 | 2,891 | 2.6 s |
| 8 | yes | 8,215 | 4,180 | 11,500 | 7,489 | 8.1 s |
| 9 | yes | 9,759 | 5,073 | 11,883 | 8,852 | 10.1 s |
| **10** | **yes** | **20,948** | **12,217** | **66,249** | **19,543** | **21.6 s** |
| 11 | **no** | | | | | 18.3 s |

"Black moves checked" counts the moves listed at Black-to-move nodes, including those inside
White's forced-mate subproofs. Each is one `decide +kernel` fact in Lean (the move is played and
gives the next checkpoint). How the White nodes close at n = 10:

| closed by | count |
|---|---:|
| White mates in 1 | 2,796 |
| White mates in 2 | 546 |
| White mates in 3 | 409 |
| White mates in 4 | 213 |
| one White reply, Black refuted again | 694 |
| budget used up | 3,441 |

**n = 11 fails, as it must.** The search tries every White reply before giving up, so finding no
refutation at 11 matches the proved mate in 11. Together with n = 10 succeeding, this is the
search's own evidence that 11 is exactly the minimum. It is evidence, not proof, until Lean
checks the n = 10 certificate.

## What the numbers say

* **The tree stays small because White is the one with the attack.** After almost any quiet Black
  move, White mates within one to four moves, which closes the branch with a small subproof. Only
  Black's checks keep a line alive, and there are few of them.
* **Repeated positions matter at depth.** At n = 10, sharing positions cuts the certificate from
  66,249 nodes as a tree to 20,948 as a DAG, a factor of 3.2. The most shared nodes are White's
  forced mates after the knight lands on c7 (`…/2N…/…/2K4P/6R1 w`), each reached from 9 different
  parents. Collecting such recurring endings first, and proving each once, is the obvious next
  saving.
* **The first attempt shows why the search order matters.** Without the forced-mate shortcut, and
  with White trying checks first, White kept sacrificing its queen and rook, so Black got huge free
  subtrees. That version needed 872,826 positions at n = 8 and did not finish n = 9 in 14 minutes,
  about 100 times the size above.

## Cost in Lean (estimate)

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

1. **Certificate type.** Add to `Chess.Game` a certificate for `¬ WinsIn a n p`: attacker nodes
   list every move, and defender nodes give one reply or a forced win for the defender. Prove its
   checker sound, as for `Cert`.
2. **Generator.** Extend `scripts/gen_cert.py` (or a sibling) to write that certificate as
   per-node theorems over shared checkpoints, split across files.
3. **Headline.** Prove `gotham_mateIn : MateIn .black 11 Puzzles.gotham` and its reading with the
   rules alone, kernel only.
4. **Repeats first.** Prove the most-shared White forced mates once, as lemmas, before the rest.
