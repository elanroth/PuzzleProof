# Specification of `ChessDemo.GothamCert` (generated)

Role: demo implementer (one overnight round, ROADMAP steps 6 and 7).
Date: 2026-11-02.
Status: Round 2 (2026-11-02, review of Round 1: the refutations gathered into their own theorem
`refutations`, from which `onlyWinningMove` is proved), matched to `ChessDemo/GothamCert.lean` as
`scripts/gen_cert.py` writes it (see `docs/process/ChessDemo.md`).

Library: `ChessDemo`. File: `ChessDemo/GothamCert.lean`, **generated**: do not edit it; regenerate
it with the command in `scripts/README.md`. Imports: `Chess.ChessGame.Fide` (for
`mem_chess_moves`) and `Chess.Puzzles`.

Nothing in this file needs to be trusted. Its claims (`winsIn`, `refutations`, `onlyWinningMove`)
are restated in `ChessDemo.Gotham`, and every proof in it is checked by the kernel.

## 0. How to read this document, and the docstring rule

The library's rule is that every definition carries the docstring of its spec word for word. A
generated file has about 1 100 declarations whose docstrings, where they have one, are produced by
the script from the position (its FEN) or the move (its SAN); the spec cannot quote them one by one.
This spec states instead **the shapes** the script emits (§1), word for word up to the names,
numbers, FEN strings and SAN that the script fills in, and the module docstring's template (§2).
The script is the single place where these texts are written (`scripts/gen_cert.py`, function
`header` and class `Generator`).

## 1. What the file contains, in order

1. The module docstring (§2).
2. `namespace ChessDemo.GothamCert`, `open Chess`.
3. **Moves.** One definition per move of the tree, named by its UCI writing, as a literal, without
   docstring: `def b7b2 : Move := ⟨⟨1, 6⟩, ⟨1, 1⟩, none⟩` (source and destination as
   `⟨file, rank⟩`, then the promotion choice). The headline reads `uci "b7b2"`; `ChessDemo.Gotham`
   proves the two equal (DG2).
4. **Checkpoints.** One position per node of the tree, `p0`, `p1`, …, each with its FEN (in this
   library's conventions) as docstring:
   ```lean
   /-- `2b2bk1/5rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PrP4P/1K4R1 w - - 0 1` -/
   def p1 : Position :=
     ⟨Board.unpack 0x0C90090007A00000400070075007200B3071000000100700100001A104000060, .white, .none,
         none⟩
   ```
   `p0` is the root itself; the claims are stated about `Puzzles.gotham`, so `p0` is used only by
   the script's `--check`.
5. **Nodes, children first.** One theorem per node, `w0`, `w1`, …, in three shapes (Game spec
   §4.1):
   - mate leaf, docstring "*Side* is checkmated.":
     `theorem wI : WinsIn a n pJ := Game.WinsIn.of_mated (by decide +kernel) (by decide +kernel)`
   - attacker node, docstring "*Side* to move plays *SAN*.":
     `Game.Forces.move_of_play_eq (by decide +kernel) (mem_chess_moves.2 (by decide +kernel))
     (by decide +kernel : pJ.play m = pK) wL`
   - defender node, docstring "*Side* to move, with the replies *SAN, …*.":
     `Game.Forces.replies_of_moves_eq (by decide +kernel) (by decide +kernel : Game.chess.moves pJ
     = [m₁, …]) <| Game.Forces.forall_mem_cons (Game.Forces.of_play_eq (by decide +kernel :
     pJ.play m₁ = pK₁) wL₁) <| … <| Game.Forces.forall_mem_nil`
   A node is identified by its position, attacker and budget; a transposition reached twice with
   the same budget is proved once.
6. **The certificate as data.** One `def cI : Cert Move` per node, mirroring `wI` (`.goal`,
   `.move m cJ`, `.replies [(m₁, cJ₁), …]`), and `def cert : OnlyMoveCert Move` with `next`, the
   win after `b7b2`, `refBudget := 5` and `refs`, the 33 refutations. No proof uses these values;
   they are what `checkOnlyMove` and `firstFailureOnlyMove` read (§3).
7. **The claims.** `play_best : Puzzles.gotham.play b7b2 = p1` (docstring "Playing `b7b2` (Rxb2+)
   at `Puzzles.gotham` gives the checkpoint `p1`."); `winsIn : WinsIn .black 11 Puzzles.gotham`
   (docstring "`Puzzles.gotham`: Black mates within 11."); one
   `refutes_<uci> : WinsIn .white k (Puzzles.gotham.play <uci>)` per alternative (docstring "After
   `<uci>` (*SAN*), White mates within *k*."); `moves_root : Game.chess.moves Puzzles.gotham =
   [c3b2, …]` (docstring "The moves available at `Puzzles.gotham`, in the order of
   `legalMoves`."), the 34 root moves, by `decide +kernel`; `refutations : ∀ m ∈ Game.chess.moves
   Puzzles.gotham, m ≠ b7b2 → ∃ k, WinsIn .white k (Puzzles.gotham.play m)` (docstring
   "`Puzzles.gotham`: after every move other than `b7b2`, White forces mate."), by
   `rw [moves_root]` and the walk over the list: `refuted_cons` for each alternative,
   `refuted_cons_self` at `b7b2` and `refuted_nil`; and `onlyWinningMove : OnlyWinningMove
   Puzzles.gotham b7b2` (docstring "`Puzzles.gotham`: `b7b2` is the only winning move."), by
   `Game.OnlyWinningMove.of_moves_eq (by decide +kernel) moves_root (by decide +kernel)
   (Game.Forces.of_play_eq play_best w60) (moves_root ▸ refutations)` (Game spec §4.1,
   L4.19–L4.22). Round 1 proved `onlyWinningMove` with the walk inline; Round 2 gives the
   refutations their own theorem because they say more than `OnlyWinningMove` (a forced mate,
   not only "Black does not win"), and `ChessDemo.gotham_refuted` restates them.

## 2. The module docstring (template)

```
# Generated certificate: ChessDemo.GothamCert

Generated by `scripts/gen_cert.py` (do not edit; regenerate) for the claim that in
`Puzzles.gotham`, the position with FEN
`2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1`,
`b7b2` is the only winning move and the side to move mates within 11.

The engine was Stockfish 19, with python-chess 1.11.2; neither is trusted. Every fact
below is checked by the kernel (`decide +kernel`), one move list, one move or one checkpoint at a
time.

Nodes: 159 attacker, 36 defender and 124 mate leaves; 314 positions.

## Contents

* One `Move` per move of the tree, named by its UCI writing.
* The checkpoints `p<i>`: each position of the tree as a literal, in this library's conventions.
* The theorems `w<i>`, one per node, children first: what the node claims, proved from its
  children with the glue lemmas of `Chess.Game.Cert`.
* The certificate as data: `c<i>` per node, and `cert` for the claim (for `firstFailureWin`,
  `firstFailureOnlyMove` and `checkWin`/`checkOnlyMove`).
* The claims `winsIn` (and, for an only-move claim, `moves_root`, `refutations` and
  `onlyWinningMove`), about `Puzzles.gotham`.
```

## 3. Size and cost

319 node theorems (159 attacker nodes, 36 defender nodes, 124 mate leaves), 314 checkpoints, 81
moves, 33 refutations (30 mates in 1, two in 2, one in 5), about 4 000 lines. The prototype's tree
(`prototype`) had 320 nodes.

Kernel cost, `lake build ChessDemo.GothamCert`, sequential elaboration (the lakefile sets
`Elab.async = false` for `ChessDemo`): **165 s, 1.13 GB peak** (2026-11-02, this machine, under
swap pressure from other processes). With parallel elaboration: 179 s and 3.1 GB. The prototype
needed about 80 s and 6 GB with its packed `Nat` board.

Per node kind (15 nodes of each kind sampled from this file, `decide +kernel`, sequential):

| Fact decided | Before (ROADMAP step 5) | After (step 6) |
|---|---|---|
| `Legal p m` (attacker node) | 0.12 s | 0.09 s |
| `m ∈ legalMoves p` (not used here) | 1.5 s | 0.47 s |
| `p.play m = pK` (checkpoint) | 0.11 s | 0.04 s |
| `Game.chess.moves p = […]` (defender node) | 2.0 s | 0.72 s |
| `Game.chess.Mated p` (mate leaf) | 2.0 s | 0.68 s |

"Before" is this library as of ROADMAP step 5; "after" adds `kingSafeAfter` (MoveGen spec D3.4) and
the `match` form of `Piece.ofCode` (Position spec D2.2). The whole file took about 430 s and
4.3 GB before (an early version of the file, whose only-move root then failed for an unrelated
reason, §4).

## 4. Elaboration pitfalls met while generating (and how the shapes avoid them)

- One theorem holding all 34 root checkpoints ran out of heartbeats: each alternative now has its
  own `refutes_<uci>` theorem.
- `(by decide +kernel : legalMoves p = […])` and `mem_legalMoves.2 …` made the elaborator unfold and
  evaluate `legalMoves p` during unification (heartbeat timeouts at `whnf` on positions with many
  moves): the shapes use `Game.chess.moves p` and `mem_chess_moves`, which match the glue lemmas'
  hypotheses syntactically (Game spec §4.1).
