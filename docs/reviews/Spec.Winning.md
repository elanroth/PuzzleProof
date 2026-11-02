# File-level review: `Chess.Spec.Winning` (and `Chess.ChessGame.Fide`)

Reviewer role: demo implementer, as the gate ROADMAP step 7 puts before the demo's headline is
stated. Date: 2026-11-02.
Read: `Chess/Spec/Winning.lean` (whole file), `docs/spec/Spec.Winning.md`,
`docs/process/Spec.Winning.md`, `Chess/ChessGame/Fide.lean` (whole file), `Chess/Game/Defs.lean`
(`Forces`, `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`), `Chess/Rules.lean` (`Legal`,
`Checkmate`, `Stalemate`, `Position.play`), and the FIDE Laws of Chess (1 January 2023) articles
1.2, 1.4, 3.9, 5.1, 5.2, 9.2, 9.3 and 9.6.

This is a short review by the same session that wrote the demo, not an independent one; an
independent reviewer should still read this file against FIDE. No file was changed by it.

## 1. Verdict

`Spec/Winning` says what its docstrings say, and its docstrings say what FIDE means by "forcing
checkmate", with the departures the docstrings themselves name (no move-count, repetition or
dead-position rule). Rule for rule it is `Game.Forces` with `legalMoves` replaced by `Legal` and
`Mated` by `Checkmate`, which is exactly what G8 (`forces_iff_specForces`) proves; nothing in it
depends on the generator or on `Chess.Game`. No change is needed before the Gotham headline is
stated through it (`ChessDemo.gotham_specWinsIn`, `gotham_specOnlyWinningMove`).

## 2. Rule by rule

| `SpecForces` rule | FIDE | `Game.Forces` | Remark |
|---|---|---|---|
| `goal`: `T p` | — | `goal` | The target is tested at every position, the root included. |
| `move`: `p.turn = a`, `Legal p m`, forced after `m` within `n`, gives `n + 1` | 1.2, 3.9: a move is legal when it obeys Article 3 and does not leave the mover's king attacked | `move` with `m ∈ moves x` | `Legal` is Rules D6.1: `PseudoLegal` and no own king attacked after the move (FIDE 3.9.2). |
| `replies`: `p.turn = a.other`, `∃ m, Legal p m`, every legal reply forced within `n` | 5.2.1: a player with no legal move who is not in check is stalemated, and the game is drawn | `replies` with `moves x ≠ []` | The guard is what makes a stalemated defender escape; `not_specWins_of_stalemate` checks it. |

`SpecWinsIn`'s target is "the other side is to move and `Checkmate`". FIDE 1.4.2 / 5.1.1: the
game is won by the player who has checkmated the opponent's king, checkmate being "the king is in
check and the opponent has no legal move"; Rules' `Checkmate` is `InCheck p ∧ ∀ m, ¬ Legal p m`
(FIDE 3.9.1 for check). The conjunct `q.turn = a.other` is needed: without it, `a` itself being
mated would count. `specWinsIn_zero_iff` checks that budget 0 is exactly "already won".

`SpecWins` (some budget fixed in advance), `SpecMateIn` (within `n`, not within fewer) and
`SpecOnlyWinningMove` (legal, wins after it, and after every other legal move does not) read as
their docstrings say. `SpecOnlyWinningMove` compares move values, so two promotions are two moves;
the docstring says so.

## 3. Concerns

### C1 (low, recorded). The draw rules that are left out, and why they rarely matter

- **Dead position (FIDE 5.2.2)** ends the game when no sequence of legal moves leads to checkmate.
  Every position of a forced-win tree has a sequence that leads to checkmate, so no position on a
  `SpecWinsIn` line is dead: leaving this rule out changes nothing for `SpecWinsIn` and
  `SpecWins`. (It would matter for draw claims of later stages.)
- **Fifty- and seventy-five-move rules (9.3, 9.6.2)** and **repetition (9.2, 9.6.1)** are not
  modelled: a position records no clocks or history (DESIGN §4.6). A `SpecWinsIn n` win is at most
  `2n` plies long. For the Gotham claim (at most 21 plies) the first move, `1...Rxb2+`, is a
  capture, so the count of moves without capture or pawn move restarts there, and the 20 plies
  after it reach neither the 100 of a fifty-move claim (9.3) nor the 150 of 9.6.2; a repetition
  could occur only on a line where the attacker repeats, which a minimal certificate does not do,
  but nothing proves that of this one. THEOREMS G15 states the general corollary; it is not
  proved.

### C2 (low). Positions no game reaches

`Legal` is total and on boards with two kings or none it admits odd moves (MoveGen spec D3.5).
`SpecWinsIn` inherits that. A headline stated about a `fen "…"` position starts from a position
that `Position.Sane` accepts (one king each, the side not to move not in check), and every legal
move keeps that, so the odd cases are not reached; but "every legal move keeps it" is R9/R10
(Stage 2), not yet proved. Until then the statement is exactly as strong as written, over all
positions reached by `Legal` moves.

### C3 (low, owner decision still open). The en passant convention

`Position.play` sets the en passant target after every two-square advance (Rules review C4). This
does not change which moves are `Legal` (an en passant capture also needs a pawn to make it), so
it does not change `SpecWinsIn`; it only makes positions differ from FIDE's notion of "same
position" for repetition, which is not modelled (C1). The generated checkpoints follow the
library's convention (`scripts/gen_cert.py`). The owner's sign-off on the convention was due at
step 7 and is still open.

## 4. `Chess.ChessGame.Fide`

Proofs only, from `mem_legalMoves` (M4) and `checkmate_iff` (M6); nothing in it is trusted. Since
ROADMAP step 6 these go through `kingSafeAfter_iff` (MoveGen Round 5), and the file did not
change. `mem_chess_moves` is now also part of the generated-file interface (Game spec §4.3),
because its statement matches the attacker-node glue syntactically.
