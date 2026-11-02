import Chess.Game.Defs
import Chess.Game.Laws
import Chess.Game.Search
import Chess.Game.Cert
import Chess.Game.Examples

/-!
# Game

Two-player games with alternating turns, forced play into a target, forced wins, a bounded search
that decides them, and a certificate checker whose acceptance proves them. Chess is one instance
(`Chess.ChessGame`); nothing here mentions a piece. This file imports the five files of the
module, which follow the trust boundary. Specification: `docs/spec/Game.md`; every definition
carries the docstring given there.

## Main definitions

* `Game`, `Game.Forces`, `Game.WinsIn`, `Game.Wins`, `Game.MateIn`, `Game.OnlyWinningMove`: games,
  forcing and winning (`Chess.Game.Defs`).
* `Game.searchForces`: bounded search, by structural recursion on the budget
  (`Chess.Game.Search`).
* `Cert`, `OnlyMoveCert`, `Game.checkWin`, `Game.checkOnlyMove`: certificates proposed by an
  untrusted search, and their checkers; `Game.firstFailure` and its variants say where a rejected
  certificate fails (`Chess.Game.Cert`).

## Main statements

* The laws G2–G4, G6, O2 and O8 (`Chess.Game.Laws`).
* `searchForces_iff` (G5): the search decides forcing.
* `checkWin_sound`, `checkOnlyMove_sound` (C1, C7), and the glue for proofs that check one node at
  a time (C3).

## Implementation notes

* Only `Chess.Game.Defs` is trusted. `Chess.Game.Laws` proves facts about its definitions;
  `Chess.Game.Search` and `Chess.Game.Cert` are executable, each with a soundness theorem, and
  import `Laws` but not each other; `Chess.Game.Examples` holds two toy games and the tests.
* `Chess.Game.Cert` is the interface of generated certificate files; its module docstring says
  which names they may use.
-/
