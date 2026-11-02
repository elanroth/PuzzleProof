# Specification of the interface ledger (`ChessTest.Interface`)

Role: overnight implementer (ROADMAP step 5).
Date: 2026-11-02.
Status: Round 2, matched to `ChessTest/Interface.lean` (see `docs/process/ChessTest.md`, Rounds 3
and 4).

Library: `ChessTest` (`lake build ChessTest`, or `lake build ChessTest.Interface` alone). One file,
which defines nothing and imports `Chess`.

## 1. What it does

`docs/spec/Game.md` §4.3 freezes the interface of generated certificate files: the names they may
use, with their argument orders. This file records the signature of each such name with
`#guard_msgs`, so that a change to a name, to the order, kind or name of an argument, or to a field
of a certificate type fails the build of the test library. A generated file that has not been
regenerated would otherwise break only when it is next built, possibly long after the change.

Each entry is the expected output above the command:

```lean
/--
info: Chess.Game.checkWin (G : Chess.Game) (a : Chess.Color) (n : Nat) (x : G.State)
  (c : Chess.Cert G.Move) : Bool
-/
#guard_msgs (whitespace := lax) in #check Chess.Game.checkWin
```

- Functions and theorems are recorded with `#check` on the bare name, which prints the binder
  names and kinds (explicit, implicit, instance). Binder names matter: a generated file may pass
  an argument by name (`Game.checkWin_sound (c := …)`, as `ChessTest/ChessGame.lean` does).
- The certificate types (`Cert`, `OnlyMoveCert`, `Cert.Rejection`) are recorded with `#print`,
  which lists the constructors or fields in order.
- Names are written in full (no `open`), so the output does not depend on which namespaces are
  open.
- As in the axioms ledger, an expected message with a line over 100 characters is wrapped at a
  binder and compared with `#guard_msgs (whitespace := lax)`, which ignores line breaks but not the
  text. The expected messages were produced by running each command and wrapping its output by
  script, not typed by hand.

Checked (2026-11-02, scratch copy): renaming the field `refBudget` in the expected output of
`#print Chess.OnlyMoveCert`, or the binder `c` of `checkWin`, makes the file fail with one error
each. Round 2, the same check on the new entries: renaming the binder `t` of
`Forces.forall_mem_cons`, or changing the expected type of `Game.chess`, gives one error each.

## 2. What it lists (30 entries)

- Certificates (data): `Cert`, `OnlyMoveCert`.
- Checkers and their soundness: `Game.checkWin`, `Game.checkOnlyMove`, `Game.checkWin_sound`,
  `Game.checkOnlyMove_sound`.
- Glue for per-node proofs: `Game.Forces.of_play_eq`, `Game.Forces.move_of_play_eq`,
  `Game.Forces.replies_of_moves_eq`, `Game.Forces.forall_mem_nil` and
  `Game.Forces.forall_mem_cons` (since Round 2), `Game.WinsIn.of_mated`,
  `Game.OnlyWinningMove.of_refuted`, and since ROADMAP step 7 the only-move root
  `Game.OnlyWinningMove.of_moves_eq`, `refuted_nil`, `refuted_cons_self`, `refuted_cons`.
- Diagnostics (called by the generator after a rejection, by `#eval`): `Cert.Rejection`,
  `Game.firstFailureWin`, `Game.firstFailureOnlyMove`.
- Chess vocabulary of generated files: `Game.chess` (since Round 2), `WinsIn`,
  `OnlyWinningMove`, `legalMoves`, `Position.play`, `mem_legalMoves`, `fen`, `uci`,
  `Puzzles.gotham`, and since ROADMAP step 7 `mem_chess_moves` (which generated files use at
  attacker nodes instead of `mem_legalMoves`, Game spec §4.1).

Not listed: `Game.checkForces` and `Game.firstFailure` (generated files use the `Win` forms), the
constructors of `Forces` (which generated files must not use), and the fields of the chess game.
Generated files name `Game.chess` itself when they call a checker or a diagnostic
(`Game.chess.checkOnlyMove 11 gotham (uci "b7b2") {…}`, `Game.chess.firstFailureWin …`), so its
name and type are recorded; what its fields unfold to is fixed by `Chess.ChessGame` and its spec,
not by this ledger.

## 3. Design choices

1. **Text, not a type ascription.** An `example : @checkWin = (fun G a n x c => …)` would check
   types but not binder names, which named arguments depend on. `#check` output shows both.
2. **A deliberate change edits this file.** The file is a ledger, not a lock: changing the
   interface is allowed, and the change then shows in the diff of this file and is logged in
   `docs/process/Game.md`, so the generator (`scripts/`, ROADMAP step 7) is updated in the same
   change.
