import Chess.ChessGame
import Chess.Spec.Winning

/-!
# Fide

The chess game means chess under FIDE's rules of movement and checkmate (THEOREMS G8). The four
notions of `Chess.ChessGame`, which are computed through the move generator and `Chess.Game`, are
equivalent to those of `Chess.Spec.Winning`, which are written with `Legal`, `Position.play` and
`Checkmate` alone. Specification: `docs/spec/ChessGame.Fide.md`; every theorem below carries the
docstring given there.

## Main statements

* `mem_chess_moves`, `chess_mated_iff_checkmate`: the moves available in `Game.chess` are the legal
  moves, and being mated there is checkmate.
* `forces_iff_specForces`: forcing in the chess game is forcing under the FIDE rules, for every
  target.
* `winsIn_iff_specWinsIn` (THEOREMS G8), `wins_iff_specWins`, `mateIn_iff_specMateIn`,
  `onlyWinningMove_iff_specOnlyWinningMove`: the headline vocabulary means FIDE chess.

## Implementation notes

* Nothing here is trusted. With these equivalences, a reader of a headline such as
  `WinsIn .black 11 (fen "…")` may read it as `SpecWinsIn .black 11 (fen "…")`, so the move
  generator and `Chess.Game` leave the trusted base: what remains is `Chess.Rules` (with `Basic` and
  `Position` below it), `Chess.Spec.Winning`, and the notation of `Chess.ChessGame`.
* The only facts used about the generator are `mem_legalMoves` and `checkmate_iff` (M4, M6).
* This file is kept apart from `Chess.ChessGame` (ChessGame review C2) so that the trusted
  definitions it targets, in `Chess.Spec.Winning`, import only `Chess.Rules`. Generated chess
  certificate files do import it, for `mem_chess_moves` at attacker nodes (Game spec §4.1, §4.3),
  so they rebuild when it changes; since `mem_chess_moves` is `mem_legalMoves`, this adds nothing
  to trust.
-/

namespace Chess

/-! ## The chess game is FIDE chess -/

section Fide

variable {a : Color} {n : Nat} {p : Position} {m : Move}

/-- The moves available in chess are exactly the legal moves. -/
theorem mem_chess_moves : m ∈ Game.chess.moves p ↔ Legal p m :=
  mem_legalMoves

/-- In chess, being mated is FIDE checkmate. -/
theorem chess_mated_iff_checkmate : Game.chess.Mated p ↔ Checkmate p :=
  checkmate_iff.symm

/-- Forcing in the chess game is forcing in FIDE chess, for every target. -/
theorem forces_iff_specForces {T : Position → Prop} :
    Game.chess.Forces a T n p ↔ SpecForces a T n p := by
  constructor
  · intro w
    -- `induction` on `w` needs its state to have the type `Game.chess.State` as written, not
    -- `Position` (it fails with "Internal error in mkElimApp" otherwise), so restate `p` first.
    obtain ⟨x, rfl⟩ : ∃ x : Game.chess.State, x = p := ⟨p, rfl⟩
    induction w with
    | goal h => exact .goal h
    | move m ht hm _ ih => exact .move m ht (mem_chess_moves.1 hm) ih
    | replies ht hne _ ih =>
      obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
      exact .replies ht ⟨m, mem_chess_moves.1 hm⟩ fun m hm => ih m (mem_chess_moves.2 hm)
  · intro w
    induction w with
    | goal h => exact .goal h
    | move m ht hm _ ih => exact .move m ht (mem_chess_moves.2 hm) ih
    | replies ht hl _ ih =>
      obtain ⟨m, hm⟩ := hl
      exact .replies ht (List.ne_nil_of_mem (mem_chess_moves.2 hm))
        fun m hm => ih m (mem_chess_moves.1 hm)

/-- `WinsIn` is `SpecWinsIn`: a win in the chess game is a forced checkmate under the FIDE rules.
(THEOREMS G8.) -/
theorem winsIn_iff_specWinsIn : WinsIn a n p ↔ SpecWinsIn a n p := by
  have hT : Game.chess.DefenderMated a = fun q => q.turn = a.other ∧ Checkmate q :=
    funext fun _ => propext (and_congr_right fun _ => chess_mated_iff_checkmate)
  rw [WinsIn, Game.WinsIn, hT]
  exact forces_iff_specForces

/-- `Wins` is `SpecWins`. -/
theorem wins_iff_specWins : Wins a p ↔ SpecWins a p :=
  exists_congr fun _ => winsIn_iff_specWinsIn

/-- `MateIn` is `SpecMateIn`: mate in exactly `n` in the chess game is mate in exactly `n` under
the FIDE rules. -/
theorem mateIn_iff_specMateIn : MateIn a n p ↔ SpecMateIn a n p :=
  and_congr winsIn_iff_specWinsIn
    (forall_congr' fun _ => imp_congr_right fun _ => not_congr winsIn_iff_specWinsIn)

/-- `OnlyWinningMove` is `SpecOnlyWinningMove`. -/
theorem onlyWinningMove_iff_specOnlyWinningMove :
    OnlyWinningMove p m ↔ SpecOnlyWinningMove p m :=
  and_congr mem_chess_moves <| and_congr wins_iff_specWins <|
    forall_congr' fun _ => imp_congr mem_chess_moves <|
      imp_congr_right fun _ => not_congr wins_iff_specWins

end Fide

/-! ## Tests

The tests of this module are in `ChessTest/ChessGame/Fide.lean` (`lake build ChessTest`). -/

end Chess
