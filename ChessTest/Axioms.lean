import Chess
import ChessTest.Tabulate

/-!
# The axioms ledger

`#print axioms` on every headline theorem of the library, so that the trust labels of DESIGN §7.3
and THEOREMS §0.4 are checked on every build of the test library, not claimed. Specification:
`docs/spec/ChessTest.Axioms.md`.

Each entry is `#guard_msgs in #print axioms X` under the expected output, so the build fails if a
theorem comes to depend on a different set of axioms: a new `sorry` shows as `sorryAx`, a
`native_decide` as `Lean.ofReduceBool`, and an added `axiom` by its name. Every theorem listed is
[kernel]: its axioms are among `propext`, `Classical.choice` and `Quot.sound`.

## Implementation notes

* The list is every theorem and instance named in the "Main statements" of a module's docstring
  (a group mentioned without naming its members is represented by its named members), the
  headline items of ROADMAP §1, the ★ items of THEOREMS that are proved, the two generator-backed
  `Decidable` instances that kernel checks of `Checkmate` and `Stalemate` run through, and
  `Position.tabulate_eq` of the test library. The entries of the kernel perft counts are in
  `ChessTest.AxiomsPerft`, so that this file imports no perft check and can be checked without
  building one.
* A theorem that uses fewer axioms than before also fails its entry; update the expected line then.
  Only a change that adds an axiom outside the three is a change of trust label.
* An expected line too long for one source line is wrapped, and its entry compares with
  `(whitespace := lax)`, which ignores the line break but not the text (checked: a wrapped entry
  with a wrong axiom list fails).
-/

/-! ### Chess.Basic (R1, R2, geometry) -/

/-- info: 'Chess.Square.ofIndex_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Square.ofIndex_index
/-- info: 'Chess.Square.index_ofIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Square.index_ofIndex
/-- info: 'Chess.Color.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Color.mem_all
/-- info: 'Chess.Color.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Color.all_nodup
/-- info: 'Chess.Kind.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Kind.mem_all
/-- info: 'Chess.Kind.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Kind.all_nodup
/-- info: 'Chess.PromoKind.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.PromoKind.mem_all
/-- info: 'Chess.PromoKind.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.PromoKind.all_nodup
/-- info: 'Chess.Piece.mem_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Piece.mem_all
/-- info: 'Chess.Piece.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Piece.all_nodup
/-- info: 'Chess.Square.mem_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Square.mem_all
/-- info: 'Chess.Square.all_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Square.all_nodup
/-- info: 'Chess.Direction.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Direction.mem_all
/-- info: 'Chess.Direction.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Direction.all_nodup
/-- info: 'Chess.Wing.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Wing.mem_all
/-- info: 'Chess.Wing.all_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Wing.all_nodup
/--
info: 'Chess.Square.offset_eq_some_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Square.offset_eq_some_iff
/-- info: 'Chess.Square.mem_ray_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.Square.mem_ray_iff
/-- info: 'Chess.shift_kingHome_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.shift_kingHome_two
/-- info: 'Chess.shift_kingHome_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.shift_kingHome_one

/-! ### Chess.Position (boards, packing, castling rights) -/

/-- info: 'Chess.Board.set_same' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Board.set_same
/-- info: 'Chess.Board.set_ne' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Board.set_ne
/-- info: 'Chess.Board.set_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Board.set_comm
/-- info: 'Chess.Board.unpack_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Board.unpack_pack
/-- info: 'Chess.Board.initial_kingHome' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Board.initial_kingHome
/-- info: 'Chess.Board.initial_rookHome' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Board.initial_rookHome
/-- info: 'Chess.Board.initial_flip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Board.initial_flip
/-- info: 'Chess.CastlingRights.get_revoke' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.CastlingRights.get_revoke
/-- info: 'Chess.CastlingRights.get_revokeAll' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.CastlingRights.get_revokeAll
/-- info: 'Chess.CastlingRights.revoke_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.CastlingRights.revoke_le
/-- info: 'Chess.CastlingRights.revokeAll_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.CastlingRights.revokeAll_le
/-- info: 'Chess.CastlingRights.get_ofGet' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.CastlingRights.get_ofGet

/-! ### Chess.Rules (R3, R4, R5, R8, R11, attack geometry, shape bridges, L4.11) -/

/-- info: 'Chess.play_board_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_of_not_mem
/-- info: 'Chess.play_board_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_src
/-- info: 'Chess.play_board_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_dst
/-- info: 'Chess.play_board_epVictim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_epVictim
/-- info: 'Chess.play_board_rookHome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_rookHome
/-- info: 'Chess.play_board_rookCastleSquare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_board_rookCastleSquare
/-- info: 'Chess.play_turn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.play_turn
/-- info: 'Chess.castling_play_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.castling_play_le
/--
info: 'Chess.PseudoLegal.isLight_dst_iff_of_bishop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.isLight_dst_iff_of_bishop
/--
info: 'Chess.PseudoLegal.isLight_dst_iff_of_knight' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.isLight_dst_iff_of_knight
/--
info: 'Chess.PseudoLegal.promo_ne_none_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.promo_ne_none_iff
/-- info: 'Chess.checkmate_or_stalemate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.checkmate_or_stalemate
/-- info: 'Chess.not_checkmate_and_stalemate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.not_checkmate_and_stalemate
/-- info: 'Chess.reaches_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_congr
/-- info: 'Chess.reaches_set_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_set_src
/-- info: 'Chess.reaches_set_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_set_dst
/-- info: 'Chess.Slides.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.Slides.symm
/-- info: 'Chess.slides_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.slides_symm
/-- info: 'Chess.Board.attackedBy_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Board.attackedBy_iff
/-- info: 'Chess.reaches_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_symm
/-- info: 'Chess.reaches_pawn_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_pawn_symm
/--
info: 'Chess.Board.attackedBy_iff_superpiece' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Board.attackedBy_iff_superpiece
/--
info: 'Chess.PseudoLegal.isEnPassant_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.isEnPassant_iff
/-- info: 'Chess.PseudoLegal.isCastle_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.PseudoLegal.isCastle_iff
/--
info: 'Chess.PseudoLegal.isDoublePush_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.isDoublePush_iff
/-- info: 'Chess.PseudoLegal.attacksFrom_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.PseudoLegal.attacksFrom_dst
/--
info: 'Chess.PseudoLegal.touched_nodup' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.touched_nodup
/-- info: 'Chess.reaches_of_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.reaches_of_clear
/--
info: 'Chess.CastleMove.legal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.CastleMove.legal_iff
/-- info: 'Chess.CastleMove.play_board_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.CastleMove.play_board_of_ne
/--
info: 'Chess.CastleMove.play_board_kingHome' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.CastleMove.play_board_kingHome
/--
info: 'Chess.CastleMove.play_board_kingCastleSquare' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.CastleMove.play_board_kingCastleSquare
/-- info: 'Chess.CastleMove.play_board_rookCastleSquare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.CastleMove.play_board_rookCastleSquare

/-! ### Chess.MoveGen (M1, M2, M3, M4, M6, perft, agreement) -/

/-- info: 'Chess.mem_slideTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_slideTargets
/-- info: 'Chess.mem_reachTargets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_reachTargets
/--
info: 'Chess.legalMoves_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Chess.legalMoves_eq_filter
/--
info: 'Chess.Board.superpieceAttackedBy_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Board.superpieceAttackedBy_iff
/-- info: 'Chess.kingSafeAfter_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.kingSafeAfter_iff
/-- info: 'Chess.legalMoves_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.legalMoves_sound
/--
info: 'Chess.PseudoLegal.mem_candidates' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.PseudoLegal.mem_candidates
/-- info: 'Chess.mem_pseudoMoves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_pseudoMoves
/-- info: 'Chess.legalMoves_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.legalMoves_complete
/-- info: 'Chess.mem_legalMoves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_legalMoves
/-- info: 'Chess.mem_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_lines
/-- info: 'Chess.lines_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.lines_nodup
/--
info: 'Chess.perft_eq_length_of_mem_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.perft_eq_length_of_mem_iff
/-- info: 'Chess.perft_eq_length_lines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_eq_length_lines
/-- info: 'Chess.legalMoves_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.legalMoves_nodup
/-- info: 'Chess.checkmate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.checkmate_iff
/-- info: 'Chess.stalemate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.stalemate_iff
/--
info: 'Chess.Checkmate.decidableByGen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Checkmate.decidableByGen
/--
info: 'Chess.Stalemate.decidableByGen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Stalemate.decidableByGen
/-- info: 'Chess.candidates_ignores_epTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.candidates_ignores_epTarget
/-- info: 'Chess.perft_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_one
/-- info: 'Chess.sum_perftDivide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.sum_perftDivide
/--
info: 'Chess.mem_legalMoves_of_agreesWithLegal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.mem_legalMoves_of_agreesWithLegal
/-- info: 'Chess.nodup_legalMoves_of_agreesWithLegal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.nodup_legalMoves_of_agreesWithLegal

/-! ### Chess.Game (G2–G6, O2, O8, C1–C3, C7) -/

/-- info: 'Chess.Game.winsIn_zero_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.winsIn_zero_iff
/-- info: 'Chess.Game.not_wins_of_stalemate' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.not_wins_of_stalemate
/-- info: 'Chess.Game.Forces.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.Forces.mono
/-- info: 'Chess.Game.Forces.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.Forces.trans
/-- info: 'Chess.Game.WinsIn.not_both' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.WinsIn.not_both
/-- info: 'Chess.Game.Wins.not_both' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.Wins.not_both
/-- info: 'Chess.Game.MateIn.unique' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.MateIn.unique
/--
info: 'Chess.Game.Wins.exists_mateIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Game.Wins.exists_mateIn
/-- info: 'Chess.Game.wins_attacker_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.wins_attacker_iff
/-- info: 'Chess.Game.wins_defender_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.wins_defender_iff
/-- info: 'Chess.Game.forces_attacker_zero_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.forces_attacker_zero_iff
/-- info: 'Chess.Game.forces_attacker_succ_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.forces_attacker_succ_iff
/-- info: 'Chess.Game.forces_defender_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.forces_defender_iff
/-- info: 'Chess.Game.searchForces_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.searchForces_iff
/-- info: 'Chess.Game.Forces.decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.Forces.decidable
/-- info: 'Chess.Game.MateIn.decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.MateIn.decidable
/-- info: 'Chess.Game.checkForces_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.checkForces_sound
/-- info: 'Chess.Game.checkForces_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.checkForces_complete
/-- info: 'Chess.Game.checkWin_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.checkWin_sound
/-- info: 'Chess.Game.checkWin_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.checkWin_complete
/-- info: 'Chess.Game.checkOnlyMove_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.checkOnlyMove_sound
/-- info: 'Chess.Game.Forces.of_play_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.Forces.of_play_eq
/-- info: 'Chess.Game.Forces.move_of_play_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.Forces.move_of_play_eq
/-- info: 'Chess.Game.Forces.replies_of_moves_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.Forces.replies_of_moves_eq
/-- info: 'Chess.Game.WinsIn.of_mated' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.WinsIn.of_mated
/-- info: 'Chess.Game.Forces.forall_mem_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.Forces.forall_mem_nil
/-- info: 'Chess.Game.Forces.forall_mem_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.Forces.forall_mem_cons
/-- info: 'Chess.Game.OnlyWinningMove.of_moves_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.of_moves_eq
/-- info: 'Chess.Game.OnlyWinningMove.refuted_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.refuted_nil
/-- info: 'Chess.Game.OnlyWinningMove.refuted_cons_self' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.refuted_cons_self
/-- info: 'Chess.Game.OnlyWinningMove.refuted_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.refuted_cons
/--
info: 'Chess.Game.firstFailure_eq_none_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Game.firstFailure_eq_none_iff
/--
info: 'Chess.Game.firstFailureOnlyMove_eq_none_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Game.firstFailureOnlyMove_eq_none_iff
/-- info: 'Chess.Game.OnlyWinningMove.wins_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.wins_iff
/-- info: 'Chess.Game.OnlyWinningMove.unique' does not depend on any axioms -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.unique
/-- info: 'Chess.Game.OnlyWinningMove.of_refuted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.of_refuted
/-- info: 'Chess.Game.OnlyWinningMove.winsIn_play' depends on axioms: [propext] -/
#guard_msgs in #print axioms Chess.Game.OnlyWinningMove.winsIn_play
/-- info: 'Chess.Game.Toy.takeAway_onlyWinningMove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Game.Toy.takeAway_onlyWinningMove

/-! ### Chess.ChessGame (notation, G2 in chess) -/

/-- info: 'Chess.fen_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.fen_eq_iff
/-- info: 'Chess.uci_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.uci_eq_iff
/-- info: 'Chess.readFEN_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.readFEN_eq_some_iff
/-- info: 'Chess.parseFEN_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.parseFEN_eq_some_iff
/-- info: 'Chess.parseUCI_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.parseUCI_eq_some_iff
/-- info: 'Chess.IsFEN.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.IsFEN.unique
/--
info: 'Chess.Position.fenFields_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.Position.fenFields_injective
/-- info: 'Chess.readFEN_toFEN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.readFEN_toFEN
/-- info: 'Chess.parseFEN_toFEN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.parseFEN_toFEN
/-- info: 'Chess.parseUCI_toUCI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.parseUCI_toUCI
/-- info: 'Chess.winsIn_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.winsIn_zero_iff
/-- info: 'Chess.not_wins_of_stalemate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.not_wins_of_stalemate

/-! ### Chess.Spec.Winning (G2 under the FIDE rules) -/

/-- info: 'Chess.specWinsIn_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.specWinsIn_zero_iff
/-- info: 'Chess.not_specWins_of_stalemate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.not_specWins_of_stalemate

/-! ### Chess.ChessGame.Fide (G8) -/

/-- info: 'Chess.mem_chess_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_chess_moves
/--
info: 'Chess.chess_mated_iff_checkmate' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.chess_mated_iff_checkmate
/--
info: 'Chess.forces_iff_specForces' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.forces_iff_specForces
/--
info: 'Chess.winsIn_iff_specWinsIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.winsIn_iff_specWinsIn
/-- info: 'Chess.wins_iff_specWins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.wins_iff_specWins
/--
info: 'Chess.mateIn_iff_specMateIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.mateIn_iff_specMateIn
/--
info: 'Chess.onlyWinningMove_iff_specOnlyWinningMove' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Chess.onlyWinningMove_iff_specOnlyWinningMove

/-! ### ChessTest (the tabulation the perft checks use) -/

/-- info: 'Chess.Position.tabulate_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.Position.tabulate_eq
