# Specification of the axioms ledger (`ChessTest.Axioms`, `ChessTest.AxiomsPerft`)

Role: test-library implementer (one overnight round, ROADMAP step 3).
Date: 2026-11-02.
Status: Round 2 and the ledger-coverage fix (2026-11-02), matched to `ChessTest/Axioms.lean` and
`ChessTest/AxiomsPerft.lean` (see `docs/process/ChessTest.md`).

Library: `ChessTest` (`lake build ChessTest`). Two files, neither of which defines anything:
`ChessTest/Axioms.lean` imports `Chess` and `ChessTest.Tabulate` and holds every entry but the
perft ones; `ChessTest/AxiomsPerft.lean` imports `ChessTest.Perft` and holds the eight entries of
the kernel perft theorems.

## 1. What it does

DESIGN §7.3 and THEOREMS §0.4 give every headline theorem a trust label, and say "a test file
records `#print axioms` for every headline theorem, so the labels are checked, not claimed". This is
that file. Each entry is

```lean
/-- info: 'Chess.mem_legalMoves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.mem_legalMoves
```

`#guard_msgs` fails the build when the message differs from the docstring. An entry whose expected
line would exceed 100 characters is wrapped after "depends on axioms:" and compared with
`#guard_msgs (whitespace := lax)`, which ignores the line break but not the text (checked: a
wrapped entry with a wrong axiom list fails). So the build of
`ChessTest` fails if any listed theorem acquires `sorryAx` (a `sorry`), `Lean.ofReduceBool` or
`Lean.trustCompiler` (a `native_decide`), or any declared `axiom`. Checked: an entry whose expected
line is wrong is an error (scratch file, 2026-11-02).

## 2. What it lists (152 entries)

Grouped by module, in this order, with a heading per group:

- `Chess.Basic` (20): R1 (`Square.ofIndex_index`, `Square.index_ofIndex`), R2 (`mem_all` and
  `all_nodup` for `Color`, `Kind`, `PromoKind`, `Piece`, `Square`, `Direction`, `Wing`),
  `Square.offset_eq_some_iff`, `Square.mem_ray_iff`, `shift_kingHome_two`, `shift_kingHome_one`.
- `Chess.Position` (12): `Board.set_same`, `set_ne`, `set_comm`, `Board.unpack_pack`,
  `Board.initial_kingHome`, `initial_rookHome`, `initial_flip`, `CastlingRights.get_revoke`,
  `get_revokeAll`, `revoke_le`, `revokeAll_le`; since the ledger-coverage fix (2026-11-02)
  `CastlingRights.get_ofGet`.
- `Chess.Rules` (33): R4 (`play_board_of_not_mem`, `play_board_src`, `_dst`, `_epVictim`,
  `_rookHome`, `_rookCastleSquare`, `play_turn`), R8 (`castling_play_le`), R5
  (`PseudoLegal.isLight_dst_iff_of_bishop`, `…_of_knight`, `PseudoLegal.promo_ne_none_iff`), R11
  (`checkmate_or_stalemate`, `not_checkmate_and_stalemate`), `reaches_congr`, `reaches_set_src`,
  `reaches_set_dst`, `Slides.symm`, `slides_symm`, `Board.attackedBy_iff`, and the bridges
  `PseudoLegal.isEnPassant_iff`, `isCastle_iff`, `isDoublePush_iff`, `attacksFrom_dst`,
  `touched_nodup`; since the L4.11 round (2026-11-02) `reaches_of_clear` and
  `CastleMove.legal_iff` (L4.11); since ROADMAP step 6 R3 (`reaches_symm`, `reaches_pawn_symm`,
  `Board.attackedBy_iff_superpiece`); since the ledger-coverage fix what castling leaves on the
  board (`CastleMove.play_board_of_ne`, `play_board_kingHome`, `play_board_kingCastleSquare`,
  `play_board_rookCastleSquare`).
- `Chess.MoveGen` (19): M1 (`mem_slideTargets`, `mem_reachTargets`), soundness
  (`legalMoves_eq_filter`, `legalMoves_sound`), the cover `PseudoLegal.mem_candidates`, M2 and M4
  (`mem_pseudoMoves`, `legalMoves_complete`, `mem_legalMoves`), M6 (`checkmate_iff`,
  `stalemate_iff`), the instances `Checkmate.decidableByGen` and `Stalemate.decidableByGen` (every
  kernel check of `Checkmate` or `Stalemate` after `MoveGen` runs through them),
  `candidates_ignores_epTarget`, `perft_one`, `sum_perftDivide`,
  `mem_legalMoves_of_agreesWithLegal`, `nodup_legalMoves_of_agreesWithLegal`; since ROADMAP step 6
  M3 (`Board.superpieceAttackedBy_iff`, `kingSafeAfter_iff`).
- `Chess.Game` (38): G2 (`winsIn_zero_iff`, `not_wins_of_stalemate`), G3 (`Forces.mono`), O8
  (`Forces.trans`), G4 (`WinsIn.not_both`, `Wins.not_both`), G6 (`MateIn.unique`,
  `Wins.exists_mateIn`), `wins_attacker_iff`, `wins_defender_iff`, since the ledger-coverage fix
  `forces_attacker_zero_iff`, `forces_attacker_succ_iff`, `forces_defender_iff`, G5
  (`searchForces_iff`, and since the ledger-coverage fix the instances `Forces.decidable` and
  `MateIn.decidable`), C1 and
  C2 (`checkForces_sound`, `checkForces_complete`, `checkWin_sound`, `checkWin_complete`), C7
  (`checkOnlyMove_sound`), C3 (`Forces.of_play_eq`, `Forces.move_of_play_eq`,
  `Forces.replies_of_moves_eq`, since ROADMAP step 5 `WinsIn.of_mated`, and since its review
  fixes `Forces.forall_mem_nil` and `Forces.forall_mem_cons`), O2
  (`OnlyWinningMove.wins_iff`, `.unique`, `.of_refuted`, `.winsIn_play`), the toy game's
  `Game.Toy.takeAway_onlyWinningMove`, and since step 5 the agreement of the diagnostics with the
  checkers (`firstFailure_eq_none_iff`, `firstFailureOnlyMove_eq_none_iff`); since ROADMAP step 7
  the only-move root glue (`OnlyWinningMove.of_moves_eq`, `refuted_nil`, `refuted_cons_self`,
  `refuted_cons`).
- `Chess.ChessGame` (12): `fen_eq_iff`, `uci_eq_iff`, `readFEN_eq_some_iff`,
  `parseFEN_eq_some_iff`, `parseUCI_eq_some_iff`, `IsFEN.unique`, `Position.fenFields_injective`,
  `readFEN_toFEN`, `parseFEN_toFEN`, `parseUCI_toUCI`, `winsIn_zero_iff`, `not_wins_of_stalemate`.
- `Chess.Spec.Winning` (2): `specWinsIn_zero_iff`, `not_specWins_of_stalemate`.
- `Chess.ChessGame.Fide` (7, G8): `mem_chess_moves`, `chess_mated_iff_checkmate`,
  `forces_iff_specForces`, `winsIn_iff_specWinsIn`, `wins_iff_specWins`, `mateIn_iff_specMateIn`,
  `onlyWinningMove_iff_specOnlyWinningMove`.
- `ChessTest` (1): `Position.tabulate_eq`.

`ChessTest/AxiomsPerft.lean` lists, under one heading:

- `ChessTest.Perft` (8): the eight kernel perft theorems of `docs/spec/ChessTest.Perft.md` §3.

Source of the list: every theorem and instance that the "Main statements" of a module's docstring
names, the table of ROADMAP §1, and the ★ and ★★ items of THEOREMS that are proved. A group that a
docstring mentions without naming its members ("the other sanity theorems about the initial board",
in `Chess.Position`) is represented by its named members only. Until the ledger-coverage fix
(2026-11-02) ten named Main statements were missing: `CastlingRights.get_ofGet`, the four
`CastleMove.play_board_…` lemmas, `forces_attacker_zero_iff`, `forces_attacker_succ_iff`,
`forces_defender_iff`, `Forces.decidable` and `MateIn.decidable`. Their coverage was checked by a
scripted comparison of the names in the Main-statements sections of `Chess/` with the ledger
entries, not by the build; the build checks only the axioms of what is listed. The Stage 1 closing
demonstration (Gotham) has its own ledger in the demo library, `ChessDemo/Axioms.lean`
(`docs/spec/ChessDemo.Axioms.md`), so that building the tests does not build the demo.

## 3. Result (2026-11-02)

All 152 are [kernel]: 62 use `propext`, `Classical.choice` and `Quot.sound`; 46 use `propext` and
`Quot.sound`; 19 use `propext` only; 25 use no axiom. (The ledger-coverage fix added ten: two
castling lemmas, `play_board_kingHome` and `play_board_kingCastleSquare`, to the first group; the
other two castling lemmas and `Forces.decidable` and `MateIn.decidable` to the second;
`forces_attacker_succ_iff` to the third; `CastlingRights.get_ofGet`, `forces_attacker_zero_iff` and
`forces_defender_iff` to the last. Before it: 142, with 60, 42, 18 and 22.) (ROADMAP steps 6–7 added
nine: R3 and M3, five, to the first group; `OnlyWinningMove.of_moves_eq` to the third and its three
list lemmas to the last; and `legalMoves_eq_filter`, `legalMoves_sound` and
`mem_legalMoves_of_agreesWithLegal` moved from the second group to the first, since their proofs now
go through `kingSafeAfter_iff`.) Before steps 6–7: 133, with 52, 45, 17 and 19. (Before the L4.11
round: 126, with 49 and 44 in the first two groups; `CastleMove.legal_iff` joined the first,
`reaches_of_clear` the second. ROADMAP step 5 added three: the two diagnostic agreements to the
first group, `WinsIn.of_mated` to the last; its review fixes added `Forces.forall_mem_nil` and
`Forces.forall_mem_cons` to the last.) (The 8 perft entries: 6 with the three axioms, 2 with
`propext` and `Quot.sound`.) None uses `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or a
declared axiom.

## 4. Design choices, with reasons

1. **The expected output is exact, not "a subset of the three".** `#guard_msgs` compares text, so
   a proof that drops an axiom also fails its entry. That costs a one-line update now and then, and
   it keeps the file a literal record of what `#print axioms` says. A Boolean subset check written
   in meta code would be shorter but would hide the actual output, which is what DESIGN §7.3 asks
   to record.
2. **Two modules, last in `ChessTest`.** `ChessTest.Axioms` imports `Chess` and
   `ChessTest.Tabulate` only, and builds in about 2 s once the library is built, so the trust labels
   of the library's own theorems can be checked without the perft suite
   (`lake build ChessTest.Axioms`). The eight perft entries need `ChessTest.Perft`, whose build
   takes minutes and about 5 GB; they are in `ChessTest.AxiomsPerft`.
3. **Instances are listed where kernel checks depend on them.** `decide +kernel` proofs of
   `Checkmate p` reduce `Checkmate.decidableByGen`; if that instance ever used a non-standard axiom,
   every such proof would inherit it.
