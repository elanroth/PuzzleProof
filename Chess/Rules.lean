import Chess.Rules.Defs
import Chess.Rules.Laws
import Chess.Rules.Castling

/-!
# Rules

The trusted specification of the FIDE Laws of Chess for moves: what a piece reaches and attacks,
check, the six movement rules, what a move does to a position, legality, checkmate and stalemate.
This file imports the three files of the module, which follow the trust boundary. Specification:
`docs/spec/Rules.md`; every definition carries the docstring given there.

## Main definitions

* `Reaches`, `Board.AttackedBy`, `InCheck`; the six rules joined into `PseudoLegal`;
  `Position.play`; `Legal`, `Checkmate`, `Stalemate` (`Chess.Rules.Defs`).

## Main statements

* R3, R4, R5, R8, R11 and G1, and the bridges between `play` and the rules (`Chess.Rules.Laws`).
* L4.11, `CastleMove.legal_iff`: castling is legal exactly when the square the king lands on is
  not attacked before the move (`Chess.Rules.Castling`).

## Implementation notes

* Only `Chess.Rules.Defs` is trusted, and it holds definitions only. `Chess.Rules.Laws` proves
  facts about them; `Chess.Rules.Castling` imports `Laws` and proves L4.11.
-/
