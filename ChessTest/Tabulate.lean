import Chess.Position

/-!
# Tabulated boards

A speed-up for running the generator in compiled or interpreted code (the `#guard`s of the perft
suite and the program `chess-perft`), proved to change nothing. Specification:
`docs/spec/ChessTest.Perft.md` §1.

## Main definitions

* `Position.tabulate`: the same position, with its board read once into an array.

## Main statements

* `Position.tabulate_eq`: tabulating gives back the same position.

## Implementation notes

* A `Board` is a function, and the code compiled for a function-valued definition can re-run the
  definition's body on every square read. A board read from a FEN (`readBoard` in
  `Chess.ChessGame`) re-reads the FEN text each time a square is asked about: measured with the
  compiled `chess-perft`, perft 3 of the initial position read from its FEN takes 11 s untabulated
  and 0.4 s tabulated. `Position.tabulate` returns a `Position`, a structure, so the array is built
  once per call.
-/

namespace Chess

/-- The position `p` with its board read once into an array of the 64 squares, in index order,
and served from that array. It is the same position (`Position.tabulate_eq`), but a square of
its board is then read in constant time, however the board was built. -/
def Position.tabulate (p : Position) : Position :=
  let a : Array (Option Piece) := (Square.all.map p.board).toArray
  { p with board := fun s => a[s.index.val]! }

/-- Tabulating a position gives back the same position. -/
theorem Position.tabulate_eq (p : Position) : p.tabulate = p := by
  obtain ⟨b, c, cr, e⟩ := p
  simp only [Position.tabulate, Position.mk.injEq, and_true]
  funext s
  have h : (List.finRange 64)[s.index.val]? = some s.index := by
    rw [List.getElem?_eq_getElem (by simpa using s.index.isLt)]
    simp [Square.index]
  simp only [Square.all, List.map_map, getElem!_def, List.getElem?_toArray, List.getElem?_map, h,
    Option.map_some, Function.comp_apply, Square.ofIndex_index]
