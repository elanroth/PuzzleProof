import Chess.ChessGame
import ChessTest.Tabulate

/-!
# The perft suite (THEOREMS M7)

The six standard perft positions of chessprogramming.org (*Perft Results*), and their published
perft counts, checked against this library's generator: in the kernel at depth 1 for all six and at
depth 2 where that is affordable, and by interpreted `#guard`s at depths 2 and 3. The deeper
`#guard`s are in `ChessTest.PerftDeep`. Specification: `docs/spec/ChessTest.Perft.md`; every
definition and theorem below carries the docstring given there.

## Main definitions

* `Perft.kiwipete`, `Perft.position3`, `Perft.position4`, `Perft.position5`, `Perft.position6`:
  positions 2 to 6 of the suite, written with `fen`. Position 1 is `Position.initial`.

## Main statements

* `perft_initial_1`, `perft_initial_2`, `perft_kiwipete_1`, `perft_position3_1`,
  `perft_position3_2`, `perft_position4_1`, `perft_position5_1`, `perft_position6_1`: the published
  counts, by `decide +kernel` [kernel].

## Implementation notes

* A perft count agreeing with the published one is evidence that `Legal` (through `legalMoves`,
  which lists exactly the legal moves by M4) and `Position.play` read FIDE as the
  chess-programming community does. It proves nothing about any position other than the one
  checked (THEOREMS M7).
* Kernel cost (this machine, measured after ROADMAP step 6): depth 1 takes 0.7 to 2.2 s per
  position; depth 2 takes 9.8 s for the initial position and 5.6 s for Position 3, and is kept; the
  whole module takes 39 s with a 3.7 GB peak. Before step 6, depth 2 of Position 4 took 26 s but
  6.6 GB, and depth 2 of Position 5 did not finish within 10 minutes under memory pressure, so
  depth 2 of Positions 4, 5, 6 and Kiwipete is checked by `#guard` only (not re-measured since).
* The `#guard`s run interpreted, on the tabulated position (`Position.tabulate`, proved equal to
  the position): a board read from a FEN is otherwise re-read from the FEN text at every square
  read, which made `perft 2 Perft.kiwipete` take 37 s instead of 1.6 s.
* The FENs have no en passant target, so the library's en passant convention does not matter here.
-/

namespace Chess

namespace Perft

/-- Position 2 of the chessprogramming.org perft suite, "Kiwipete" (Peter McKenzie): a middlegame
in which both sides hold both castling rights, with many captures and pins. -/
def kiwipete : Position :=
  fen "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"

/-- Position 3 of the chessprogramming.org perft suite: a rook-and-pawn endgame whose
lines include en passant captures that would expose a king along the fifth rank. -/
def position3 : Position := fen "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1"

/-- Position 4 of the chessprogramming.org perft suite: White to move and in check, with pawns
about to promote on both sides and Black's two castling rights. -/
def position4 : Position :=
  fen "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1"

/-- Position 5 of the chessprogramming.org perft suite: White's pawn on d7 can promote by
capturing on c8, and White holds both castling rights. -/
def position5 : Position := fen "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"

/-- Position 6 of the chessprogramming.org perft suite (Steven Edwards): a middlegame with
no castling rights. -/
def position6 : Position :=
  fen "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10"

end Perft

/-! ## Kernel checks -/

/-- Perft 1 of the initial position is 20, the published count. [kernel] -/
theorem perft_initial_1 : perft 1 Position.initial = 20 := by decide +kernel

/-- Perft 2 of the initial position is 400, the published count. [kernel] -/
theorem perft_initial_2 : perft 2 Position.initial = 400 := by decide +kernel

/-- Perft 1 of Kiwipete is 48, the published count. [kernel] -/
theorem perft_kiwipete_1 : perft 1 Perft.kiwipete = 48 := by decide +kernel

/-- Perft 1 of Position 3 is 14, the published count. [kernel] -/
theorem perft_position3_1 : perft 1 Perft.position3 = 14 := by decide +kernel

/-- Perft 2 of Position 3 is 191, the published count. [kernel] -/
theorem perft_position3_2 : perft 2 Perft.position3 = 191 := by decide +kernel

/-- Perft 1 of Position 4 is 6, the published count. [kernel] -/
theorem perft_position4_1 : perft 1 Perft.position4 = 6 := by decide +kernel

/-- Perft 1 of Position 5 is 44, the published count. [kernel] -/
theorem perft_position5_1 : perft 1 Perft.position5 = 44 := by decide +kernel

/-- Perft 1 of Position 6 is 46, the published count. [kernel] -/
theorem perft_position6_1 : perft 1 Perft.position6 = 46 := by decide +kernel

/-! ## Interpreted checks -/

-- Depth 2 of the four positions whose depth 2 is not checked in the kernel (about 1.5 s each).
#guard perft 2 Perft.kiwipete.tabulate == 2039
#guard perft 2 Perft.position4.tabulate == 264
#guard perft 2 Perft.position5.tabulate == 1486
#guard perft 2 Perft.position6.tabulate == 2079
-- Depth 3 of the three cheapest positions (about 2 to 10 s each).
#guard perft 3 Position.initial == 8902
#guard perft 3 Perft.position3.tabulate == 2812
#guard perft 3 Perft.position4.tabulate == 9467

end Chess
