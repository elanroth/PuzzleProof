import Chess.ChessGame
import ChessTest.Tabulate

/-!
# ChessPerft

The command-line program `chess-perft`, for differential tests of the move generator against other
programs (python-chess, Stockfish's `go perft`). Specification: `docs/spec/ChessPerft.md`.

Usage: `lake exe chess-perft <FEN> <depth>`. The FEN may be one argument or several, which are
joined by single spaces. It is read by `parseFEN`, so it must be canonical FEN of a sane position.
The program prints `fen ` followed by the position written back by `Position.toFEN`; then, for a
depth of at least 1, the divide: one line `<uci> <count>` per entry of `legalMoves`, in the
generator's order (`perftDivide`); and last the line `perft <depth> <count>`.

## Implementation notes

* Nothing here is trusted or proved: the program runs `parseFEN` and `perftDivide` of the
  library, compiled, on the position tabulated by `Position.tabulate` (which changes nothing,
  `Position.tabulate_eq`, but makes reading a square of a board read from a FEN cheap).
* The total is the sum of the divide, which is `perft n p` by `sum_perftDivide`; so the search
  runs once, not twice.
* The FEN line shows the position as this library stores it, with the clocks written as `0 1`
  (a position records none). The en passant target is the one given in the input, which may differ
  from what another program writes: python-chess writes it only when a capture is possible. Perft
  counts do not depend on this.
-/

open Chess

/-- The text printed for a bad command line. -/
def usage : String :=
  "usage: chess-perft <FEN> <depth>\n" ++
  "  prints the FEN as read, the divide (one line '<uci> <count>' per legal move) and\n" ++
  "  the line 'perft <depth> <count>'"

/-- The lines printed for position `p` at depth `n`: the FEN as read, the divide when `n` is at
least 1, then the total. -/
def perftReport (p : Position) (n : Nat) : List String :=
  let d := match n with
    | 0 => []
    | k + 1 => perftDivide k p
  let total := if n = 0 then 1 else (d.map (·.2)).sum
  [s!"fen {p.toFEN}"] ++ d.map (fun (m, c) => s!"{m.toUCI} {c}") ++ [s!"perft {n} {total}"]

/-- Reads the FEN (all arguments but the last, joined by spaces) and the depth (the last
argument), and prints `perftReport` of the tabulated position; exits with code 1 on a bad command
line. -/
def main (args : List String) : IO UInt32 := do
  match args.reverse with
  | depth :: fenRev@(_ :: _) =>
    let s := " ".intercalate fenRev.reverse
    match parseFEN s, depth.toNat? with
    | some p, some n =>
      for line in perftReport p.tabulate n do IO.println line
      return 0
    | none, _ =>
      IO.eprintln s!"not a canonical FEN of a sane position: {s}\n{usage}"
      return 1
    | _, none =>
      IO.eprintln s!"not a depth: {depth}\n{usage}"
      return 1
  | _ =>
    IO.eprintln usage
    return 1
