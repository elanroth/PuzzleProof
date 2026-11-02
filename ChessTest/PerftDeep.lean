import ChessTest.Perft

/-!
# The perft suite, deeper

Interpreted `#guard`s of the published perft counts (chessprogramming.org, *Perft Results*) at
depth 3 for the three positions whose depth 3 is too slow for `ChessTest.Perft`, and at depth 4 for
Position 3. Kept in their own file so that they build in parallel with the rest of the test
library. Specification: `docs/spec/ChessTest.Perft.md` §4.

## Implementation notes

* The four checks run interpreted in about 2 to 2.5 minutes together on this machine (about 25 to
  40 s each), measured after the king-safety filter of ROADMAP step 6; before it they took about
  4.4 minutes.
  The compiled program `chess-perft` is about 20 times faster, and the differential test against
  python-chess (`docs/process/ChessTest.md`) runs every position to depth 4.
-/

namespace Chess

#guard perft 3 Perft.kiwipete.tabulate == 97862
#guard perft 3 Perft.position5.tabulate == 62379
#guard perft 3 Perft.position6.tabulate == 89890
#guard perft 4 Perft.position3.tabulate == 43238

end Chess
