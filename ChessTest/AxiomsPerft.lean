import ChessTest.Perft

/-!
# The axioms ledger, part 2: the kernel perft counts

`#print axioms` on the eight kernel perft theorems of `ChessTest.Perft`, in the format of
`ChessTest.Axioms`. Specification: `docs/spec/ChessTest.Axioms.md`.

## Implementation notes

* These entries are kept apart from `ChessTest.Axioms` because they need `ChessTest.Perft`, the
  heaviest build of the test library (several minutes, about 5 GB); the ledger of the library's
  own theorems does not wait for it.
-/

/-! ### ChessTest.Perft (M7 in the kernel) -/

/-- info: 'Chess.perft_initial_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_initial_1
/-- info: 'Chess.perft_initial_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_initial_2
/-- info: 'Chess.perft_kiwipete_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_kiwipete_1
/-- info: 'Chess.perft_position3_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_position3_1
/-- info: 'Chess.perft_position3_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_position3_2
/-- info: 'Chess.perft_position4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_position4_1
/-- info: 'Chess.perft_position5_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_position5_1
/-- info: 'Chess.perft_position6_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chess.perft_position6_1
