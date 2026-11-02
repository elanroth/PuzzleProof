import ChessDemo.Gotham
import ChessDemo.Mates

/-!
# The demo's axioms ledger

`#print axioms` on every theorem of `ChessDemo.Gotham` and `ChessDemo.Mates`, and on the three
claims of the generated `ChessDemo.GothamCert`, each checked by `#guard_msgs`, so that the build of
`ChessDemo` fails if one of them comes to depend on `sorryAx`, on `native_decide`
(`Lean.ofReduceBool`, `Lean.trustCompiler`) or on a declared `axiom`. Specification:
`docs/spec/ChessDemo.Axioms.md`.

Every theorem listed is [kernel]: its axioms are among `propext`, `Classical.choice` and
`Quot.sound`. The library's own ledger is `ChessTest.Axioms`.
-/

/-! ### ChessDemo.Gotham and the generated ChessDemo.GothamCert -/

/-- info: 'ChessDemo.gotham_winsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.gotham_winsIn
/-- info: 'ChessDemo.uci_b7b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.uci_b7b2
/--
info: 'ChessDemo.gotham_onlyWinningMove' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_onlyWinningMove
/--
info: 'ChessDemo.gotham_specWinsIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_specWinsIn
/--
info: 'ChessDemo.gotham_specOnlyWinningMove' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_specOnlyWinningMove
/--
info: 'ChessDemo.gotham_not_wins_white' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_not_wins_white
/-- info: 'ChessDemo.gotham_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.gotham_refuted
/--
info: 'ChessDemo.gotham_specRefuted' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.gotham_specRefuted
/--
info: 'ChessDemo.GothamCert.winsIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.GothamCert.winsIn
/--
info: 'ChessDemo.GothamCert.refutations' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.GothamCert.refutations
/--
info: 'ChessDemo.GothamCert.onlyWinningMove' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.GothamCert.onlyWinningMove

/-! ### ChessDemo.Mates -/

/-- info: 'ChessDemo.foolsMate_mateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.foolsMate_mateIn
/-- info: 'ChessDemo.rookMate2_mateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.rookMate2_mateIn
/-- info: 'ChessDemo.rookMate3_winsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.rookMate3_winsIn
/--
info: 'ChessDemo.rookMate3_not_winsIn_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ChessDemo.rookMate3_not_winsIn_two
/-- info: 'ChessDemo.rookMate3_mateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChessDemo.rookMate3_mateIn
