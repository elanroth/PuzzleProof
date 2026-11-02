# Specification of the demo's axioms ledger (`ChessDemo.Axioms`)

Role: demo implementer (one overnight round, ROADMAP step 7).
Date: 2026-11-02.
Status: Round 2 (2026-11-02: three entries added, for `gotham_refuted`, `gotham_specRefuted` and
the generated `refutations`; 16 in all), matched to `ChessDemo/Axioms.lean` (see
`docs/process/ChessDemo.md`).

Library: `ChessDemo`. File: `ChessDemo/Axioms.lean`, which imports `ChessDemo.Gotham` and
`ChessDemo.Mates` and defines nothing.

## 1. What it does

The same as the library's ledger (`docs/spec/ChessTest.Axioms.md`), for the demo: each entry is
`#guard_msgs in #print axioms X` under the expected output, so `lake build ChessDemo` fails if a
demo theorem comes to depend on `sorryAx`, on `Lean.ofReduceBool` or `Lean.trustCompiler` (a
`native_decide`), or on any declared `axiom`. Lines too long for one source line are wrapped and
compared with `#guard_msgs (whitespace := lax)`.

It is a separate file, not part of `ChessTest/Axioms.lean`, so that building the test library does
not build the demo (about three minutes).

## 2. What it lists

- `ChessDemo.Gotham`: `gotham_winsIn`, `uci_b7b2`, `gotham_onlyWinningMove`, `gotham_specWinsIn`,
  `gotham_specOnlyWinningMove`, `gotham_not_wins_white`, `gotham_refuted`, `gotham_specRefuted`.
- `ChessDemo.GothamCert` (generated): `winsIn`, `refutations`, `onlyWinningMove`, the three claims
  the headlines restate.
- `ChessDemo.Mates`: `foolsMate_mateIn`, `rookMate2_mateIn`, `rookMate3_winsIn`,
  `rookMate3_not_winsIn_two`, `rookMate3_mateIn`.

Every entry is [kernel]: its axioms are among `propext`, `Classical.choice` and `Quot.sound`.

## 3. The module docstring, word for word

```
# The demo's axioms ledger

`#print axioms` on every theorem of `ChessDemo.Gotham` and `ChessDemo.Mates`, and on the three
claims of the generated `ChessDemo.GothamCert`, each checked by `#guard_msgs`, so that the build of
`ChessDemo` fails if one of them comes to depend on `sorryAx`, on `native_decide`
(`Lean.ofReduceBool`, `Lean.trustCompiler`) or on a declared `axiom`. Specification:
`docs/spec/ChessDemo.Axioms.md`.

Every theorem listed is [kernel]: its axioms are among `propext`, `Classical.choice` and
`Quot.sound`. The library's own ledger is `ChessTest.Axioms`.
```
