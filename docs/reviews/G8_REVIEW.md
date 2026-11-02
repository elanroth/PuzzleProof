# Independent review: `Chess.Spec.Winning` and `Chess.ChessGame.Fide` (G8)

Date: 2026-11-02. Commit reviewed: `ae51012` (working tree clean). Lean `v4.28.0`.
Reviewer: an independent session. It did not write either file, and it did not rely on
`docs/VERIFICATION.md` or on the authors' own review (`docs/reviews/Spec.Winning.md`).

**Method.** I read both files whole, together with `Chess/Rules/Defs.lean` and the `Game.chess`
definitions they target. I then wrote scratch probes outside the library and ran each with
`lake env lean`. Copies of the probes are in the shared notes folder, under `g8review-probes/`:

| Probe | What it checks |
|---|---|
| `Boundary.lean` | The import closure and the constant closure of `Spec/Winning` |
| `Axioms.lean` | The axioms of the bridge and of the Gotham theorems, and the statement closure of the Gotham theorems |
| `Semantics.lean` | General theorems about the Spec definitions, proved from `Spec/Winning` and `Rules` alone |
| `CA`–`CD.lean`, `Insane.lean` | Concrete positions |

No library file was edited. `lake build` (Chess) succeeds, and `lake build ChessDemo --no-build`
reports that all targets are up to date, so the oleans I inspected match the source.

---

## Findings, by severity

**No finding affects the soundness of the Gotham headline theorems.** None is Critical, High or
Medium.

### F1 (Low): the Spec notions are unguarded on positions that cannot arise in chess

`SpecForces`, `Legal` and `Checkmate` place no requirement on the starting position. On a position
where the side not to move is in check, `Legal` allows the king to be captured. After that, the
side without a king can never be checkmated, because `InCheck` needs a king. Kernel-checked
(`Insane.lean`):

```lean
def Q : Position := { (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1").play ⟨⟨0,0⟩,⟨0,7⟩,none⟩
                      with turn := .white }            -- Black mated, but White to move
theorem Q_kingCapture : Legal Q ⟨⟨0,7⟩,⟨6,7⟩,none⟩ ∧
    ¬ (Q.play ⟨⟨0,7⟩,⟨6,7⟩,none⟩).board.HasKing .black := by decide +kernel   -- ✓
```

FIDE says nothing about such positions, so this is not a mis-statement. Still, neither docstring
says the notions are meant for legal positions.

**Effect on Gotham: none.** Three facts close it off:

- `Puzzles.gotham` is `Position.Sane` (`fen_eq_iff`). I also checked directly that White is not in
  check (`CC.lean`, `gotham_turn`, by `decide +kernel`).
- Every legal move keeps the side not to move out of check. This is immediate from `Legal`, and
  `Insane.lean` proves it as `after_legal`:
  `Legal p m → ¬ (p.play m).board.KingAttacked (p.play m).turn.other`.
- So no line from Gotham ever reaches a king capture.

**Suggestion (optional):** add one sentence to the module docstring: "Meant for positions in which
the side not to move is not in check, such as every `fen` position and every position reached from
one by legal moves."

### F2 (Low, about trust): the headline *statement* depends on the FEN and UCI parsers

`Spec/Winning` is clean (see Q2). But the statements of `gotham_specWinsIn`,
`gotham_specOnlyWinningMove` and `gotham_specRefuted` mention `Puzzles.gotham := fen "…"` and
`uci "b7b2"`. Their constant closure pulls in 39 constants from `Chess.ChessGame`, including
`parseFEN`, `readFEN`, `readBoard`, `parseUCI` and `readMove` (`Axioms.lean`, `reportStmt`). The
closure contains nothing from `MoveGen` or `Game`.

The demo's docstring already says the reader trusts `fen` and `uci` through `fen_eq_iff` and
`uci_eq_iff`. That is a valid argument, but it was outside the scope of this review. I checked the
position itself independently of the parser:

- **Board.** `Position.diagram` (in `Chess.Position`, not the parser) prints:

  ```
  8 . . b . . b k . / 7 . r . . . r p . / 6 p . . p . . . R / 5 q . . N p . . Q
  4 . . . . P p . B / 3 . . p . . P . . / 2 P P P . . . . P / 1 . K . . . . R .
  Black to move, castling -, en passant -
  ```

  This matches `2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1` square by square.
- **The move.** `uci "b7b2" = ⟨⟨1,6⟩,⟨1,1⟩,none⟩ ∧ Legal Puzzles.gotham (uci "b7b2")`, by
  `decide +kernel` (`CC.lean`).
- **Black's legal moves.** I filtered all 64 × 64 × 5 move values through the `Legal` decision
  procedure of `Rules.Defs` (`CD.lean`, `#eval`). There are **34** legal moves, `b7b2` among them.
  This agrees with "its other 33 legal moves" in `gotham_onlyWinningMove`.

**Suggestion (optional):** to remove the parser from the reading entirely, add a kernel-checked
theorem `Puzzles.gotham.diagram = "…"`, or one that states the board literally.

### F3 (Informational, tooling): the kernel stalls on `∀ r, Legal p r → Q r`

`decide +kernel` proves `Checkmate p`, i.e. `∀ m, ¬ Legal p m`, in about 1 s on small positions
(`Speed.lean`, `CA.lean`). It did not finish within 280 s on either of these:

- `∀ r, Legal P5 r → r = uci "h8g8"`
- `∀ r, Legal P5 r → Legal (P5.play r) ra8 ∧ Checkmate ((P5.play r).play ra8)`

Here `P5` is `7k/8/6K1/8/8/8/8/R7 b - - 0 1`. Compiled `#eval` and `native_decide` return `true`
at once. I did not diagnose the cause. This does not affect soundness; it is a note for whoever
writes kernel tests of the Spec layer.

### F4 (Nit): readability and docstrings

Every docstring in `Spec/Winning.lean` appears verbatim in `docs/spec/Spec.Winning.md` (10 of 10,
checked by script). I found none that misdescribes its definition. Each claim checked against a
proof:

| Docstring claim | Proof |
|---|---|
| "Moves of the other side cost nothing" | `def_inv` |
| "budgets count the moves of `a` only, the mating move included" | `specWinsIn_one_iff` |
| "a stalemated defender has not lost" | `not_specWins_of_stalemate`; concrete in `P3_qf7_not_win` |
| "`T` is tested at every position, `p` included" | the `goal` rule |

Two nits:

- `SpecMateIn` says "mates in exactly `n`". This also holds with `n = 0` when the defender is
  already mated. That is harmless, but it could be said.
- `Spec/Winning` imports `Chess.Rules`, which brings in the untrusted `Laws` and `Castling`. The
  import is needed for the G2 proofs (`play_turn`). The definitions use only `Rules.Defs` (Q2), so
  a reader loses nothing, but a one-line comment would save the reader from checking.

`Fide.lean` reads well. Its claim that "the only facts used about the generator are
`mem_legalMoves` and `checkmate_iff`" is true of the source: `mem_chess_moves` and
`chess_mated_iff_checkmate` are those two lemmas, and every other proof uses only them plus `List`
lemmas.

---

## Evidence by question

### Q1: do the Spec definitions say what a chess player means?

**The main result.** I defined the textbook mate-in-n recursion independently. For the attacker to
move:

```lean
def Ref (a : Color) : Nat → Position → Prop
  | 0, _ => False
  | n + 1, p => p.turn = a ∧ ∃ m, Legal p m ∧
      (Checkmate (p.play m) ∨
        ((∃ r, Legal (p.play m) r) ∧ ∀ r, Legal (p.play m) r → Ref a n ((p.play m).play r)))
```

I then proved, from `Spec/Winning` and `Rules` alone (`Semantics.lean`, axioms
`propext, Classical.choice, Quot.sound`):

```lean
theorem specWinsIn_iff_ref : ∀ n p, p.turn = a → (SpecWinsIn a n p ↔ Ref a n p)
```

The two inversion lemmas behind it also pin down the case where the defender is to move:

```lean
theorem att_inv (ht : p.turn = a) :       SpecWinsIn a n p ↔ ∃ k, n = k + 1 ∧ ∃ m, Legal p m ∧ SpecWinsIn a k (p.play m)
theorem def_inv (ht : q.turn = a.other) : SpecWinsIn a n q ↔
    Checkmate q ∨ ((∃ r, Legal q r) ∧ ∀ r, Legal q r → SpecWinsIn a n (q.play r))
```

**Each case in the brief, checked:**

| Case | Result | Evidence |
|---|---|---|
| Stalemate is not a win | ✓ | `not_specWins_of_stalemate`, in the file and re-read. Concrete: in `7k/4Q3/6K1/8/8/8/8/8 w`, `Qe7f7` is `Legal` and leads to `Stalemate`, so it is `¬ SpecWins .white` there. `Qe7e8` is `Checkmate`, so `SpecWinsIn .white 1` holds (`CA.lean`, all by `decide +kernel`). |
| A defender with no legal move | ✓ | By `def_inv`: a win iff `Checkmate`. A defender that is not in check with no legal move is stalemate, so not a win. The `∃ r, Legal q r` guard rules out a vacuous `∀`. |
| Move count: n moves, not n plies | ✓ | `specWinsIn_one_iff : p.turn = a → (SpecWinsIn a 1 p ↔ ∃ m, Legal p m ∧ Checkmate (p.play m))`. Concrete: `SpecMateIn .white 1` for the back-rank mate `6k1/5ppp/8/8/8/8/8/R5K1 w` (`CA.lean`, `P1_mateIn1`). With the defender to move, its reply is free: `P5` (Black to move, only Kg8, then Ra8#) has `SpecWinsIn .white 1` and `¬ SpecWinsIn .white 0` (`CB.lean`; the "every reply" step was checked with `native_decide`, see F3). |
| No win when the side mated is the wrong one | ✓ | The target requires `q.turn = a.other ∧ Checkmate q`, so the side mated is the defender, on its own turn. `not_specWins_of_checkmated : p.turn = a → Checkmate p → ¬ SpecWins a p` (proved). After the mate in `P1`, `SpecWinsIn .white 0` holds and `¬ SpecWins .black` holds (`P1_after`). With the attacker to move, budget 0 never wins (`att_inv`). |
| No vacuous truth | ✓ | `move` requires a `Legal` witness. `replies` requires `∃ m, Legal p m`. `SpecForces` is inductive, so derivations are finite and play that never reaches mate is never forced. |
| Colour and turn | ✓ | `not_both : SpecWinsIn a n p → ¬ SpecWinsIn a.other k p` (proved): no position is won for both sides. Gotham: `turn = .black` (`gotham_turn`). |
| Budgets well behaved | ✓ | `specWinsIn_succ` (monotone), so `SpecMateIn`'s `∀ k < n` means "not within `n − 1`". |
| `SpecOnlyWinningMove` | ✓ | It requires `Legal p m`, then `SpecWins p.turn (p.play m)`, then that every other legal `m'` does not win. Proved: `only_wins` (the side to move then wins at `p`) and `only_unique` (any legal winning `m'` equals `m`). Distinct `Move` values are distinct chess moves: every rule other than push and pawn capture forces `promo = none`, those two force `promo ≠ none` exactly on the last rank, castling is only the king's two-square move, and `PieceMove` cannot land on its own rook. Different promotion pieces count as different moves, as the docstring says and as chess has it. |

### Q2: is the trust boundary real?

Checked with `Boundary.lean`, which imports only `Chess.Spec.Winning`.

**Imports.** The non-core transitive imports are exactly `Chess.Basic`, `Chess.Position`,
`Chess.Rules.Defs`, `Chess.Rules.Laws`, `Chess.Rules.Castling`, `Chess.Rules` and
`Chess.Spec.Winning`. There is no `MoveGen`, `Game`, `ChessGame` or certificate module.

**Constants.** I took the closure over types and definition bodies of `SpecForces`, `SpecWinsIn`,
`SpecWins`, `SpecMateIn` and `SpecOnlyWinningMove`, grouped by module, leaving out `Init`:

| Module | Constants |
|---|---|
| `Chess.Basic` | 105 |
| `Chess.Position` | 22 |
| `Chess.Rules.Defs` | 38 (`Legal`, `Checkmate`, `Position.play` and their parts, among them the `Decidable` instances used by `if` inside `play`) |
| `Chess.Spec.Winning` | 8 |
| `Rules.Laws`, `Rules.Castling` | **0** |

The definitions therefore depend on nothing outside the documented trusted base. The `Decidable`
instances used inside `play` cannot change its meaning, since any `Decidable p` instance agrees
with `p`.

**Elaborated definitions.** `#print Chess.SpecForces` shows the three constructors exactly as the
source reads them. G2's axioms are `propext, Quot.sound`.

### Q3: is the bridge sound and stated at full strength?

**Statements** (`#check`). Each is an unconditional iff over all `a`, `n`, `p`, `m`, with no
extra hypotheses:

- `forces_iff_specForces` holds **for every target `T`**.
- The others are `winsIn_iff_specWinsIn`, `wins_iff_specWins`, `mateIn_iff_specMateIn`,
  `onlyWinningMove_iff_specOnlyWinningMove`, `mem_chess_moves` and `chess_mated_iff_checkmate`.

**Matching definitions.** `#print` confirms that `Chess.WinsIn` and the other headline notions are
reducible wrappers of the `Game.chess` notions. `Game.Forces` has the same three rules, with
`m ∈ G.moves x` for `Legal` and `G.moves x ≠ []` for `∃ m, Legal`. `DefenderMated` is
`turn = a.other ∧ Mated`, and `Game.chess.Mated` is `InCheck p ∧ legalMoves p = []`.

**Axioms.** Every one of the seven bridge theorems, and `gotham_specWinsIn`,
`gotham_specOnlyWinningMove` and `gotham_specRefuted`, depends on exactly
`[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, `Lean.ofReduceBool` or
`Lean.trustCompiler`, so no `native_decide`, and no custom axiom.

**Statement closure of the three Gotham Spec theorems.** It contains `Basic`, `Position`,
`Rules.Defs`, `Spec.Winning`, `Puzzles.gotham`, the `fen`/`uci` parser in `Chess.ChessGame`
(see F2), and one proof term `ChessDemo.uci_b7b2._proof_1`. That term is proof-irrelevant: it is
the `isSome` side condition of `uci`. There is nothing from `MoveGen`, `Game` or `GothamCert`.

---

## Verdict

1. **Q1: yes.** `SpecWinsIn`, `SpecWins`, `SpecMateIn` and `SpecOnlyWinningMove` say what a chess
   player means by "side `a` forces checkmate within `n` of its own moves", under FIDE's movement
   and checkmate rules with no draw rules. I showed this by proving `SpecWinsIn` equivalent to the
   textbook mate-in-n recursion, and by kernel-checked concrete cases covering mate in one, the
   stalemate trap, a free defender reply, the mated side, and both colours. The only caveat is
   positions that cannot arise in chess (F1), which no headline can reach.
2. **Q2: yes.** `Spec/Winning`'s definitions depend only on `Basic`, `Position` and `Rules.Defs`.
   Nothing from `MoveGen`, `Game`, `ChessGame` or the certificates is imported. The headline
   statements additionally use the `fen`/`uci` parsers (F2). I checked the Gotham position, its
   34 legal moves and the move `b7b2` independently of those parsers.
3. **Q3: yes.** All seven bridge theorems are unconditional iffs at full strength (`Forces` for
   every target), proved from `mem_legalMoves` and `checkmate_iff` alone. They and the three
   Gotham Spec theorems use only `propext`, `Classical.choice` and `Quot.sound`.
