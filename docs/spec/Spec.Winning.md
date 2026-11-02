# Specification of `Chess.Spec.Winning`

Role: English specification writer and translator (one overnight round, G8).
Date: 2026-11-02.
Status: Round 1, matched to the Lean of `Chess/Spec/Winning.lean` (see
`docs/process/Spec.Winning.md`). Every definition and lemma below is in the library, with no
`sorry`.

File: `Chess/Spec/Winning.lean`. Depends on: `Chess.Rules` only (and through it `Chess.Position`,
`Chess.Basic`); core only. Refines `docs/spec/ChessGame.md` §7 (D7.1–D7.4, planned there in Round 1)
and THEOREMS G8. The proofs that connect these definitions to the chess game are in
`Chess/ChessGame/Fide.lean` (`docs/spec/ChessGame.Fide.md`).

What a reader must trust from this module: **all of it.** It is short on purpose. From Stage 2 on, a
headline `WinsIn a n (fen "…")` or `OnlyWinningMove (fen "…") (uci "…")` may be read through the
definitions here, and then the reader needs `Chess.Rules` (with `Position` and `Basic` below it),
this file, and the notation of `Chess.ChessGame`, but not `Chess.MoveGen` and not `Chess.Game`.

## 0. How to read this document

The conventions of `docs/spec/Game.md` §0 and `docs/spec/ChessGame.md` §0 apply unchanged: each
definition has an ID, its Lean name and type, its Lean body, and a **docstring** in quotation marks
that the Lean carries word for word; each lemma has an ID, an English statement (its docstring), the
Lean statement and a tag ([core] or [sanity]); `autoImplicit = false`; everything lives in
`namespace Chess`.

Letters: `a` the attacker (a colour); `T` a target (a predicate on positions); `n k` budgets;
`p q` positions; `m m'` moves.

**Words.** "The other side" is `a.other`, the defender. "Legal" is `Legal` of `Chess.Rules`: the
movement rules hold and the mover's king is not attacked afterwards (FIDE 3.9.2). "Checkmate" is
`Checkmate` of `Chess.Rules`: in check and no legal move (FIDE 1.4 and 1.4.1; 5.1.1 makes it a win). "Stalemate" is `Stalemate`:
not in check and no legal move (FIDE 5.2.1).

### The idea of the module

`Chess.Game` states forcing once, for any game, and `Chess.ChessGame` instantiates it with the move
generator. That is the right shape for proofs and certificates, but it puts two extra layers between
a reader and the rules. This file writes the same three rules of forcing directly for chess, with
`Legal` where the game says "available" and `Checkmate` where it says "mated", so that a chess
reader can check a headline against FIDE without reading the generator or the abstract game.
`Chess.ChessGame.Fide` proves the two readings equivalent.

## Contents of the file, in order

1. Winning under the FIDE rules: `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecMateIn`,
   `SpecOnlyWinningMove`.
2. Checkmate and stalemate (`section Laws`): `specWinsIn_zero_iff`, `not_specWins_of_stalemate`.

---

## 1. Section "Winning under the FIDE rules"

### D1.1 `SpecForces (a : Color) (T : Position → Prop) : Nat → Position → Prop` (an inductive)

```lean
inductive SpecForces (a : Color) (T : Position → Prop) : Nat → Position → Prop
  | goal {n : Nat} {p : Position} : T p → SpecForces a T n p
  | move {n : Nat} {p : Position} (m : Move) : p.turn = a → Legal p m →
      SpecForces a T n (p.play m) → SpecForces a T (n + 1) p
  | replies {n : Nat} {p : Position} : p.turn = a.other → (∃ m, Legal p m) →
      (∀ m, Legal p m → SpecForces a T n (p.play m)) → SpecForces a T n p
```

Docstring: "`SpecForces a T n p`: from position `p`, the side `a` can force play into the target `T`
using at most `n` moves of its own, whatever the other side does, the moves of both sides being the
legal moves of `Chess.Rules`. Moves of the other side cost nothing. `T` is tested at every position,
`p` included. The other side, to move with no legal move, escapes unless the position is in `T`, and
play that never reaches `T` is never forced."

Constructor docstrings:

- `goal`: "A position in the target is forced, within any budget."
- `move`: "If `a` is to move and some legal move leads to a position forced within `n`, the position
  is forced within `n + 1`."
- `replies`: "If the other side is to move, has at least one legal move, and every legal move leads
  to a position forced within `n`, the position is forced within `n`. This rule never applies to a
  side with no legal move, so for `SpecWinsIn` a stalemated defender has not lost."

Notes.
- The three rules are those of `Game.Forces` (`docs/spec/Game.md`), with `G.turn x` read as
  `p.turn`, `m ∈ G.moves x` as `Legal p m`, `G.moves x ≠ []` as `∃ m, Legal p m`, and `G.play x m`
  as `p.play m`. The correspondence is exact, rule for rule, which is what makes the bridge
  (`forces_iff_specForces`) a plain induction in each direction.
- The `replies` rule has the **guard** `∃ m, Legal p m`. Without it, a defender with no legal move
  would satisfy "every legal move leads to a forced position" vacuously, and a stalemate would count
  as a loss for the side to move. With it, a defender with no legal move is forced only if the
  position is already in `T`.
- "Whatever the other side does" covers only the other side's legal moves. A position with the
  attacker to move and no legal move is not forced unless it is in `T`: no rule applies.
- `p.play m` is total (`Chess.Rules`), and is read here only after `Legal p m`.

### D1.2 `SpecWinsIn (a : Color) (n : Nat) (p : Position) : Prop` (an `abbrev`)

```lean
abbrev SpecWinsIn (a : Color) (n : Nat) (p : Position) : Prop :=
  SpecForces a (fun q => q.turn = a.other ∧ Checkmate q) n p
```

Docstring: "`SpecWinsIn a n p`: from position `p`, whichever side is to move there, the side `a` can
force checkmate (FIDE 5.1.1) of the other side using at most `n` moves of its own, the mating move
included, whatever the other side plays, the moves of both sides being FIDE-legal moves. There is no
move-count, repetition or dead-position rule."

Notes.
- `abbrev`, as `Game.WinsIn` is, so that `cases` and `induction` see `SpecForces` directly.
- The target names the side: checkmate of `a.other`, with `a.other` to move. `Checkmate q` alone
  would also count the attacker being checkmated.
- Budgets count the moves of `a` only, the mating move included, and are counted at `p`. If
  `a.other` is to move at `p`, its first reply is free.

### D1.3 `SpecWins (a : Color) (p : Position) : Prop`

```lean
def SpecWins (a : Color) (p : Position) : Prop :=
  ∃ n, SpecWinsIn a n p
```

Docstring: "`SpecWins a p`: from position `p`, the side `a` can force checkmate of the other side
within some number of its own moves, a bound fixed in advance (`∃ n, SpecWinsIn a n p`)."

### D1.4 `SpecMateIn (a : Color) (n : Nat) (p : Position) : Prop`

```lean
def SpecMateIn (a : Color) (n : Nat) (p : Position) : Prop :=
  SpecWinsIn a n p ∧ ∀ k < n, ¬ SpecWinsIn a k p
```

Docstring: "`SpecMateIn a n p`: from position `p`, the side `a` mates in exactly `n`: it can force
checkmate of the other side within `n` moves of its own, and not within fewer. With `n = 0` it says
that the other side is to move and already checkmated."

Note. Not in the Round 1 plan of `docs/spec/ChessGame.md` §7, which stated L7.5 for `MateIn` by
spelling out `SpecWinsIn a n p ∧ ∀ k < n, ¬ SpecWinsIn a k p`. A name makes the bridge read like the
other three.

### D1.5 `SpecOnlyWinningMove (p : Position) (m : Move) : Prop`

```lean
def SpecOnlyWinningMove (p : Position) (m : Move) : Prop :=
  Legal p m ∧ SpecWins p.turn (p.play m) ∧
    ∀ m', Legal p m' → m' ≠ m → ¬ SpecWins p.turn (p.play m')
```

Docstring: "`SpecOnlyWinningMove p m`: `m` is legal at `p`, the side to move wins after `m`, and
after every other legal move it does not win. 'Other' means a different move value: promotions to
different pieces are different moves. An alternative that wins only slowly still counts as winning,
so it makes this false."

Note. "Different move value" relies on `Move` having one value per FIDE move. Castling has one
encoding (the king's two-square move), so no FIDE move has two values; this is the same obligation
`Game.moves` states, and here it is a property of `Move` and `Legal`, not of a generator.

---

## 2. Section "Checkmate and stalemate" (`section Laws`)

`section Laws`, opening with `variable {a : Color} {p : Position}`.

| ID | English | Lean | Tag |
|---|---|---|---|
| L2.1 | `SpecWinsIn a 0 p` holds exactly when the other side is to move at `p` and is checkmated: `a` has already won. | `theorem specWinsIn_zero_iff : SpecWinsIn a 0 p ↔ p.turn = a.other ∧ Checkmate p` | [sanity] |
| L2.2 | In a stalemate (FIDE 5.2.1), neither side wins. | `theorem not_specWins_of_stalemate (h : Stalemate p) : ¬ SpecWins a p` | [sanity] |

Notes.
- These are THEOREMS G2 in FIDE terms, and they check that the definitions say what their
  docstrings say: with no budget, only a position that is already checkmate (with the right side to
  move) is a win (L2.1); and the guard of `replies` makes stalemate a win for nobody (L2.2).
- Both are proved from the definitions by `cases`, without the generator: `play_turn` (Rules) and
  `Color.other_other`, `Color.self_ne_other` (Basic) are the only lemmas used. `#print axioms` shows
  `propext` and `Quot.sound` for both.
- The chess-game versions (`Chess.winsIn_zero_iff`, `Chess.not_wins_of_stalemate`) remain in
  `Chess.ChessGame`; through `Chess.ChessGame.Fide` each now also follows from the other, but
  neither is restated.

---

## 3. Design choices, with reasons

1. **Import `Chess.Rules` only** (ChessGame review C2). The trusted reading of a headline should not
   contain the generator or the abstract game. Every name used here (`Legal`, `Position.play`,
   `Checkmate`, `Stalemate`, `Position.turn`, `Color.other`) is in `Chess.Rules` or below it. The
   definitions use only `Chess.Rules.Defs`; `Rules.Laws` is needed only to prove the G2 lemmas
   (`play_turn`). An independent review (`docs/reviews/G8_REVIEW.md`) checked the constant closure.
6. **Meant for positions in which the side not to move is not in check**, such as every `fen`
   position (`Position.Sane`) and every position reached from one by legal moves. Elsewhere `Legal`
   allows the capture of a king, after which that side can never be checkmated (G8 review, F1).
   FIDE says nothing about such positions, so the definitions are left unguarded.
2. **The same three rules as `Game.Forces`, written out**, rather than a second `Game` instance
   whose moves are `Legal`. A `Game` needs a finite list of available moves; `Legal` is a relation,
   and listing it is exactly the generator's job. Writing the rules out keeps this file free of
   lists.
3. **The `Spec` prefix**, so that `Chess.WinsIn` (the chess game) and `Chess.SpecWinsIn` (FIDE,
   written out) can sit side by side, and every bridge theorem is named `x_iff_specX`.
4. **No decision procedure.** Claims are decided or certified through `Chess.Game` (search,
   certificates) and carried here by `Chess.ChessGame.Fide`. A decision procedure here would be a
   second search to prove correct.
5. **The two G2 lemmas are proved directly, not through the bridge**, because their job is to check
   these definitions, independently of the generator.

## 4. Open items

1. The bitboard layer (Stage 5) and the clocked game (Stage 4, THEOREMS G12–G15) will want their own
   bridges to the same definitions. G15's "a `WinsIn` win with clock headroom is a FIDE win" would
   then be stated with `SpecWinsIn` and a clock hypothesis.
2. If the owner wants `Spec` to be a namespace rather than a prefix (`Chess.Spec.WinsIn`), it is a
   rename of the five definitions and of the theorems whose names mention them; the prefix was
   chosen so that a file opening `Chess` sees both vocabularies without ambiguity.
