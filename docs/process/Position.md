# Process log: `Chess.Position`

The record of the back-and-forth between the English specification (`docs/spec/Position.md`) and
the Lean (`Chess/Position.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written in the library: none.

**Inputs read.** `docs/DESIGN.md` (whole file; §4.3–§4.6, §5.5, §7.4 and §8.2 most closely),
`docs/THEOREMS.md` (§0.5, R4, R6–R11, M10, M11, G16, C1–C3, §9), `docs/research/lean-engineering.md`
(§2, §5, §6, §10), `Chess/Basic.lean` (whole file), `docs/spec/Basic.md`, `docs/process/Basic.md`
and `docs/reviews/Basic.md` (conventions, and review items C1, C4, C5, C8 addressed to later
modules), and the prototype's `chess-lean/ChessProof/Basic.lean` (nibble codes 1–6 and 9–14,
`castle : Nat` bit flags, `get bd s` by shift and mask).

**What the draft fixes.** 37 definition entries (D1.1–D6.9) and 39 lemma entries (P1.1–P5.10,
none in section 3, several grouping two to four Lean lemmas), in six file sections: Boards; Piece codes and packed
boards; Moves; Castling rights; Positions; Display; plus a test list.

**Facts checked in Lean 4.28 before writing them down.** Every snippet in the spec was translated
into one scratch file importing the built `Chess.Basic` (scratchpad only, nothing in the library).
It elaborates with no errors in about 2 s, all lemmas proved by the plans the spec gives. Along the
way:
- `Board` as a `def` works with application `b s`, dot notation `b.set`, `funext` and a named
  `DecidableEq` instance; `decide` and `decide +kernel` use it.
- `ext s` on a board goal also applies `Option.ext`; proofs use `refine Board.ext fun s => ?_`.
- `Fin 8` literal patterns (`backRankKind`) are accepted, exhaustive, and evaluated by `decide`.
- `Piece.ofCode` as a search of `Piece.all` gives the round trip by `revert pc; decide`. Kernel cost,
  five `decide +kernel` comparisons of a literal board after two `set`s: about 55 ms each with the
  search, about 35 ms with a hand-written `match`. The search is kept (spec §8 item 4, with the
  fallback).
- `hexDigit_ofHexDigits` by induction with core's `Nat.div_div_eq_div_mul`; `unpack_pack` from it
  through a helper `Square.getElem?_all_index` that really belongs in `Basic`.
- `Board.pack Board.initial` evaluates to
  `0xA89CB98A77777777000000000000000000000000000000001111111142365324`, and both that and the
  literal after 1. e4 are kernel-checked against `set` chains.
- A whole-type quantifier over `CastlingRights` (16 values through four `Bool`s) makes every
  castling-rights lemma, including extensionality and antisymmetry, a `decide`; all of them
  together take under a second.
- The `Move` quantifier instances (64 × 64 × 5) work, and the bounded-quantifier `rfl` tests pass
  with `priority := low`; a full `∀ m : Move` sweep takes about 4 s, so tests avoid it.
- Two traps found and written into the spec: inside `namespace CastlingRights` a bare `none` means
  `CastlingRights.none` (D4.5); and a structure instance `{ board := …, turn := … }` whose second
  line is indented less than its first field does not parse (§7).
- The diagram printer produces exactly the text the spec quotes.

**Decisions taken in the English, beyond DESIGN** (each argued in spec §8):
1. `set_comm` is **not** `@[simp]` (DESIGN §4.3 lists it with the simp lemmas): a permutation lemma
   makes simp's normal form depend on term order. Added `set_set` and `set_eq_self`.
2. `Piece.ofCode` searches `Piece.all`, so the code table is written once.
3. New helper names: `squareCode` (code of a square's contents, 0 if empty), `hexDigit`,
   `ofHexDigits`; `Board.hexDigit_pack` is the lemma `unpack_pack` is proved from.
4. Packed digits by division (`n / 16 ^ i % 16`), not shifts, for the proofs; digit `i` is the square
   with `index` `i`.
5. `CastlingRights` fields in FEN order (`whiteKingside`, `whiteQueenside`, `blackKingside`,
   `blackQueenside`); all-rights value named `CastlingRights.full` (not `.all`, which means a list of
   values in this library); `@[ext]` on `ext_get`, not on the structure.
6. Whole-type quantifier instances for `Move` and `CastlingRights`, `priority := low`, with the
   `rfl` tests (Basic review C1).
7. `Position.decEq` compares turn, castling and en passant target before the board.
8. The initial board is computed from `backRankKind` and `relRank` through `startingPiece`, with a
   colour-symmetry sanity theorem; the packed literal is only a test.
9. `Move` gets a hand-written UCI `Repr` (Basic review C5) instead of the derived one DESIGN §4.1
   names; `Board` and `Position` print as diagrams.
10. `Wing` stays in `Basic` (D7.1); this module only adds the rights.

**Questions for the translator and the critic** (spec §9 lists them with context):
- Should `Square.getElem?_all_index` (P2.7) move to `Basic` now?
- Keep `get_revoke_of_ne` (conditional, not simp), or add one unconditional simp equation for
  `(cr.revoke c w).get c' w'`?
- `Option.or` in `Board.initial`: clear enough, or a `match`/`if` instead?
- `Repr Move` as UCI, or derived `Repr` plus `ToString`?
- Keep the name `CastlingRights.none` despite the `Option.none` hazard, or rename it?
- Is ~55 ms per kernel board comparison acceptable for the Stage 1 demonstration, or should
  `ofCode` become a `match` now?

**Open items for others (not edited, outside this module's files).**
- `Basic`: `Square.getElem?_all_index` belongs next to `Square.mem_all`.
- DESIGN §4.3 lists `set_comm` among the `@[simp]` lemmas; DESIGN §4.1 says `Move` derives `Repr`.
- Owner: the square literal elaborator of Basic review C4; this spec's tests use `⟨file, rank⟩` with
  the algebraic name in a comment until it is decided.

**Next.** Round 2: the critic reviews the English; then the translator writes
`Chess/Position.lean` in spec order, adds `import Chess.Position` to `Chess.lean`, and records here
every place the Lean forced the English to change.

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator, answering the Round 1 English critique (A1–A6, B1–B12,
C1–C8). Every item was taken; none was rejected. Lean written in the library: none yet.

**[A] Contradictions and false statements.**
- **A1 (R2 not delivered).** The header no longer claims R2 for `Move` and `CastlingRights`. A new
  paragraph says they meet only the decidability half, on purpose, and why; §3 and D4.6 point to
  it. §9 item 0(a) asks THEOREMS to list only `Color`, `Kind`, `PromoKind`, `Wing`, `Square`,
  `Piece` under R2.
- **A2 (R8's hypothesis).** D4.8 now says the module supports DESIGN §4.5's unconditional R8, which
  is stronger than THEOREMS' `castling_play_le (h : Legal p m)`; §9 item 0(b) asks THEOREMS to drop
  the hypothesis.
- **A3 (interface rule overclaimed).** Rewritten: no function takes rights to rights containing one
  its input lacked; the only such functions are `revoke` and `revokeAll`, both `≤` their input
  (P4.10); this makes R8 *provable*, and `Chess.Rules` proves it. The constructor appears only in
  literals: parsers, checkpoints, tests (which resolves the clash with §7's test literal). §8 item 9
  reworded to match.
- **A4 (`epTarget` refers to a last move).** New docstring: `some t` means the previous move was a
  two-square advance over `t` (FIDE 3.7.3.2); set after every double push (PGN convention, not
  Stockfish's). D5.1 now says that for literal positions the field meanings are a convention the
  author must follow and that `Position` enforces none of them, naming python-chess's
  `fen(en_passant="fen")` as the matching generator setting.
- **A5 (castling flag is not "still allowed").** Structure, field, `get` and `Position.castling`
  docstrings now speak of the FEN flag / the right held, say it is lost when king or rook moves or
  the rook is captured on its home square, and say it does not mean castling is possible now. P4.2
  and P4.3's English changed from "allowed" to "holds".
- **A6 (`Kind.letter` and SAN).** "The upper-case FEN letter …; algebraic notation uses the same
  letters but omits P."

**[B] Hidden choices.**
- **B1 (rank numbering).** §0 gained a rule: "rank N" (1–8) is the chess name; 0-based values only
  in code. D5.4 and P5.5 rewritten ("home rank (`relRank` 0)", "second rank (`relRank c = 1`)").
- **B2 (`unpack` ignores digits).** D2.6 docstring adds "(13 to 15)" and "Digits beyond the 63rd are
  ignored"; a note says malformed literals are not rejected.
- **B3 (`pack` is not "the" number).** Docstring: "the number below 16 ^ 64 whose …"; a note states
  exactly when `pack (unpack n) = n`.
- **B4 (`Move` presupposes a piece).** Field docstrings "The source square." / "The destination
  square." / promotion "meaningful only when a pawn reaches its last rank"; a note lists `a1a1` etc.
  as values.
- **B5 (castling encoding).** Docstring names e1g1, e1c1, e8g8, e8c8, "never king-takes-rook; no
  Chess960".
- **B6 (`revoke` "removed").** "set to not held (whether or not it was held)"; same for `revokeAll`.
- **B7 (`CastlingRights.none`).** The hazard text shrank to one paragraph and now also covers
  THEOREMS R6's `p.castling = none`. The rename to `.empty` is recorded as the critic's
  recommendation in §9 item 6; the name stays `none` (the task assigns that name) until the owner
  decides. §9 item 0(c) asks THEOREMS to qualify R6's `none`.
- **B8 (`default`s disagree).** §8 item 12 now says so on purpose, and that no proof reads a
  `default`.
- **B9 ("exactly").** `Position` docstring: "It holds what decides which moves are legal and what
  they do; no move clocks and no history."
- **B10 ("64 comparisons").** "at most 64 comparisons" in D1.3 and D5.2.
- **B11 (`backRankKind` "its side's").** "of either colour's home rank (the same for both)".
- **B12 (`Board.initial` mechanism).** Docstring states the meaning; open item 4 closed in favour
  of `Option.or`.

**[C] Wording.** C1: "the `i`-th hexadecimal digit (the least significant is the 0th)" as a §0 rule
and in §2's intro, D2.4, D2.6, D2.7, P2.6, P2.8, P2.10. C2: D2.2 parenthetical fixed. C3: §7's
literal explanation reads right to left consistently. C4: header says `Std.Format` is core's.
C5: "found early in the sweep" replaced by "(through D3.2's `∃` instance)". C6: P5.8 says "32
pieces, pawns included", and §0 says "piece" includes pawns. C7: §0 states the explicit/implicit
rule (section `variable`s are the implicit names of rewrite lemmas; lemmas meant to be applied bind
explicitly and shadow). C8: FIDE 3.7.3.2 added to §0.

---

## Round 3: translation feedback

Date: 2026-11-01. Author role: translator. Lean written: `Chess/Position.lean` (96 declarations,
each with its spec docstring), and `import Chess.Position` added to `Chess.lean`. `lake build`
succeeds with no errors, no warnings, no `sorry` and no `native_decide`; the module elaborates in
about 2.4 s. `#print axioms Board.unpack_pack` gives `propext, Quot.sound`; the castling lemmas
need only `propext`. Every lemma was proved by the plan the spec gives; nothing is marked
`-- TARGET:`.

The translation went through in spec order, definition by definition, and every proof plan worked
as written. The places where the Lean forced a decision the English had not made, or where the
English was awkward to translate, and what changed in the spec:

1. **One English sentence for several Lean lemmas.** Rows P2.4, P4.9, P4.10, P4.11, P4.12, P5.1
   and P5.8 each hold two to four Lean theorems but one English sentence, while §0 says "the Lean
   docstring of a lemma is its English column". Each theorem needs its own docstring, so the
   translator had to split the sentences, and for `revokeAll_le` invent one. *Spec change:* §0 now
   says a multi-lemma row gives one sentence per lemma, separated by " / ", in order; the seven rows
   were rewritten that way, matching the Lean word for word (P4.10's second sentence: "(R8)
   Revoking all of a colour's rights never adds a right."). §0 also says bold in the English
   column is for this document only; the docstrings drop it (P2.9, P4.10).
2. **Lean scopes for the section `variable` lines.** The English gave each section a `variable`
   line but not the Lean scope that holds it, and that scope decides how names are written. The
   translation uses `namespace Board` for the §1 lemmas (so `set`, `set_ne`), `section
   PackedBoards` for §2, `namespace CastlingRights` for D4.2–D4.8 and the §4 lemmas (so `get`,
   `revoke_le`, and the D4.5 name hazard applies throughout), and `section InitialPosition` for §5.
   Names beginning with another namespace (`Piece.code`, `Square.getElem?_all_index`) are written
   in full rather than by reopening it. *Spec change:* §10 records this layout.
3. **`set_ne` orientation under `simp`.** §1 claimed `simp [Board.set_ne, h]` finds the frame
   lemma in R4 proofs. Checked in a scratch file: with `h : t ≠ s` it works (even `simp [h]`),
   but with `h : s ≠ t` `simp [h]` makes **no progress**; `Ne.symm h` is needed. On concrete
   squares plain `simp` works, since the side goal is decided. *Spec change:* the §1 note now says
   exactly this, so the `Rules` translator knows which way round to state hypotheses.
4. **P2.6's proof needed one more step.** After `Fin.ext` the goal is `Fin.val` of two anonymous
   constructors, which `rw [Nat.pow_succ]` cannot see through; a bare `simp only` reduces it.
   *Spec change:* the proof note mentions it.
5. **`revokeAll_le`'s argument order.** "From `revoke_le` twice and `le_trans`" leaves the order
   open; since `revokeAll` revokes kingside first, the queenside `revoke_le` is the first argument
   of `le_trans`. *Spec change:* the note gives the term.
6. **The 100-column limit versus §7's diagram test.** The `#guard` string is 250 characters on one
   line. It is split with Lean string gaps (`\` at a line end inside the literal, which also skips
   the next line's indentation), and the test still passes. *Spec change:* §10 says so.

Checked and needing no change: `Board` as a `def` takes application and dot notation; `ext c w`
on castling rights goes through `ext_get` and yields the `∀ c w` goal; `simp
[CastlingRights.get_revoke_of_ne]` closes a concrete instance (the disjunction is decided); the
derived `default : CastlingRights` prints as all four flags `false`, as §8 item 12 now says; the
diagram of a position with Black to move, no rights and target e3 prints
`Black to move, castling -, en passant e3`.

**Still open for others** (spec §9): THEOREMS edits to R2, R8 and R6 (item 0); moving
`Square.getElem?_all_index` to `Basic` (item 1); square literals (item 2); the unconditional
`get_revoke` equation, not added because no `Rules` proof asks for it yet (item 3); `Repr Move` as
UCI (item 5); and the owner's choice between `CastlingRights.none` and `CastlingRights.empty`
(item 6).

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner. Input: the Round 4 critique of `Chess/Position.lean`
against `docs/spec/Position.md` (items F1–F7, E1–E7, P1–P5). `lake build` stays green (5 jobs, no
errors, no warnings, no `sorry`, no `native_decide`); every Lean docstring (112) still appears word
for word in the spec (checked by script, whitespace-insensitive). Every line is at most 100
characters.

**English fixed first, then the Lean made to match.**

1. **F1, `Board.pack`'s docstring claimed an unproved bound.** "The number below 16 ^ 64" is kept,
   and the bound is now a lemma: P2.7 `ofHexDigits_lt` (`ofHexDigits l < 16 ^ l.length`, induction
   and `omega`) and P2.10 `Board.pack_lt` (`b.pack < 16 ^ 64`, from P2.7 by `List.length_map` and
   `Square.length_all`). D2.7 now says which lemma backs each half of the docstring.
2. **F2, proof order.** The P2 table is renumbered to the Lean order: P2.6 digits, P2.7 bound
   (new), P2.8 `Square.getElem?_all_index`, P2.9 `hexDigit_pack`, P2.10 `pack_lt` (new), P2.11
   `unpack_apply`, P2.12 `unpack_pack`. Proof notes and cross-references (D2.7, §8 item 7, §9 item
   1) follow.
3. **F3, D5.2's false reason.** Deriving `DecidableEq Position` does work (`Board.decEq` exists
   first). D5.2 now gives the one true reason, the order of comparison (board last), and records
   that Round 3's second reason was wrong.
4. **F4, "changed only by `revoke` and `revokeAll`" is a convention.** The `CastlingRights`
   docstring now says "By convention … the fields stay public for literals, so it is `Chess.Rules`
   (R8) that proves a move adds no right." D4.1's interface rule is retitled a convention, says
   `{ cr with whiteKingside := true }` typechecks anywhere, and why the constructor stays public.
   §8 item 9 and the module docstring say the same.
5. **F5, `CastlingRights.none`.** The hazard is recorded as confirmed in D4.5, and §9 item 6 notes
   that both critics recommend `.empty`. **Not renamed**: still an owner decision.
6. **F7, `promo`'s forward promise.** D3.1 now tells the `Rules` review to hold `PseudoLegal` to
   it both ways.
7. **P3, R9.3 needs the converse direction.** Added P4.8, `get_revoke` and `get_revokeAll`, the
   unconditional equations `(cr.revoke c w).get c' w' = (cr.get c' w' && !(c' == c && w' == w))`
   and `(cr.revokeAll c).get c' w = (cr.get c' w && !(c' == c))`, both `revert …; decide`, not
   `@[simp]`. Checked in a scratch file: `simpa [get_revoke, get_revokeAll]` takes a `true` read of
   `(cr.revoke .white .kingside).revokeAll .black` back to `cr`. P4.8 onwards are renumbered
   (P4.9 `le_def` … P4.13 `revoke_comm`); §9 item 3 is closed.

**Lean simplified without changing meaning.**

8. **E1.** `hexDigit_ofHexDigits`'s successor case is now `rw [List.getD_cons_succ, ← ih i]`,
   `Fin.ext`, and one `simp only` with the division lemmas and `v.val / 16 = 0`: no rewriting in a
   hypothesis, no bare `simp only`, no `congr 2; omega`. The spec's proof note says it in words.
9. **E2.** `squareCode` renamed `contentsCode` (it takes a square's contents, letter `x`, not a
   square), and its lemma `ofCode_squareCode` renamed `Piece.ofCode_contentsCode`, beside its
   siblings `Piece.ofCode_code` and `Piece.ofCode_zero`. `hexDigit` and `ofHexDigits` are left
   public; D2.4 now calls them plumbing used only in §2.
10. **E5.** `instance : Trans (α := CastlingRights) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans⟩` after
    the order lemmas, so R8 can be a `calc` (checked). No `ite_le` lemma: `revoke_le` and the
    `Trans` instance cover `play`'s conditional revocations once it is written; add it if the
    `Rules` proof asks.
11. **E6.** `letters` is `filter` then `map (·.1)` over a named `table`, with no `filterMap` and
    no `Option.none`; `rankLine` uses `((b ⟨f, r⟩).map (·.letter.toString)).getD "."`;
    `Position.diagram` uses `(p.epTarget.map Square.name).getD "-"`. The `#guard`s still pass, and
    a new one checks the diagram's last line for Black to move, no rights and target e3. The
    `Repr` precedence quirk is noted in the spec and left alone (display is untrusted).
12. **E7 and P1.** The module docstring's implementation notes now carry the `ext s : 1` advice
    and the `t ≠ s` orientation rule for `set_ne`, for people who read the Lean and not the spec.

**Other documents (F6).**

13. `THEOREMS.md`: §0.5 sketch says `Wing`, `CastlingRights` (read by `get c w`) and
    `Option PromoKind`; R2's English lists `Color`, `Kind`, `PromoKind`, `Wing`, `Square`, `Piece`
    and says `Move` and `CastlingRights` have quantifiers only; R4 no longer lists `set_comm` as
    `@[simp]`; R6 says `CastlingRights.get c w` and `p.castling = CastlingRights.none`; R8 is the
    unconditional `castling_play_le (p : Position) (m : Move)`. Spec §9 item 0 is closed.
14. `DESIGN.md`: §2's glossary row and §8.2 say a right is "still held", not "still allowed";
    §4.3 drops `set_comm` from the simp lemmas and states the `t ≠ s` orientation; §12 records
    which of its requested THEOREMS edits are now made.

**Not done, and why.**

- **E3** (`Option.decidableForall`/`decidableExists` in `Basic`, making the `Move` instances
  one-liners) and **E4** (`Square.flip`, `Piece.flip` in `Basic`, so P5.10 reads
  `Board.initial s.flip = (Board.initial s).map Piece.flip`): both need `Basic`, which this
  module's agents do not edit. Recorded as spec §9 item 7 for the next `Basic` revision.
- **F5** rename to `CastlingRights.empty`: owner decision (spec §9 item 6).
- **P4, P5** (the `ofCode` search cost and the slow whole-`Move` sweep): no change needed; the
  fallback (spec §8 item 4) and DESIGN §5.6's generator route stand.

---

## Note, 2026-11-02 (test library review round): the tests stay in the module

Spec §7 said the tests stay at the end of the file "until the test library exists". The library
exists, and its round kept these tests here (0.14 s; `docs/process/ChessTest.md` §1). The sentence
now says so. No Lean changed.

---

## Round 5 (2026-11-02, ROADMAP step 6): `Piece.ofCode` as a table

Spec §8 item 4 had kept `Piece.ofCode` as a search of `Piece.all` and named a fallback "if the DESIGN
§7.4 benchmarks show board reads dominate". The Gotham certificate is that benchmark: 64 reads of a
packed board cost 34 ms with the search and 13 ms with a `match` (`decide +kernel`); a checkpoint
`p.play m = q` went from about 0.10 s to 0.04 s and a mate leaf about 15 % faster (MoveGen process
log, Round 5). The fallback was taken as written: D2.2's body is the 13-arm `match`, and the new
P2.0 `Piece.ofCode_eq_find?` proves it equal to the old search by `decide`, so the code table D2.1
still decides every code's meaning. P2.1–P2.5 kept their `decide` proofs unchanged. No other
definition changed.

---

## Round 6 (2026-11-02, readability round): the castling-rights convention, `ofCode`'s notes, two definitions moved in

Inputs: findings of the readability and fidelity audit, each reproduced by two skeptics; Rules
spec §12 item 7; ChessGame review C5. Spec first, then the Lean.

- **`CastlingRights` docstring** (trusted text, D4.1). It said rights are "changed only with
  `revoke` and `revokeAll`", which has been false since Rules wrote step 4 with `ofGet` (Rules
  review C5). It now says a move changes them only through `Move.castlingAfter`, which builds them
  with `ofGet` and can only clear a flag, and names `castling_play_le` as R8. The module docstring
  and D4.1's interface rule say the same. `revoke`, `revokeAll` and their lemmas stay (a small
  algebra used by tests and literals), but `revoke_le` and `revokeAll_le` no longer carry "(R8)";
  P4.13's note no longer claims `play` uses them.
- **Moved in.** `CastlingRights.ofGet` and `get_ofGet` from Rules (D4.6b, P4.3b);
  `CastlingRights.all` with `mem_all` and `length_all` from ChessGame (D4.6a, P4.3a);
  `Board.squaresOf` with `Board.mem_squaresOf` from ChessGame (D1.6, P1.8). Docstrings and proofs
  unchanged; only `mem_squaresOf` lost its now redundant binders `{b} {t}`, which the
  `namespace Board` variable line provides. `squaresOf` is trusted here as it was in ChessGame
  (`Position.Sane` counts kings with it); MoveGen now uses it in place of its own copy.
- **`Piece.ofCode`'s notes.** The module docstring still described the Round 1–4 body ("its inverse
  found by search", "a `match` can replace its body"). It now says that `ofCode` is a second table,
  for speed, tied to `Piece.code` by `ofCode_eq_find?` and `ofCode_code`. Spec §8 item 4 and §9
  ("the way `ofCode` searches `Piece.all`") are reworded to match.

Checks: as in the Rules process log, Round 8 (all four builds green). `scripts/check_docstrings.py
Chess/Position.lean`: 120 docstrings, none missing.
