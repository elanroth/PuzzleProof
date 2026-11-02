# Process log: `Chess.ChessGame`

The record of the back-and-forth between the English specification (`docs/spec/ChessGame.md`) and
the Lean (`Chess/ChessGame.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written in the library: none.

**Inputs read.** `docs/DESIGN.md` (all; §3.1, §4.6, §6.1, §6.4–§6.5, §7.3–§7.4, §8.6, §10 most
closely), `docs/THEOREMS.md` (§0, §1, G1, G2, G8, M11, §7, §10), `docs/research/lean-engineering.md`
(§2, kernel reduction of `String` and `Nat`), `Chess/Game.lean`, `Chess/MoveGen.lean`, and the
declarations of `Chess/Rules.lean`, `Chess/Position.lean` (all of the castling, position and display
sections) and `Chess/Basic.lean`; `docs/spec/MoveGen.md` (§0, §8, §10, for format) and
`docs/process/MoveGen.md` (Round 1, for format); the review findings addressed to this module:
Game review C1 (explicit `decMated`, `abbrev`) and C8 ("without move-count rules" in headline
docstrings), Position review C3 (the display letters become trusted); and the prototype's
`chess-lean/ChessProof/Fen.lean` (what to drop: `pieceCode` returning 0 for unknown letters,
`epSquare` returning 64, `fenChars` returning `default` on a malformed string, `uci` returning
`default`).

**What the draft fixes.** 5 game definitions (D1.1–D1.5), 9 writers (D2.1–D2.9), 13 untrusted
readers (D3.1–D3.13), 9 acceptance definitions with 3 instances (D4.1–D4.9); 6 game lemmas
(L1.1–L1.6), 14 notation lemmas proved now (L5.1–L5.14), 7 completeness lemmas as [target]
(L5.15–L5.21), the tests of §6, and the Stage 2 plan for G8 (D7.1–D7.4, L7.1–L7.6).

**The one decision that shapes the notation half: readers propose, writers dispose.** A string is
accepted only if writing the proposed position (or move) back gives the string. Considered and
rejected: a strict, field-by-field parser (the prototype's shape, made strict), which is all trusted.
Consequences, all recorded in spec §8 (choices 4, 5, 7):
- the trusted base is the writers, `splitOn` and the guards; the readers are untrusted;
- the soundness half of M11 is a Stage 1 theorem (`readFEN_sound`, `fen_spec`, `parseUCI_sound`),
  so "what does `fen "…"` mean" has a proved, reader-free answer;
- accepted FEN is exactly canonical FEN (castling letters in `KQkq` order, no adjacent digits);
- injectivity of the writing (two positions never share a FEN) is the remaining trusted claim until
  the [target] group L5.15–L5.21 is proved.

**Facts checked in Lean 4.28 before writing them down** (scratch files importing the built `Chess`
library; nothing in the library was written):
- Every definition of spec §1–§4 elaborates as written, and every lemma tagged [core] or [sanity]
  is proved (no `sorry`): including `intercalate_splitOn` (by induction through `splitOn.go`),
  `readFEN_sound`, `parseFEN_eq_some_iff`, `fen_spec`, `Square.toList_name` (`decide +kernel` over
  64 squares), `Move.toList_toUCI`, `parseUCI_sound`, `toUCI_uci`, `Board.mem_squaresOf`.
- Every test of spec §6 passes. The whole scratch module elaborates in about 21 s, of which about
  20 s is kernel checking of the tests; the `MateIn .white 1` example is about 3 s.
- **`Move` inside a `Game.…` declaration is `Game.Move`.** Writing `Move := Move` in `Game.chess`, or
  `(m : Move)` in `theorem Game.chess_play`, fails with "type expected, got (Move : Game → Type)":
  Lean opens the namespace `Chess.Game` while elaborating a declaration named `Game.…`. The spec
  writes `Chess.Move` there and states the rule in §0.
- With `Game.chess` and the four chess names as `abbrev`s: `Game.checkWin_sound` applies to a
  `Chess.WinsIn` goal; dot notation `h.mono`, `h.not_both`, `h.wins` works on `Chess.WinsIn`,
  `Chess.Wins`, `Chess.OnlyWinningMove` hypotheses; `(fen "…").turn = .white` is `rfl`.
- `String.toList` of a 56-character literal reduces in the kernel in well under a second, so
  parsers over `List Char` are kernel-friendly in 4.28. `Square.name.toList` and `Move.toUCI`'s
  character list also reduce quickly.
- Board construction, measured (DESIGN §10's open question): `(legalMoves (fen "<start>")).length =
  20` by `decide +kernel` took 4.8 s with the board as a list lookup (D3.5), 5.1 s with
  `Board.unpack` of a computed number, against 3.5 s for `Position.initial` itself; on Kiwipete
  10.8 s against 11.6 s. The list lookup was chosen.
- `by decide +kernel` against `by decide` as the default proof of `fen`: 1.9 s against 2.9 s for
  parsing and sanity-checking Kiwipete. Both report a bad string as "Tactic `decide` proved that the
  proposition `(…).isSome = true` is false".
- `#print axioms` on the `MateIn` test: `propext`, `Classical.choice`, `Quot.sound` ([kernel]).

**Deviations from DESIGN and THEOREMS, recorded in spec §9.** Four-field FEN accepted; a third
sanity condition (en passant target on the mover's relative rank 5); THEOREMS M11.2 without
`normalize`; M11's soundness moved to Stage 1; G8 lemma names.

**Requests to other modules, recorded in spec §9.** Position: rename the "Display" heading (the
letters are now trusted), and host `CastlingRights.all`. Invariants (Stage 2): `WellFormed` should
include the en passant rank condition and imply `Position.Sane`.

**Open for the critique.** Whether the four-field FEN is worth its extra case (spec §10 item 4);
where G8 lives (item 2); whether the [target] budget of about 150 lines is right.

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator, revising the English after the Round 1 critique. Every
finding was accepted; none was rejected. Changes to `docs/spec/ChessGame.md`, by finding:

**A (false or misleading).**
- A1. §7's filter paragraph rewritten: the Stage 2 filter is `p.Sane ∧ WellFormed p`. It never
  accepts a string Stage 1 rejected, an accepted string denotes the same position, and Stage 1
  strings whose positions are not `WellFormed` become compile-time errors (the Stage 2 translator
  re-runs every literal). §9 request 3 is now optional.
- A2. L5.19 is now general: `readFEN_intercalate (p) (hcl : ClockFields cl)`, for every acceptable
  clock list. No separate "no space in a clock field" hypothesis: it follows from `IsNumeral`, and
  the proof plan says so. The old L5.19 is the corollary L5.20 `readFEN_toFEN`; old L5.20 and L5.21
  are renumbered L5.21 and L5.22. The `↔` paragraph notes that L5.19 applies through
  `s = String.ofList s.toList`.
- A3. `Position.Sane` structure docstring: "an en passant target, if any, lies on the rank that a pawn
  of the side not to move crosses in a two-square advance".
- A4. `epTarget_relRank` docstring: "the sixth rank counted from the side to move (`relRank p.turn =
  5`, counting from 0)". The `EnPassantMove` note says the same. §0 gains a paragraph on rank
  indices; D2.3 says "rank index `r` (rank `r + 1`)".
- A5. Choice 5 limited to the board, side to move and castling fields; choice 8 rewritten (the
  Stockfish/Lichess `-` convention, the 1.e4 example, the missing transfer lemma, the advice to
  authors).
- A6, A7. `emptyRun` and `rowChars` docstrings now state their range conditions.
- A8. *Canonical FEN* defined once (D4.3 notes); "accepted = canonical" split into the proved
  direction (L5.3) and the [target] direction (L5.19).
- A9–A11. L5.6, L5.15 and L5.16 English corrected to match their Lean statements.
- A12. Header: "the definition of `Game.chess` (D1.1)". Also fixed: the header cited D4.4 for
  `Position.Sane`, which is D4.5.

**B (ambiguities).**
- B1, B2, B3, B4. D1.2–D1.5 docstrings rewritten with one shared sentence ("chess as computed by the
  move generator … 'mated' means in check with no listed move"), "mated" instead of
  "checkmated", "whichever side is to move" in D1.2, the meaning of "other" in D1.5; a note on
  non-sane positions added after D1.5.
- B5. D1.1 docstring: moves are values of `Chess.Move`; play ends only by mate or no listed move; the
  list of absent rules includes dead positions, with the remark that none creates a forced mate.
- B6. §7 heading and a definition of "FIDE chess" (Articles 3 and 5.1, without 5.2.2 and 9).
- B7. `parseUCI` docstring states exactly what is accepted (`e2e2`, `e7e8`, `e1h1`).
- B8. `IsNumeral` and `ClockFields` docstrings state leading zeros, large values, move number 0.
- B9. `readFEN` docstring: what a field separator is.
- B10. `fenFields` docstring: the target is as stored; `play` stores one after every double push.
- B11. §0's [target] rule: keep the proved lemmas, log the rest, no other module relies on them.
- B12. Header names both missing guarantees: meaning (L5.18) and liveness (L5.19).
- B13. `emptyCount?` docstring shortened; a note on `9` and `0`.
- B14. `Board.ofRows` docstring: "both counting from 0".
- B15. L1.5 and L1.6 English.
- B16. §9 deviations: M11.3's `parseSAN_toSAN` dropped.

**C (minor).** Letter table extended (`e`, `o`, `w`, `ws`, rank indices); `s` as a square now only
in D3.5 and D3.10 (D4.4 and L5.9 use `t`); D4.2 uses `w` for a field. The slogan is "Readers
propose; the guard (writing back) disposes" everywhere. L5.14 split into L5.14a–L5.14e, one English
line each. `Wins` says "a bound fixed in advance". `not_kingAttacked_other` says "by the side to
move". `fen` says "the position whose FEN is `s` (up to clock fields)". `splitOn.go` docstring
reworded.

---

## Round 3: translation feedback

Date: 2026-11-01. Author role: translator. Lean written: `Chess/ChessGame.lean` (about 752 lines),
imported from `Chess.lean`. `lake build` succeeds with no warnings, no `sorry` and no
`native_decide`; the whole library builds in about 26 s, most of it the kernel tests of this
module. `#print axioms` on `fen_spec`, `readFEN_eq_some_iff`, `Position.fenFields_injective`,
`parseFEN_toFEN` and `parseUCI_eq_some_iff`: `propext`, `Classical.choice`, `Quot.sound`.

Every definition of spec §1–§4 went in as written in Round 2, in the same order, with the same
names and the spec's docstrings word for word. Every [core] and [sanity] lemma was proved by the
route the spec gives. Every test of §6 passes. The cases where the Lean forced a decision the
English had not made, or where the translation was awkward, each fixed in the spec:

1. **§1's `variable` line.** It declared `{m : Move}`, which no declaration of §1 uses (L1.2 binds
   its move explicitly, as `Chess.Move`, §0). Dropped. The `variable` line needs a scope, so §1 is
   `section ChessAsAGame … end ChessAsAGame`; the spec now names the section.
2. **L5.2's auxiliary statement needed a name.** The spec's proof route for `intercalate_splitOn`
   went through an unnamed statement about `splitOn.go`. Under the docstring-on-every-declaration
   rule it became the lemma `splitOn_go_join` (L5.2a, [core]) with its own English line.
3. **The [target] group was completed, over budget.** All of L5.15–L5.22 are proved, plus the two
   corollaries the spec asked for if the group was completed, now numbered L5.23
   (`readFEN_eq_some_iff`) and L5.24 (`parseUCI_eq_some_iff`) and given English lines. The group
   took about 220 lines with docstrings, against the estimate of 80–150. The §0 rule (Round 2, B11)
   keeps every fully proved lemma, so nothing was dropped. The spec's status line and header now
   say that the meaning (L5.18) and liveness (L5.19) guarantees are proved, so a reader no longer
   trusts injectivity of the FEN writing.
4. **Sixteen helper lemmas.** The proof plan's steps became named lemmas, each added to spec §5's
   completeness table with an English line and marked *(helper)*: `forall_mem_rowChars` (L5.15a),
   `readRow_emptyRun` (L5.15b), `splitOn_go_append` (L5.16a), `splitOn_go_join_pieces` (L5.16b),
   `mem_intercalate` (L5.16c), `readBoard_fenChars` (L5.17a), `Board.space_not_mem_fenChars`
   (L5.17b), `readTurn_fenChar` (L5.17c), `readCastling_letters` (L5.17d), `Square.ofName?_chars`
   (L5.17e), `Square.ofName?_name` (L5.17f), `Square.ofName?_epChars` (L5.17g),
   `space_not_mem_fenFields` (L5.18a), `space_not_mem_of_clockFields` (L5.18b), `readPromo_toList`
   (L5.22a), `readMove_toUCI` (L5.22b).
5. **"No row text contains `/`" is not a finite check over all digits.** The proof plan called it
   a finite check. `Nat.digitChar` is a sixteen-way `if` chain on a free `k`, and neither `decide`
   nor `split` closes `∀ k, k.digitChar ≠ '/'`. The fix keeps the statement small: the row lemma
   L5.15a takes the property only for `k < 9` (a decidable bounded quantifier) and the same bound
   `k + row.length ≤ 8` as L5.15. The English proof plan now says so.
6. **Which finite checks need the kernel.** `∀ c` (colours) goes by `decide`. `∀ cr` (castling
   letters) and `∀ t` (square names) reduce `String.toList` and go by `decide +kernel`. `Option
   Square` has no `Decidable ∀` instance, so the en passant field is split into `none` and `some t`.
   The proof plan now says which is which.
7. **L5.19 needed no extra hypothesis.** The critique (A2) suggested a hypothesis that no clock
   field contains a space. It is derived from `IsNumeral` (L5.18b: `' '.isDigit = false`), so
   `readFEN_intercalate` keeps the Round 2 signature.
8. **Binder letters.** The spec's proof of L5.10 named a move's squares `s` and `t`, but in `section
   Notation` `s` is a string. The Lean uses `t` and `t'` (letter table); the spec's proof note is
   updated.
9. **Test comment.** After the Round 2 renumbering, the round-trip test checks L5.20
   (`readFEN_toFEN`), not L5.19. Updated in the spec's §6 and in the Lean.

Nothing in the Lean required a change of a definition, a docstring of a definition, or a theorem
statement written in Round 2.

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner, applying the Round 4 Lean critique. Files changed:
`Chess/ChessGame.lean`, `docs/spec/ChessGame.md`, and three passages of `docs/THEOREMS.md` (G1, G8,
M11). Nothing else was edited; in particular `Chess/Position.lean` and `Chess/Basic.lean` belong to
other owners (F10 below). `lake build`: "Build completed successfully (9 jobs)", no warnings, no
`sorry`, no `native_decide`. `#print axioms` on `fen_eq_iff`, `uci_eq_iff`, `IsFEN.unique`,
`fen_toFEN`, `uci_toUCI`: `propext`, `Classical.choice`, `Quot.sound`. A script compared every Lean
docstring (102) with the spec after whitespace normalisation: all present word for word.

Principle of the round: the critique found no wrong Lean semantics, so the English was fixed first
(where it claimed too much or was vague), then the Lean docstrings were made to match, and only then
was the Lean restructured, without changing any definition's meaning.

**English that claimed too much, or was vague (spec first, then the Lean docstring).**
- F1 (`Game.chess` docstring). "None of these can make a forced mate exist where it otherwise would
  not" was true but pointed the wrong way. Now: "so a win here is a win under FIDE only when those
  rules do not intervene (THEOREMS G15)". A D1.1 note gives the concrete case (halfmove clock 149),
  and a new test proves by `decide +kernel` that `… w - - 149 80` and `… w - - 0 1` denote the same
  position.
- F2 (clocks). Choice 6 no longer says the clocks "carry nothing the library could use"; it says
  G15 needs the halfmove clock and M11 assigns it to the game layer. New open item 5 plans a clock
  reader with a writing-back guard (and notes that G15 headlines will need six-field FENs). The
  `fen` docstring now says "The clocks are not part of the position … (see THEOREMS G15)", and the
  module docstring has an implementation note on clocks.
- F3 (trusted base). The spec header and the module docstring now list exactly: `Game.chess` and
  the four abbreviations; the writers (with the letter tables and square names they use); the
  predicates `IsNumeral`, `ClockFields`, `IsFEN`, `Position.Sane`; and the statements of
  `fen_eq_iff` and `uci_eq_iff`. `splitOn`, the readers and the guards' code are named as untrusted.
  L5.15–L5.24 retagged [core]; §0's stale "allowed to slip" text replaced by a note on the retired
  [target] tag; the Status paragraph rewritten (F11).
- F4 (Main statements). Rewritten, led by `fen_eq_iff`, `uci_eq_iff`, the three characterisations,
  `IsFEN.unique` with `Position.fenFields_injective`, then the round trips and the G2 lemmas.
  `readRow_rowChars` and `splitOn_intercalate` are no longer listed (they are steps, not results).
- F5 (`fen` docstring). Now "the one sane position of which `s` is a FEN (`fen_eq_iff`; there is only
  one by `IsFEN.unique`)" and "a string that is not a FEN of a sane position is a compile-time
  error". The definite article is now justified by a cited lemma.
- F6 (`readChar`). "or one empty square if no piece has that letter" (the Lean is `[none]`).
- F7 (`rowChars`). The parenthetical with the wrong bound is replaced by: "A board row has eight
  squares and is written with `rowChars 0`, so every run is one of the digits `1` to `8`."
- F8 (choice 9). Lists all `String` values met: the input, `toFEN`'s output, and `Square.name`,
  `CastlingRights.letters`, `Move.toUCI`, each read through `String.toList`.
- F9 (THEOREMS). `Chess.game` → `Game.chess` everywhere (G1, G8, G12, G15, the index, the open
  questions); G8's names → `Chess.mem_chess_moves`, `Chess.chess_mated_iff_checkmate`,
  `Chess.winsIn_iff_specWinsIn` (also in the Stage 2 headline line); M11.2 now
  `parseFEN_toFEN (h : p.Sane) : parseFEN p.toFEN = some p` with English to match, and M11 gains a
  Status bullet (what is proved, M11.1 waiting for `WellFormed`, SAN dropped, clock reading open).
  Spec §9's deviation bullets record that THEOREMS now agrees.
- F10 (the "Display (untrusted …)" headings in Position.lean line 548 and Basic.lean line 1036).
  **Not changed: other owners' files.** Spec §9 request 1 now says it is still open and why it is
  the most important fidelity defect outside this file. Request to the Position and Basic owners:
  split the heading into "Notation (trusted: the FEN and UCI guards of `Chess.ChessGame` compare
  against these)" and "Display".
- F11 (housekeeping). Status paragraph split; table order fixed (below); request 2
  (`CastlingRights.all` to Position) marked still open.
- P1. The L7.3 note now says the congruence already exists (`Forces.trans` with `k := 0`).
- P3. Choice 8 now names THEOREMS G16 (`normalize`, `legalMoves_normalize`, `play_normalize`) as
  the lemma that makes headlines stated with tool-produced FENs transfer, and cites the critique's
  `decide +kernel` check that the Lichess FEN after 1.e4 is not `Position.initial.play (uci "e2e4")`.
- P5. A note after D1.5: Stage 1 `OnlyWinningMove` headlines need every alternative to lose
  (`Wins.not_both`) or stalemate; drawing alternatives wait for G9.
- P6. A note after D1.1: `Mated` and `OnlyWinningMove` rely on `Game.moves`' contract that no move is
  listed under two values; the obligation is MoveGen's (M4).

**The Lean, restructured without changing meaning.**
- E1, `IsFEN` (new D4.2a, trusted). `∃ cl, ClockFields cl ∧ s.toList = [' '].intercalate
  (p.fenFields ++ cl)` was written out three times; it is now one definition with a docstring, and
  the contract reads `readFEN_sound : … → IsFEN s p`, `fen_spec : IsFEN s (fen s h)`,
  `readFEN_eq_some_iff : readFEN s = some p ↔ IsFEN s p`, plus the new `IsFEN.unique` (L5.23a). The
  `readFEN` docstring's last sentence now says "exactly when `IsFEN s p` (`readFEN_eq_some_iff`)".
- E8 + E1. `readFEN_intercalate (p) (hcl) : readFEN (String.ofList …) = some p` became
  `readFEN_of_isFEN (h : IsFEN s p) : readFEN s = some p` (L5.19, same ID), named for what it means.
  `readFEN_toFEN` now goes through the new helper `Position.isFEN_toFEN` (L5.19a), and
  `readFEN_eq_some_iff` is `⟨readFEN_sound, readFEN_of_isFEN⟩`.
- Section structure. `splitOn` moved from "Writing (trusted)" to the start of "Reading (untrusted)"
  (spec D2.9 → D3.0): `IsFEN` joins with `intercalate` and never splits, so `splitOn` is reader
  machinery. "Accepting (trusted)" became "Accepting", with a section comment saying which of its
  definitions are trusted (the four predicates) and which are verified (the parsers, by three named
  lemmas). The spec's §4 quotes that comment; IDs D4.x are unchanged apart from the new D4.2a.
- P4, new section "Using `fen` and `uci` in proofs": `fen_eq_iff` (L5.25), `fen_toFEN` (L5.26),
  `uci_eq_iff` (L5.27), `uci_toUCI` (L5.28), each one to three lines. With `parseUCI_uci` (L5.11a,
  the UCI twin of `parseFEN_fen`). Checked: `(uci_eq_iff _).2 rfl` proves `uci "e2e4" = ⟨…⟩`.
- Shorter proofs. `parseFEN_fen` and `parseUCI_uci` are `(Option.some_get h).symm` instead of
  `simp [fen]`; `toUCI_uci` is `parseUCI_sound (parseUCI_uci h)`; `IsFEN.unique` and `fen_toFEN` are
  one line each.
- Order. The UCI round trip (L5.22a, L5.22b, L5.22) now precedes `readFEN_eq_some_iff` (L5.23), so
  the completeness table is in both file order and ID order without renumbering (F11).
- E2. `@[simp]` dropped from L1.1–L1.4. Checked after the change: `simp at h` still turns
  `m ∈ Game.chess.moves p` into `m ∈ legalMoves p` and `Game.chess.Mated p` into its conjunction;
  `rw [Game.chess_moves]` still works. Spec L1 notes and checklist updated.
- E4. `{cs : List Char}` dropped from `section Notation`'s `variable` line. The binder convention is
  now stated in spec §0 ("Binders"): `variable` arguments are implicit; a lemma rebinds a letter
  explicitly only when no hypothesis determines it (hypothesis-free equations, finite checks).
  Under that rule the explicit `(sep : Char)` of L5.2a/L5.2 and `(pc : Piece)` of L5.14c/L5.14d are
  the convention, not inconsistencies, so they stay.
- E7. A comment in `Position.Sane.decidable` says the restated conditions are deliberate.

**Declined or deferred, with reasons.**
- E3 (generic list lemmas in `namespace Chess`). Deferred to DESIGN as spec open item 6: there is
  no `Util` module yet, and moving `intercalate_singleton_cons` and `mem_intercalate` into `List`
  names would be the clash the critique warns about if core adds them. They stay here, beside
  their only users.
- E5 (`readBoard_fenChars` via `r.rev`). Tried a shorter proof with the definition unchanged:
  `simp` unfolds `Board.row` before it can use the row lemma, and the arithmetic step remains, so
  nothing was gained. The definition change would touch a trusted writer for a proof's sake, and
  `.reverse` matches "rank 8 down to rank 1" most literally. Kept.
- E6 (one idiom for digit characters). Kept `Nat.digitChar` in `emptyRun`. Switching to
  `Char.ofNat ('0'.toNat + k)` changes a trusted writer and makes "no row character is `/` or a
  space" a fact about `Char.ofNat` instead of a bounded finite check; the bound `k < 9` in
  `forall_mem_rowChars` is the honest price and is explained in the spec.
- P2 (M11.1 plan). No change needed; the spec already tells the Stage 2 translator to re-run every
  `fen "…"` literal.

**ID changes this round** (for readers of the critique): `readFEN_intercalate` → `readFEN_of_isFEN`
(L5.19); `splitOn` D2.9 → D3.0; new D4.2a, L5.11a, L5.19a, L5.23a, L5.25–L5.28. No other ID moved.
