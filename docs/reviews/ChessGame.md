# File-level design review: `Chess.ChessGame`

Reviewer role: file-level design reviewer. Date: 2026-11-01.
Read: `Chess/ChessGame.lean` (whole file), `docs/spec/ChessGame.md` (whole file),
`docs/process/ChessGame.md` (Rounds 1–4), and the parts of the other modules this file touches:
`Chess/Basic.lean` (enumerations, the "Display" section), `Chess/Position.lean` (`Board`, `Move`,
`Position`, the "Display" section), `Chess/Rules.lean` (`KingAttacked`, `InCheck`,
`EnPassantMove`, `play`, `Legal`, `Checkmate`), `Chess/MoveGen.lean` (`legalMoves`,
`legalMoves_sound`, `agreesWithLegal`), `Chess/Game.lean` (the declarations of the semantics,
search and certificates), `docs/DESIGN.md` (§1, §6.4–6.6, §7, §8), `docs/THEOREMS.md` (G8, G15,
G16, M11) and the other five reviews.

State at review time: `lake build` green ("Build completed successfully (9 jobs)"), no warnings,
no `sorry`, no `native_decide`, no line over 100 characters. 798 lines. All 102 Lean docstrings
occur word for word in the spec (checked by script, whitespace-normalised). Elaborating the module
takes **29.5 s**; without its `## Tests` section, **3.1 s** (both `lake env lean`, this machine).

Experiments were run in scratch files outside the library that import the built `Chess`.

## Changes made in this review

- **Spec only, one note corrected** (`docs/spec/ChessGame.md`, notes on D1.2–D1.5, last bullet).
  It said a file opening both `Chess` and `Chess.Game` "gets an ambiguity error". Checked: Lean
  resolves the overload by elaboration, so `WinsIn .white 1 p` works with both open; the error
  appears only where both readings elaborate, for example `(winsIn_zero_iff.1 h).1`. The note now
  says exactly that. No Lean, no docstring, no other file touched.

Every other point below is a recommendation.

---

## 1. Verdict

**Faithful, small where it must be small, and fully proved. Build on it.** I found no semantic
error. The four headline names say what their docstrings say, and the notation layer is the best
part of the library so far: the meaning of `fen "…"` is one trusted predicate (`IsFEN`) plus
`Position.Sane`, tied to the code by `fen_eq_iff`, and neither the readers nor the guards are
trusted. The concerns are about where Stage 2 code goes, about build cost once generated
certificate files import this module, and about a few helpers living in the wrong layer.

What is right and should not change:

- **Readers propose; the guard (writing back) disposes.** Total, lenient readers; writers that are
  short total functions; acceptance only if the proposal writes back to the input. Soundness came
  for free in Stage 1 and completeness (`readFEN_of_isFEN`) is proved, so a canonical FEN is never
  rejected and a string never means the wrong position. This is the same "compute, then check"
  idea as `legalMoves`, so the library has one pattern, not two.
- **`IsFEN` as the one trusted statement of what FEN text is**, with the contract stated in three
  short lemmas (`readFEN_eq_some_iff`, `IsFEN.unique`, `fen_eq_iff`). A reader of a headline needs
  the writers, four predicates and two statements. That is the right size.
- **`fen` and `uci` take an explicit auto-proved argument.** No default position, no `Option` in
  statements, and the failure message names the string (checked: "Tactic `decide` proved that the
  proposition `(parseFEN "…").isSome = true` is false").
- **`decMated` and `decEqMove` written out, `Game.chess` an `abbrev`** (Game review C1). Dot
  notation from `Chess.Game` works on the chess names (checked again: `h.mono` on a
  `Chess.WinsIn`).
- **`Mated` as `InCheck p ∧ legalMoves p = []`**, cheap order first, with G8 planned to equate it to
  `Checkmate`.
- **`Position.Sane` as a structure of three named, documented conditions**, separate from reading,
  so `readFEN_toFEN` holds for every position.
- **Everything over `List Char`.** No byte positions, kernel-friendly.

---

## 2. Concerns, in priority order

### C1 (high, cheap, other owners). The trusted notation is still labelled "untrusted"

This module makes `Kind.letter`, `Piece.letter`, `PromoKind.letter`, `CastlingRights.letters`,
`Move.toUCI` (Position) and `Square.fileChar`, `Square.rankChar`, `Square.name` (Basic) part of the
meaning of every `fen "…"` and `uci "…"`: `IsFEN` and `fen_eq_iff` are stated through them. Yet
`Chess/Position.lean` line 548 and `Chess/Basic.lean` line 1036 still head them
"Display (untrusted: nothing in the specification reads it)", and `docs/spec/Position.md` choice 13
says "Display is separate and untrusted". A reader who believes the heading skips auditing part of
what a headline means. This is the library's highest-priority fidelity defect, it has been "still
open" through four rounds and two reviews (Position review C3, this spec §9 request 1), and it is a
comment-and-spec change with no proof impact.

Recommendation: assign it now to the Position and Basic owners (I did not edit their files or
specs). Split each section into

- `/-! ## Notation (trusted: the FEN and UCI guards of `Chess.ChessGame` compare against these) -/`
  holding the letters, `CastlingRights.letters`, `Move.toUCI`, `Square.fileChar`, `rankChar`,
  `name`; and
- `/-! ## Display (untrusted) -/` holding `Color.name`, `rankLine`, `diagram` and the `Repr` /
  `ToString` instances,

and update Position spec §6 and choice 13 and Basic spec §8 to match.

### C2 (high, before Stage 2 starts). Put G8 in its own file, and the FIDE definitions below `Game`

Spec §7 and DESIGN §8 put G8 at the end of this file, which would then import
`Chess.MoveGen.Correct` (spec open item 2 leaves it undecided). Two reasons to decide against that
now:

1. **Every certificate file imports this module.** Lake rebuilds every dependent when this source
   changes, so each edit to a Stage 2 proof would rebuild every generated certificate, and every
   certificate would transitively import the generator's correctness proofs, which it never uses.
2. **The trusted reading after Stage 2 should not contain the generator or the abstract game.**
   After G8 the point is that a reader can read a headline as `SpecWinsIn` / `SpecOnlyWinningMove`.
   Those definitions (D7.1–D7.4) need only `Position.play`, `Legal` and `Checkmate`, that is,
   `Chess.Rules`. If they live in `ChessGame`, the "trusted" file for them also imports `MoveGen`
   and `Game`.

Recommended layout:

| File | Imports | Contents | Trusted? |
|---|---|---|---|
| `Chess/Spec/Winning.lean` | `Chess.Rules` | `SpecForces`, `SpecWinsIn`, `SpecWins`, `SpecOnlyWinningMove` (D7.1–D7.4) | yes, after Stage 2 |
| `Chess/ChessGame/Fide.lean` | `Chess.ChessGame`, `Chess.MoveGen.Correct`, `Chess.Spec.Winning` | L7.1–L7.6 (G8) | no (proofs) |

`ChessGame.lean` itself then never changes in Stage 2 (except perhaps C4), and DESIGN §8's table
and spec §7 / open item 2 need the matching edit. One fact helps here: only the generator's
**completeness** (M4) is missing for G8. `legalMoves_sound` is already proved. A false `WinsIn`
could come only from a legal defender reply, or a legal escape from "mate", that `legalMoves`
leaves out. So L7.1 is the one hard input, and the file split costs nothing in proof effort.

### C3 (medium-high, library-wide). The tests are 26 of the module's 29.5 s and sit on the import path of every certificate

Measured: 29.5 s with tests, 3.1 s without. Because Lake rebuilds dependents whenever a source file
changes, adding or editing a test here invalidates every file that imports `Chess.ChessGame`. Once
`scripts/` generates certificate files (DESIGN §7.4: hundreds of small theorems per headline), that
is the dominant iteration cost. MoveGen review C4 already asks for a `ChessTest` library; this
module is its strongest case. Recommendation: create `ChessTest` (a second `lean_lib`, not in
`defaultTargets`) and move the `## Tests` section to `Test/ChessGame.lean`, keeping the spec's §6
as its specification. If a few examples should stay as documentation, keep only the `#guard`s,
which are cheap.

### C4 (medium, decide now). Do not strengthen `parseFEN`'s filter to `WellFormed` in Stage 2

Spec §7 ("Stage 2 change to the sanity filter") plans `parseFEN := … p.Sane ∧ WellFormed p`. That
changes the trusted statement `fen_eq_iff`, the meaning of every `fen "…"` literal already in the
library and in generated files, and can turn existing literals into compile errors (castling rights
with no rook at home, which many puzzle FENs carry: checked, `4k3/8/8/8/8/8/8/4K3 w KQkq - 0 1` is
accepted today). DESIGN §5.1 says no theorem about `Legal` needs `WellFormed` (M4 is
unconditional), and nothing in G8 needs it either. Recommendation: keep `fen`'s filter at `Sane`
for good. Where a lemma does need `WellFormed (fen "…")`, it is one `decide` per literal. Drop
M11.1 as stated (`parseFEN s = some p → WellFormed p` would then be false), or restate it as that
per-literal check. If a strict variant is ever wanted, add it under a new name rather than changing
`fen`.

Related, for the `Invariants` author: `Sane.one_king` counts with `Board.squaresOf`, while Rules
has `Board.HasKing` (an `∃`). If `WellFormed` states "exactly one king" a third way, the bridge
`WellFormed → Sane` becomes a proof about three formulations. Use `squaresOf` (see C5) in both.

### C5 (medium). General helpers are homed in the top module, out of reach of the lower layers

`Board.squaresOf` and `Board.mem_squaresOf` (material counts, R7; "one king" in `WellFormed`; a
bitboard popcount refinement), `CastlingRights.all` with `mem_all` and `length_all` (the R2
enumeration of `Position`; spec §9 request 2, still open), `Board.row`, `Square.ofName?` and
`Piece.ofLetter?` are all about the data model, not about chess-as-a-game or notation. Here they
can be used only by files that import `ChessGame`, and through it `MoveGen` and `Game`.
`Chess/Invariants.lean` (planned to import `Rules` only) cannot use them. Moving them keeps their
names (same namespaces), so it is cheap, but it should happen before `Invariants` and `Fast/` are
written. Recommendation: move `Board.squaresOf`, `Board.mem_squaresOf`, `CastlingRights.all` and
its two lemmas to `Chess.Position`, `Square.ofName?` beside `Square.name` (in the new "Notation"
section of C1), and `Piece.ofLetter?` beside `Piece.letter`. The generic list lemmas
(`intercalate_singleton_cons`, `mem_intercalate`; spec open item 6) can wait until a `Util` module
exists.

### C6 (medium, usability, cross-module). FENs from Stockfish and Lichess denote different positions after a double push

Checked: `fen "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1"` (Lichess and Stockfish
after 1.e4) is **not** `Position.initial.play (uci "e2e4")` (`decide` gives `false`), because
`play` stores `e3`. This is not a soundness problem: a headline is about the position its string
denotes, and the two positions have the same moves. But it will break naive checkpoint equalities
in the certificate pipeline, and repetition (Stage 4) needs the same identification. The warning
lives in the `fenFields` docstring and spec choice 8, not in the `fen` docstring, which is where a
headline author looks. Recommendations: (a) spec first, add to the `fen` docstring one sentence
saying the en passant target must be written as the library stores it (after every double push),
pointing to `Position.fenFields`; (b) schedule G16 (`normalize`, `legalMoves_normalize`,
`play_normalize`) in Stage 2 alongside G8, since the Stockfish pipeline hits it at once; (c) or
settle THEOREMS open question 3 (store the target only when a capture is possible) before
generated files exist, because changing `play` later moves every checkpoint.

### C7 (low-medium). One name per headline position

Each `fen "…"` in a statement elaborates its own auxiliary proof (checked: `#print` shows
`fen "…" p1._proof_1`) at about 0.5 s of kernel time, and is re-reduced wherever a proof
evaluates it. The planned headline shape, `OnlyWinningMove (fen s) (uci "…") ∧ WinsIn .black 11
(fen s)`, writes the same 60-character string twice, so a typo in one copy states a claim about two
positions. Recommendation for the headline and certificate conventions (DESIGN §7.4, `scripts/`):
`def gotham : Position := fen "…"`, one literal test `gotham = ⟨Board.unpack 0x…, …⟩` by
`decide +kernel`, and statements over `gotham`. `fen` reduces through a `def` (checked:
`def start' := fen startStr` then `start' = Position.initial` by `decide +kernel`).

### C8 (low). Plan the clock extension as an addition, not an edit of `IsFEN`

G15 needs the halfmove clock (spec open item 5). `IsFEN` is trusted and quoted by `fen_eq_iff`;
changing it later changes the meaning statement every headline relies on. Recommendation: when the
clock is read, add a separate predicate (say `FENClock s c`, "`s` is a six-field FEN whose halfmove
field is the numeral of `c`") with its own reader and guard, and leave `IsFEN`, `fen` and
`fen_eq_iff` untouched. Open item 4 (the four-field form) can then stay: G15 headlines will need
six fields anyway, by the new predicate's own statement.

### C9 (low, nits)

- `Position.Sane.decidable` restates the conjunction to guard against drift. A named
  `Position.sane_iff : p.Sane ↔ (∀ c, …) ∧ … ∧ …` (proved by the same anonymous constructors) gives
  the same protection, a rewrite lemma for proofs, and the instance
  `decidable_of_iff _ sane_iff.symm`.
- `variable {a : Color} {n : Nat} {p : Position}` in `section ChessAsAGame`: no declaration uses
  `n`. Harmless (unused section variables are not included), but the spec's variable line can drop
  it.
- `Game.chess_*` lemmas need `Chess.Move` written qualified (spec §0). Every future `Game.chess…`
  lemma (G8's included) inherits this papercut. Naming G8's lemmas without the `Game.` prefix, as
  spec §9 already does (`mem_chess_moves`, `chess_mated_iff_checkmate`), avoids it; keep doing so.

### C10 (information). Fit with the fast layer and later modules

- **Bitboards (Stage 5).** Nothing here needs to change. The fast layer is a second `Game` with a
  morphism to `Game.chess` (G7); the Game review (C4) checked that the trusted definitions read
  `moves` only through membership and emptiness, so the fast generator may list moves in any order.
  Two cautions: never redefine `Game.chess.moves` as the fast generator (that would put bitboard
  code in the trusted base of every headline), and if the fast game packs moves (`UInt16`),
  transferring `OnlyWinningMove` needs the move map to be injective. `fen` yields a `Board.ofRows`
  closure, so a fast-layer certificate should start from an `unpack` checkpoint literal (C7), not
  re-encode `fen "…"` in every theorem.
- **Certificates.** `Game.checkWin_sound (c := .move (uci "a1a8") .goal)` already works on the
  chess names with no annotation (the test file shows it). `checkOnlyMove` will too.
- **Draws (Stage 3).** `Chess.Holds` is planned as one more `abbrev`; no change to anything here.
  Until G9, `OnlyWinningMove` headlines need every alternative to lose or stalemate (spec note P5),
  which is the right warning.

---

## 3. Summary

| ID | Priority | Recommendation | Owner |
|---|---|---|---|
| C1 | high | Split "Display" into trusted "Notation" and untrusted "Display" in Basic and Position, with their specs | Position, Basic |
| C2 | high | G8 in `Chess/ChessGame/Fide.lean`; `Spec*` definitions in `Chess/Spec/Winning.lean` over `Rules` only | Stage 2 lead, DESIGN |
| C3 | medium-high | Create `ChessTest`; move this module's tests there (26 of 29.5 s) | anyone, DESIGN |
| C4 | medium | Keep `fen`'s filter at `Sane`; check `WellFormed` per literal; one "one king" vocabulary | ChessGame, Invariants |
| C5 | medium | Move `squaresOf`, `CastlingRights.all`, `Square.ofName?`, `Piece.ofLetter?` to their types' modules | Position, Basic, ChessGame |
| C6 | medium | Warn in `fen`'s docstring about en passant; G16 in Stage 2, or settle the convention now | ChessGame, Rules |
| C7 | low-medium | Headlines name their position once (`def gotham := fen "…"`) | headline and `scripts/` conventions |
| C8 | low | Read the clock with a new predicate; never edit `IsFEN` | Stage 4 |
| C9 | low | `Position.sane_iff`; drop the unused `n`; keep G8 names unprefixed | ChessGame |

## Appendix: checks behind the findings

All in scratch files importing the built library.

```lean
-- C4: accepted today (castling rights without rooks; en passant target with no pawn; pawns on
-- the back ranks; move number 0)
#eval (parseFEN "4k3/8/8/8/8/8/8/4K3 w KQkq - 0 1").isSome      -- true
#eval (parseFEN "4k3/8/8/8/8/8/8/4K3 w - e6 0 1").isSome        -- true
#eval (parseFEN "P3k3/8/8/8/8/8/8/P3K3 w - - 0 1").isSome       -- true
#eval (parseFEN "4k3/8/8/8/8/8/8/4K3 w - - 0 0").isSome         -- true
-- C6: the Lichess FEN after 1.e4 is not the played position
#eval decide (fen "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1"
  = Position.initial.play (uci "e2e4"))                         -- false
-- C7: fen through a def, and its auxiliary proof
def startStr : String := "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
def start' : Position := fen startStr
example : start' = Position.initial := by decide +kernel       -- ok
-- `#print p1` with pp.proofs: `fen "…" p1._proof_1`
-- Spec note fixed in this review: with `open Chess Chess.Game`,
example (p : Position) : Prop := WinsIn .white 1 p               -- ok (resolved by elaboration)
-- (winsIn_zero_iff.1 h).1 with h : WinsIn .white 0 p             -- "Ambiguous term"
```
