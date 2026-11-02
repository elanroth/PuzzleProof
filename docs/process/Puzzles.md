# Process log: `Chess.Puzzles`

The record of the back-and-forth between the English specification (`docs/spec/Puzzles.md`) and the
Lean (`Chess/Puzzles.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English and Lean (ROADMAP step 5)

Date: 2026-11-02. Author role: overnight implementer (ROADMAP step 5, "name headline positions
once"), writing spec and Lean in one round. Inputs: `docs/ROADMAP.md` §5 steps 5 and 7,
`chess-lean/ChessProof/Gotham.lean` and `chess-lean/README.md` (read only),
`chess-lean/artifact/chess-proofs.html` (the prototype's write-up, for the main line and the move
count), `Chess/ChessGame.lean` (`fen`, the en passant and clock conventions), `Chess/Position.lean`
(`Position.epTarget`).

**Checking the FEN before writing it down.** The string was copied from the prototype and checked
with python-chess 1.11.2 (script in the round's scratch directory): a valid position, Black to
move, 34 legal moves, `b7b2` legal (`Rxb2+`), White not in check, the FEN written back unchanged.
The en passant field was the one point that needed thought, since this library writes the target
after every two-square advance and Stockfish does not. The only White pawn that could have just
advanced two squares is the one on `e4`, and Black's `f4` pawn could then capture on `e3`
(python-chess, with `e3` set: 35 legal moves, `f4e3` among them). So both conventions would write
`e3` after `e2e4`, and the string's `-` reads the same in both. The docstring says this in one
sentence, so a reader does not have to redo the argument.

**English first.** Spec D1.1 with its docstring, then the Lean. The docstring cites the source (the
GothamChess short and the game), says the claim is the prototype's and the target of step 7, not
proved here, and states the en passant and clock readings.

**Lean.** No surprise. `fen` proves the parse by `decide +kernel` at elaboration. The first
version had six tests: the turn, castling rights and en passant target by `rfl`, and three
`#guard`s. The file then took 3.5 s, of which about 2 s were the three `rfl`s (each, presumably,
reduces `fen` in the kernel again). They were redundant with the `toFEN` guard, which writes all
three fields, so they were dropped; the file now takes about 2.0 s (0.6 s the definition, 1.4 s
the guards).

**Name.** `Chess.Puzzles` (spec design choice 2): `Positions` would read like `Chess.Position`, and
`Headlines` would name the use rather than the thing.

**Checked.** Both Lean docstrings (the module docstring and `gotham`) occur word for word in the
spec. `Chess.lean` imports the module. `lake build` green.

---

## Round 2: review fixes (ROADMAP step 5)

Date: 2026-11-02. Author role: overnight implementer, fixing the review of step 5.

**Tests moved to `ChessTest` (low; the review left it to the owner).** The three `#guard`s cost
about 1.4 s of the module's 2.0 s on every `lake build`, against step 3's convention that tests
live in the `ChessTest` library. They are now in the new file `ChessTest/Puzzles.lean`, imported
from `ChessTest.lean`, with the same comments and IDs T1–T3. The definition stays in the library
(design choice 1, which now also says why the tests do not). The parse is still kernel-checked on
every library build, by `fen`'s default argument. Spec first: §2 says where the tests are and
quotes the new file's module docstring; "Contents of the file" and the header list the two files;
the module docstring gained a bullet saying where the tests are.

**T3 overclaimed (low).** §2 said that through `mem_legalMoves`, T3 "also says"
`Legal gotham (uci "b7b2")`. T3 is an interpreted `#guard`, so it establishes nothing in the
kernel. Now: T3 is evidence, not a proof, of that fact; the kernel fact comes with the step 7
certificates.

**Clock wording (low).** The module docstring said the clock fields "are read and ignored", while
`ClockFields` in `Chess.ChessGame` says their values are "not read or checked". Now: "the clock
fields must be numerals but are otherwise ignored", in the spec first, then in the Lean.

**Checked.** The three docstrings (two module docstrings and `gotham`'s) occur word for word in
the spec (script, whitespace-normalised). `lake build` and `lake build ChessTest.Puzzles` green;
timings in `docs/process/ChessTest.md` Round 4.
