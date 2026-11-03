# Specification of `Chess.ChessGame`

Role: English specification writer (Round 1); revised by the translator (Rounds 2 and 3); refined
(Round 4).
Date: 2026-11-01.
Status: Round 5, matched to the Lean of `Chess/ChessGame.lean` (see `docs/process/ChessGame.md`,
Rounds 2–5; Round 5, 2026-11-02, is G8). Every lemma of this document is proved in the library, with
no `sorry`; the [later] lemmas of §7 since Round 5, in `Chess/ChessGame/Fide.lean`. In Round 1,
every definition, every lemma tagged [core] or [sanity], and every test was elaborated in a
scratch file importing the built `Chess` library (scratchpad only; nothing in the library was
written), and is marked *(checked)*. Timings are from that scratch file, on this
machine, one process at a time.

File: `Chess/ChessGame.lean`. Depends on: `Chess.MoveGen` and `Chess.Game.Search`, `Chess.Game.Cert`
(not `Chess.Game`, whose examples it does not need, since 2026-11-03) (and through them
`Chess.Rules`, `Chess.Position`, `Chess.Basic`); core only. Refines DESIGN §6.4 and §8.6. Theorem
targets here: **G1** (the chess instance) and **M11** except M11.1 (the FEN and UCI readers, sound
and complete, all proved in Stage 1). **G8** (the chess game means FIDE chess) is proved in its own
files, `Chess/Spec/Winning.lean` and `Chess/ChessGame/Fide.lean` (§7 below, 2026-11-02); M11.1 is
still planned.

What a reader must trust from this module:

- the definition of `Game.chess` (D1.1) and the four abbreviations (D1.2–D1.5);
- the **writers**: how a position is written in FEN and a move in UCI (§2, plus the letter tables
  of `Chess.Position` and `Square.name` of `Chess.Basic` that they use);
- the **predicates** of §4 that say what an accepted string means: `IsNumeral` (D4.1),
  `ClockFields` (D4.2), `IsFEN` (D4.2a) and `Position.Sane` (D4.5);
- the **statements** of `fen_eq_iff` (L5.25) and `uci_eq_iff` (L5.27), which say what `fen "…"` and
  `uci "…"` denote in terms of the items above.

Since G8 (§7), the first item can be replaced: a reader may read `WinsIn`, `Wins`, `MateIn` and
`OnlyWinningMove` as `SpecWinsIn`, `SpecWins`, `SpecMateIn` and `SpecOnlyWinningMove` of
`Chess.Spec.Winning` (which imports `Chess.Rules` only), by the equivalences of
`Chess.ChessGame.Fide`. Then neither `Game.chess`, nor `Chess.Game`, nor the generator is trusted.

A reader does **not** have to trust the readers of §3 (including `splitOn`, D3.0) or the bodies of
`readFEN`, `parseFEN` and `parseUCI`. The readers only propose and the guards dispose, and three
proved characterisations say exactly what the parsers accept: `readFEN_eq_some_iff` (L5.23),
`parseFEN_eq_some_iff` (L5.4) and `parseUCI_eq_some_iff` (L5.24). Two guarantees behind them are
worth naming:

- *Meaning* (L5.18, L5.23a): the FEN writing loses no information, so a string is a FEN of at most
  one position. `fen s` is therefore *the* sane position of which `s` is a FEN, not merely *a* one.
- *Liveness* (L5.19): every canonical FEN (D4.2a) is accepted, so a correct FEN of a sane position
  is never rejected.

## 0. How to read this document

The conventions of `docs/spec/Basic.md` §0, `docs/spec/Position.md` §0, `docs/spec/Rules.md` §0 and
`docs/spec/MoveGen.md` §0 apply unchanged:

- Each definition has an ID (`D2.4`), its Lean name and type, its Lean body, and a **docstring** in
  quotation marks; the Lean docstring is that text, word for word.
- Each lemma has an ID (`L5.2`), an English statement, the Lean statement, and a tag: **[core]**
  (proved in this file in Stage 1; later files may depend on it), **[sanity]** (checks that a
  definition says what its docstring says), or **[later]** (planned in Round 1 for Stage 2, §7;
  since Round 5 proved in `Chess/ChessGame/Fide.lean`). Rounds 1–3 also used **[target]** for lemmas
  allowed to slip to Stage 5; all of them (L5.15–L5.24) were proved in Round 3 and are [core] since
  Round 4. The Lean docstring of a lemma is its English column. IDs with a letter suffix (`L5.2a`,
  `D4.2a`) were added after Round 1, so that the Round 1 numbering stays stable.
- **Binding rule.** Every name a docstring mentions is bound in the signature or introduced by the
  docstring itself.
- `autoImplicit = false`. Each section opens with the `variable` line given for it.
- **Binders.** Arguments named in a section's `variable` line are implicit. A lemma takes an
  argument explicitly, rebinding its letter, when nothing in the lemma's hypotheses determines it:
  an equation with no hypotheses (`intercalate_splitOn (sep : Char) (cs : List Char)`,
  `readFEN_toFEN (p : Position)`) or a finite check over all values (`Piece.ofLetter?_letter (pc :
  Piece)`).
- `@[simp]` is written on every lemma that carries it; a lemma whose entry does not say `@[simp]`
  does not carry it.
- Everything lives in `namespace Chess`; names are given without the prefix.
- **`Chess.Move` is written qualified inside every declaration whose name starts with `Game.`**
  (D1.1, L1.1–L1.4). In such a declaration Lean resolves a bare `Move` to the structure field
  `Game.Move : Game → Type`, and elaboration fails with "type expected, got (Move : Game → Type)"
  *(checked)*. Elsewhere `Move` is `Chess.Move` as usual.

Letters used in this module: `p q` positions; `m` a move; `a` the attacker (a colour), `c` a colour;
`n k` budgets or counts; `s` a string (in §4–§6) or a square (only in D3.5 and D3.10, where it is
never a string); `t` a square; `e` an optional square (an en passant target); `b` a board; `pc` a
piece; `pk` a promotion kind; `o` an optional promotion kind; `cr` castling rights; `ch` a
character; `cs` and `w` a list of characters (`w` a single field or piece of a split list); `ws` and
`fs` a list of fields or pieces (each a `List Char`); `cl` the clock fields; `r` a rank index
(`Fin 8`, counting from 0: rank `r + 1`), `f` a file index (`Fin 8`); `row` a list of square
contents; `sep` a separator character.

**Rank indices.** `Square.rank` and `Square.relRank` count from 0 (Basic: "0 is rank 1"). Wherever
this document says "the rank with index `r`", it means rank `r + 1` in chess notation; "relative
rank index 5" is the sixth rank counted from that side.

### The ideas of the module, in two paragraphs

**Chess is one game.** `Chess.Game` states forced wins once, for any game with alternating turns
and finite move lists. This module instantiates it: the states are positions, the available moves
are the list `legalMoves` that the generator computes, playing is `Position.play`, and the side to
move has been mated when it is in check and the generator lists no move for it. The two laws of a
game are one-liners: `play` always passes the turn (`play_turn`), and a mated side has an empty
move list by the definition of mated. Headline theorems then speak chess, not game theory:
`Chess.OnlyWinningMove (fen "…") (uci "…") ∧ Chess.WinsIn .black 11 (fen "…")`. "Available move"
means "listed by `legalMoves`"; `Chess.MoveGen` proves that the listed moves are exactly the
FIDE-legal ones (M4), and G8 (`Chess.ChessGame.Fide`) proves that the four notions are equivalent to
their FIDE versions in `Chess.Spec.Winning`. No statement of this module changed for either.

**Readers propose; the guard (writing back) disposes.** A FEN or UCI string in a headline is part of the claim, so
its meaning must be as easy to audit as the rules. Writing is easy to audit: a writer is total, has
no error cases, and says plainly how each field of a position becomes text. Reading is not: a
parser handles every malformed input, and that is where the prototype's silent defaults lived
(garbage became the default position). So the reading here is split in two, exactly as the move
generator is (MoveGen design choice 1): an untrusted, total, lenient **reader** proposes a position
for the string, and the trusted **guard** accepts the proposal only if writing it back gives the
string. Then `fen s` is, by a short theorem (L5.25), "the sane position of which `s` is a FEN",
and a bug in a reader can only make a correct string rejected (a compile-time error in the
headline), never make a string mean the wrong position. Since Round 3 the readers are also proved
complete, so even that cannot happen for a canonical FEN (L5.19).

## Contents of the file, in order

1. Chess as a game: `Game.chess`; `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`; the lemmas of §1.
2. Writing (trusted): `emptyRun`, `rowChars`, `Board.row`, `Board.fenChars`, `Color.fenChar`,
   `epChars`, `Position.fenFields`, `Position.toFEN`.
3. Reading (untrusted proposals): `splitOn`, `emptyCount?`, `Piece.ofLetter?`, `readChar`,
   `readRow`, `Board.ofRows`, `readBoard`, `readTurn`, `readCastling`, `Square.ofName?`,
   `readFields`, `readPromo`, `readMove`.
4. Accepting: first the trusted predicates `IsNumeral`, `ClockFields`, `IsFEN`, `Position.Sane`,
   then the verified parsers `readFEN`, `parseFEN`, `fen`, `parseUCI`, `uci`. (Until the
   readability round of 2026-11-02, `readFEN` and `Board.squaresOf` sat between the predicates.)
5. Lemmas about notation (`section Notation`).
6. Tests.

The trusted reading of the file is §1, §2, the predicates of §4, and the statements of L5.25 and
L5.27. §3 is marked untrusted in its heading, and the heading of §4 says which of its definitions
are trusted. Sections 7–11 of this document are G8 (now in its own files), the design choices,
requests to other modules, the open items and the translator's checklist.

---

## 1. Section "Chess as a game"

`section ChessAsAGame`, opening with `variable {a : Color} {n : Nat} {p : Position}`

(Round 3: the Round 1 line also declared `{m : Move}`, which no declaration of §1 uses; L1.2 binds
its move explicitly as a `Chess.Move`, §0. It was dropped.)

### D1.1 `Game.chess : Game` (an `abbrev`)

```lean
abbrev Game.chess : Game where
  State := Position
  Move := Chess.Move
  turn := Position.turn
  moves := legalMoves
  play := Position.play
  Mated p := InCheck p ∧ legalMoves p = []
  decMated p := inferInstanceAs (Decidable (InCheck p ∧ legalMoves p = []))
  decEqMove := inferInstanceAs (DecidableEq Chess.Move)
  turn_play _ := play_turn _ _
  moves_eq_nil_of_mated h := h.2
```

Docstring: "Chess as a game: the states are positions, the moves are values of `Chess.Move`
(source, destination, promotion choice), the side to move is the position's turn, the available
moves are those listed by the move generator `legalMoves`, a move is played by `Position.play`, and
the side to move has been mated when it is in check and the generator lists no move for it. Play
ends only by mate or by the side to move having no listed move. There is no clock, no fifty- or
seventy-five-move rule, no repetition rule and no dead-position rule, so a win here is a win under
FIDE only when those rules do not intervene (THEOREMS G15). The listed moves are exactly the legal
moves of `Chess.Rules` (`mem_legalMoves`), and `Chess.ChessGame.Fide` restates the notions of this
game with `Legal` and `Checkmate` (THEOREMS G8)."

Notes.
- `abbrev`, not `def` (Game review C1.2): `Game.chess.State` and `Game.chess.Move` must unfold to
  `Position` and `Chess.Move` during unification and instance search, so that a `Position` can be
  passed where a `Game.chess.State` is expected and `Game.checkWin_sound`, `Forces.mono` and dot
  notation (`h.mono`, `h.not_both`) apply to the abbreviations of D1.2–D1.5 *(all checked)*. The
  toy games of `Chess.Game` are `abbrev`s for the same reason.
- `decMated` and `decEqMove` are **given explicitly** (Game review C1.1), although instance search
  would find the same instances today. The reason is the trap the review describes: if `Mated`
  were later changed to `Checkmate p`, instance search would silently pick an instance for
  `Checkmate` that the author of the change never looked at. When this note was written (Round 1)
  that was Rules' `Checkmate.decidable`, which enumerates 64 × 64 × 5 candidate moves (over 500 s
  in the kernel), and every `goal` leaf of every certificate would have timed out with nothing
  failing to build. Since M4, `Chess.MoveGen` declares `Checkmate.decidableByGen` with high
  priority, which decides `Checkmate` through the generator (`checkmate_iff`), so today the silent
  choice would be fast. Writing the instance next to the definition still makes any change of
  `Mated` change the decision procedure visibly too.
- `Mated` is the **executable** form, `InCheck p ∧ legalMoves p = []` (DESIGN §6.4, THEOREMS open
  question 3): in Round 1, `Checkmate p` would have needed the slow decision above. The conjunct
  order is FIDE's ("in check and no legal move") and is also the cheap order: `instDecidableAnd`
  decides `InCheck p` first, and in most positions that is false and ends the test.
  `legalMoves p = []` is decided by list equality with `[]`, which the kernel evaluates lazily: it
  needs only the first listed move to answer "no".
- `turn_play` gets the unconditional `play_turn p m : (p.play m).turn = p.turn.other` (Rules); the
  law asks it only for available moves. `moves_eq_nil_of_mated` is the second conjunct of `Mated`.
- In `Move := Chess.Move` and `DecidableEq Chess.Move`, the qualification is required (§0)
  *(checked: a bare `Move` fails)*.
- The draw rules (Round 4). The direction that matters for a headline is that a `WinsIn` here can
  be a draw under FIDE: `parseFEN` ignores the clocks, so a mate in 2 from a FEN with halfmove clock
  149 is a `WinsIn` here although FIDE 9.6.2 draws it (§6 tests that the clocks do not change the
  position). THEOREMS G15 transfers wins to FIDE given clock headroom.
- `Mated` reads `legalMoves p = []`, and `OnlyWinningMove` tells moves apart by their values, so
  both rely on the contract of `Game.moves`: no move is listed under two values (for chess, castling
  has the one encoding of `Move`, the king's two-square move). That obligation belongs to
  `Chess.MoveGen` and M4.

### D1.2 `WinsIn (a : Color) (n : Nat) (p : Position) : Prop` (an `abbrev`)

```lean
abbrev WinsIn (a : Color) (n : Nat) (p : Position) : Prop := Game.chess.WinsIn a n p
```

Docstring: "`WinsIn a n p`: from position `p`, whichever side is to move there, the side `a` can
force the other side to be mated using at most `n` moves of its own, the mating move included,
whatever the other side plays. This is chess as computed by the move generator (moves are those
listed by `legalMoves`; 'mated' means in check with no listed move, as in `Game.chess`), without
move-count or repetition rules."

### D1.3 `Wins (a : Color) (p : Position) : Prop` (an `abbrev`)

```lean
abbrev Wins (a : Color) (p : Position) : Prop := Game.chess.Wins a p
```

Docstring: "`Wins a p`: from position `p`, the side `a` can force the other side to be mated within
some number of its own moves, a bound fixed in advance (`∃ n, WinsIn a n p`). This is chess as
computed by the move generator (moves are those listed by `legalMoves`; 'mated' means in check with
no listed move, as in `Game.chess`), without move-count or repetition rules."

### D1.4 `MateIn (a : Color) (n : Nat) (p : Position) : Prop` (an `abbrev`)

```lean
abbrev MateIn (a : Color) (n : Nat) (p : Position) : Prop := Game.chess.MateIn a n p
```

Docstring: "`MateIn a n p`: from position `p`, the side `a` mates in exactly `n`: it can force the
other side to be mated within `n` moves of its own, and not within fewer. This is chess as computed
by the move generator (moves are those listed by `legalMoves`; 'mated' means in check with no
listed move, as in `Game.chess`), without move-count or repetition rules."

### D1.5 `OnlyWinningMove (p : Position) (m : Move) : Prop` (an `abbrev`)

```lean
abbrev OnlyWinningMove (p : Position) (m : Move) : Prop := Game.chess.OnlyWinningMove p m
```

Docstring: "`OnlyWinningMove p m`: `m` is listed by `legalMoves p`, the side to move wins after `m`,
and after every other listed move it does not win. 'Other' means a different move value: promotions
to different pieces are different moves, so if `e7e8q` and `e7e8r` both win, neither is the only
winning move. An alternative that wins only slowly still counts as winning, so it makes this false.
This is chess as computed by the move generator (moves are those listed by `legalMoves`; 'mated'
means in check with no listed move, as in `Game.chess`), without move-count or repetition rules."

Notes on D1.2–D1.5.
- The four names are the vocabulary of headline theorems (DESIGN §6.4): no `(G := …)` annotation,
  and the arguments are `Position` and `Move`, not `Game.chess.State` and `Game.chess.Move`, so a
  reader of a headline never meets the abstract game.
- "Without move-count or repetition rules" is in each docstring because that is where a chess reader
  looks (Game review C8). It says which game the claim is about (DESIGN §6.5: G∞). Each docstring
  says "mated", not "checkmated": in Stage 1 the target is `InCheck ∧ legalMoves = []`, not Rules'
  `Checkmate`; `checkmate_iff` (M6) and G8 (`Chess.ChessGame.Fide`) prove the two equal.
- The definitions accept any position. Headlines obtain positions from `fen`, which are sane
  (L5.7). On positions that are not sane the definitions still have a meaning, but it is not chess
  (D4.5 notes): with no defending king, `WinsIn` is always false, because `InCheck` is false; with
  two kings, "in check" means "one of them is attacked".
- `OnlyWinningMove` needs `¬ Wins` after every other listed move, with no bound. In Stage 1 that is
  provable only where the opponent wins after the alternative (`Wins.not_both`) or the alternative
  stalemates (L1.6). An alternative that draws needs the drawing arguments of G9 (Stage 3), so
  Stage 1 headlines `OnlyWinningMove (fen "…") (uci "…")` are expected only in positions where no
  alternative draws.
- `Chess.Holds` (Stage 3) will join them, as `abbrev Holds (d : Color) (p : Position) : Prop :=
  Game.chess.Holds d p`. Not written now.
- A file that opens both `Chess` and `Chess.Game` sees two `WinsIn`s (and two `winsIn_zero_iff`s,
  two `not_wins_of_stalemate`s). Lean picks the reading that elaborates, so `WinsIn .white 1 p`
  works, but where both readings elaborate it reports an ambiguity: `(winsIn_zero_iff.1 h).1` with
  `h : WinsIn .white 0 p` fails *(checked, file review)*. Clients open `Chess` only; `Chess.Game`
  names are reached by dot notation or written `Game.…`.

### Lemmas of §1

| ID | English | Lean | Tag |
|---|---|---|---|
| L1.1 | The moves available in chess at `p` are the moves listed by `legalMoves p`. | `theorem Game.chess_moves (p : Position) : Game.chess.moves p = legalMoves p := rfl` | [core] *(checked)* |
| L1.2 | Playing a move in chess is `Position.play`. | `theorem Game.chess_play (p : Position) (m : Chess.Move) : Game.chess.play p m = p.play m := rfl` | [core] *(checked)* |
| L1.3 | The side to move in chess is the position's turn. | `theorem Game.chess_turn (p : Position) : Game.chess.turn p = p.turn := rfl` | [core] *(checked)* |
| L1.4 | In chess the side to move has been mated exactly when it is in check and `legalMoves` lists no move. | `theorem Game.chess_mated (p : Position) : Game.chess.Mated p ↔ InCheck p ∧ legalMoves p = [] := Iff.rfl` | [core] *(checked)* |
| L1.5 | `WinsIn a 0 p` holds exactly when the other side is to move at `p`, is in check, and has no listed move: `a` has already won. (THEOREMS G2, read in chess.) | `theorem winsIn_zero_iff : WinsIn a 0 p ↔ p.turn = a.other ∧ InCheck p ∧ legalMoves p = [] := Game.winsIn_zero_iff` | [core] *(checked)* |
| L1.6 | In a position where the side to move is not in check and has no listed move (stalemate, as the generator sees it; `stalemate_iff` (M6) says it is FIDE stalemate), neither side wins. (THEOREMS G2.) | `theorem not_wins_of_stalemate (hc : ¬ InCheck p) (hl : legalMoves p = []) : ¬ Wins a p := Game.not_wins_of_stalemate (G := Game.chess) (fun h => hc h.1) hl` | [core] *(checked)* |

Notes. L1.1–L1.4 are `rfl` and exist so that `rw` can move between the game's vocabulary and the
chess vocabulary in proofs that are not by evaluation; they are named with the `Game.` prefix so
that they are found next to `Game.chess`. They are not `@[simp]` (Round 4): `simp` already reduces
projections of the `abbrev` instance, so `simp at h` turns `m ∈ Game.chess.moves p` into
`m ∈ legalMoves p` without them, and with them it reports them as unused. Their signatures need
`Chess.Move` (§0). L1.5 and L1.6 are the two chess-level facts a reader checks first ("mate is a
win; stalemate is not"); everything else of `Chess.Game` (monotonicity, `not_both`, `MateIn.unique`, the checkers' soundness)
applies to D1.2–D1.5 directly, through the `abbrev`s, with no restatement *(checked for
`Forces.mono`, `Wins.not_both`, `OnlyWinningMove.wins`, `checkWin_sound`)*.

---

## 2. Section "Writing" (trusted)

How a position is written in FEN and a move in UCI. These definitions carry the meaning of every
`fen "…"` and `uci "…"`, so they are part of the trusted reading. They reuse the letter tables of
`Chess.Position` (`Piece.letter`, `PromoKind.letter`, `CastlingRights.letters`, `Move.toUCI`) and
`Square.name` of `Chess.Basic`, so every letter is written once in the library (DESIGN Principle 5).
All writers produce `List Char`, not `String`: the kernel reduces lists directly, and the guards of
§4 compare lists.

No `variable` line.

### D2.1 `emptyRun (k : Nat) : List Char`

```lean
def emptyRun (k : Nat) : List Char := if k = 0 then [] else [k.digitChar]
```

Docstring: "How FEN writes a run of `k` empty squares inside a row: nothing if `k = 0`, otherwise
the single character `k.digitChar`, which is the digit `k` when `1 ≤ k ≤ 9`. `rowChars` calls it
only with `k ≤ 8` when the row has at most eight squares."

### D2.2 `rowChars : Nat → List (Option Piece) → List Char`

```lean
def rowChars : Nat → List (Option Piece) → List Char
  | k, [] => emptyRun k
  | k, none :: row => rowChars (k + 1) row
  | k, some pc :: row => emptyRun k ++ pc.letter :: rowChars 0 row
```

Docstring: "`rowChars k row`: the FEN text of the squares `row`, from left to right, when `k` empty
squares have just been passed and not yet written. Each piece is written as its letter (upper case
for White, lower case for Black), and each maximal run of empty squares as one digit, its length;
the first run includes the `k` pending squares. (A board row has eight squares and is written with
`rowChars 0`, so every run is one of the digits `1` to `8`.)"

Notes. Structural recursion on the row; the pending count `k` is what merges a run of empty
squares into one digit, so the writer never writes two digits in a row. A row is written with
`rowChars 0`.

### D2.3 `Board.row (b : Board) (r : Fin 8) : List (Option Piece)`

```lean
def Board.row (b : Board) (r : Fin 8) : List (Option Piece) :=
  (List.finRange 8).map fun f => b ⟨f, r⟩
```

Docstring: "The contents of the eight squares of `b` whose rank index is `r` (rank `r + 1`), from
the a-file to the h-file."

### D2.4 `Board.fenChars (b : Board) : List Char`

```lean
def Board.fenChars (b : Board) : List Char :=
  ['/'].intercalate ((List.finRange 8).reverse.map fun r => rowChars 0 (b.row r))
```

Docstring: "The first field of FEN, the board: its eight ranks from rank 8 down to rank 1, each
written by `rowChars`, separated by `/`."

### D2.5 `Color.fenChar (c : Color) : Char`

```lean
def Color.fenChar (c : Color) : Char :=
  match c with
  | .white => 'w'
  | .black => 'b'
```

Docstring: "The FEN letter of the side to move: `w` for White, `b` for Black."

### D2.6 `epChars (e : Option Square) : List Char`

```lean
def epChars (e : Option Square) : List Char :=
  match e with
  | none => ['-']
  | some t => t.name.toList
```

Docstring: "The fourth field of FEN, the en passant target: the square's name, such as `e3`, or `-`
if there is none."

### D2.7 `Position.fenFields (p : Position) : List (List Char)`

```lean
def Position.fenFields (p : Position) : List (List Char) :=
  [p.board.fenChars, [p.turn.fenChar], p.castling.letters.toList, epChars p.epTarget]
```

Docstring: "The four FEN fields of `p` that describe the position itself: the board, the side to
move, the castling rights (the letters `KQkq` of the rights held, in that order, or `-`), and the
en passant target as `p` stores it. Positions produced by `Position.play` store a target after
every two-square pawn advance, whether or not a capture is possible (the convention of the PGN
standard's FEN section)."

Notes. `CastlingRights.letters` (Position) already writes `-` for no rights, as FEN does. The en
passant convention is the library's (DESIGN §4.6): a FEN from python-chess must be produced with
`en_passant="fen"` to match, as for certificate checkpoints (DESIGN §7.4).

### D2.8 `Position.toFEN (p : Position) : String`

```lean
def Position.toFEN (p : Position) : String :=
  String.ofList ([' '].intercalate (p.fenFields ++ [['0'], ['1']]))
```

Docstring: "The FEN of `p`: its four fields, then the clock fields `0 1`, separated by single
spaces. A position records no clocks, so the halfmove clock is written as 0 and the move number as
1."

Notes. Six fields, because every engine and every library expects six; the clock values are the
ones a position with no history has. `parseFEN p.toFEN = some p` for every sane `p` is L5.21.

---

## 3. Section "Reading" (untrusted: the guards of §4 check every result)

The readers turn text into a proposal. They are **total and lenient**: they never fail, and on text
that no writer produces they return some position or move, which the guard then rejects. Nothing in
this section is trusted, and nothing here needs to reject anything; its only obligation is to read
correctly what the writers write (the completeness lemmas L5.15–L5.24, all proved). Every table is
inverted by search over the finite list of all values, so no letter is written twice.

No `variable` line.

### D3.0 `splitOn (sep : Char) (cs : List Char) : List (List Char)`

```lean
def splitOn (sep : Char) (cs : List Char) : List (List Char) :=
  (go cs).1 :: (go cs).2
where
  /-- The first piece of the list (up to the first `sep`), and the remaining pieces in order. -/
  go : List Char → List Char × List (List Char)
    | [] => ([], [])
    | ch :: cs =>
      let (w, ws) := go cs
      if ch = sep then ([], w :: ws) else (ch :: w, ws)
```

Docstring: "The pieces of `cs` between the occurrences of `sep`, in order: one more piece than there
are occurrences of `sep`, and empty pieces kept, so that joining the pieces with `sep` gives `cs`
back (`intercalate_splitOn`)."

Notes. Core has no `List.splitOn`, and `String.splitOn` works on byte positions (not measured
in the kernel; avoided, choice 9); this is the library's own. It was D2.9, in the trusted section,
until Round 3, because the guard of D4.3 compares the fields it produces. Since Round 4 it is
untrusted like the other readers: `readFEN_eq_some_iff` (L5.23) states what `readFEN` accepts with
`IsFEN`, which joins fields with `List.intercalate` and never splits. Its lemmas L5.2 (splitting
loses and invents nothing) and L5.16 (splitting undoes joining) are what that proof uses. The helper
`go` returns the first piece separately, so the result is non-empty by construction and the
recursion has no impossible case. Empty pieces are kept, so a doubled, leading or trailing
separator produces an empty field, which no writer produces: such a string is rejected, never
silently repaired.

### D3.1 `emptyCount? (ch : Char) : Option Nat`

```lean
def emptyCount? (ch : Char) : Option Nat := (List.range' 1 8).find? fun k => k.digitChar = ch
```

Docstring: "The number of empty squares that the FEN digit `ch` stands for, if `ch` is one of the
digits `1` to `8`."

Notes. `9` and `0` are not read as runs; `readChar` then reads them as one empty square (through
`Piece.ofLetter? = none`), and the guard rejects the string, because no writer writes them.

### D3.2 `Piece.ofLetter? (ch : Char) : Option Piece`

```lean
def Piece.ofLetter? (ch : Char) : Option Piece := Piece.all.find? fun pc => pc.letter = ch
```

Docstring: "The piece whose FEN letter is `ch`, if any."

### D3.3 `readChar (ch : Char) : List (Option Piece)`

```lean
def readChar (ch : Char) : List (Option Piece) :=
  match emptyCount? ch with
  | some k => List.replicate k none
  | none => [Piece.ofLetter? ch]
```

Docstring: "The squares that one character of a FEN row proposes: `k` empty squares for a digit
`k`, otherwise one square holding the piece with that letter, or one empty square if no piece has
that letter."

### D3.4 `readRow (cs : List Char) : List (Option Piece)`

```lean
def readRow (cs : List Char) : List (Option Piece) := cs.flatMap readChar
```

Docstring: "The squares that a FEN row proposes, from left to right: the squares of each character
in turn. The result may be shorter or longer than eight squares; the guard rejects such a row."

Notes. A `flatMap`, so that reading distributes over appending (`List.flatMap_append`), which is
the one fact the round-trip lemma L5.15 needs.

### D3.5 `Board.ofRows (rows : List (List (Option Piece))) : Board`

```lean
def Board.ofRows (rows : List (List (Option Piece))) : Board :=
  fun s => (rows.getD s.rank.rev.val []).getD s.file.val none
```

Docstring: "The board whose square `s` holds entry number `s.file` of row number `7 − s.rank` of
`rows`, both counting from 0, the rows being listed from rank 8 down to rank 1 as in FEN; empty
where `rows` has no such entry."

Notes. DESIGN §10 left open whether a parsed board is built from `Board.unpack` of a computed
number or by `set`s. Measured here: as a list lookup it is as fast as `unpack` and faster to read.
`legalMoves (fen …)` on the initial position took 4.8 s with this board and 5.1 s with `unpack`
(3.5 s for `Position.initial` itself); on Kiwipete, 10.8 s against 11.6 s. Kernel whnf caching
makes each square read cheap after the first.

### D3.6 `readBoard (cs : List Char) : Board`

```lean
def readBoard (cs : List Char) : Board := Board.ofRows ((splitOn '/' cs).map readRow)
```

Docstring: "The board that a FEN board field proposes: its rows, separated by `/`, each read by
`readRow`."

### D3.7 `readTurn (cs : List Char) : Color`

```lean
def readTurn (cs : List Char) : Color :=
  (Color.all.find? fun c => [c.fenChar] = cs).getD .white
```

Docstring: "The side to move that a FEN field proposes: the colour whose letter the field is, or
White if there is none."

### D3.8 (moved) `CastlingRights.all`

Moved to `Chess.Position` (Position D4.6a, with its lemmas `mem_all` and `length_all`, Position
P4.3a, formerly L5.14a and L5.14b) in the readability round of 2026-11-02, as §9 request 2 and
ChessGame review C5 asked. `readCastling` searches it there.

### D3.9 `readCastling (cs : List Char) : CastlingRights`

```lean
def readCastling (cs : List Char) : CastlingRights :=
  (CastlingRights.all.find? fun cr => cr.letters.toList = cs).getD .none
```

Docstring: "The castling rights that a FEN field proposes: the rights whose FEN letters the field
is, or no rights if there are none."

### D3.10 `Square.ofName? (cs : List Char) : Option Square`

```lean
def Square.ofName? (cs : List Char) : Option Square :=
  Square.all.find? fun s => s.name.toList = cs
```

Docstring: "The square whose name, such as `e4`, is `cs`, if any."

Notes. It also reads the en passant field: `-` is no square's name, so it gives `none`, which
`epChars` writes back as `-`.

### D3.11 `readFields (fs : List (List Char)) : Position`

```lean
def readFields (fs : List (List Char)) : Position :=
  ⟨readBoard (fs.getD 0 []), readTurn (fs.getD 1 []), readCastling (fs.getD 2 []),
    Square.ofName? (fs.getD 3 [])⟩
```

Docstring: "The position that the first four fields of a FEN propose: board, side to move,
castling rights and en passant target, each read from its field. Missing fields read as empty."

### D3.12 `readPromo (cs : List Char) : Option PromoKind`

```lean
def readPromo (cs : List Char) : Option PromoKind :=
  PromoKind.all.find? fun pk => [pk.letter] = cs
```

Docstring: "The promotion choice that the end of a UCI move proposes: the kind whose letter (`n`,
`b`, `r` or `q`) the text is, or none."

### D3.13 `readMove (cs : List Char) : Move`

```lean
def readMove (cs : List Char) : Move :=
  ⟨(Square.ofName? (cs.take 2)).getD ⟨0, 0⟩, (Square.ofName? ((cs.drop 2).take 2)).getD ⟨0, 0⟩,
    readPromo (cs.drop 4)⟩
```

Docstring: "The move that UCI text proposes: the source square from its first two characters, the
destination square from the next two, and the promotion choice from the rest. A square that cannot
be read is proposed as a1."

---

## 4. Section "Accepting"

The section opens with this comment (Round 4): "The predicates `IsNumeral`, `ClockFields`, `IsFEN`
and `Position.Sane` are trusted: they say what an accepted string means. The parsers `readFEN`,
`parseFEN` and `parseUCI` are not: `readFEN_eq_some_iff`, `parseFEN_eq_some_iff` and
`parseUCI_eq_some_iff` prove that they accept exactly what those predicates and `Move.toUCI`
describe."

The guards. A string is accepted only if it is the writing of the proposal (D4.3, D4.8), and a FEN
only if the position also passes the sanity filter (D4.5, D4.6). Until Round 3 the whole section
was trusted; the characterisations L5.4, L5.23 and L5.24 now verify the parsers, so only the
predicates D4.1, D4.2, D4.2a and D4.5 (with Position's `Board.squaresOf`, which D4.5 uses) are.
Since the readability round of 2026-11-02 the section lists the four trusted predicates first and
the parsers after them, so the trusted text is one block: D4.1, D4.2, D4.2a, D4.5, then D4.3,
D4.6–D4.9. The IDs were not renumbered.

No `variable` line.

### D4.1 `IsNumeral (cs : List Char) : Prop`, with a `Decidable` instance

```lean
def IsNumeral (cs : List Char) : Prop := cs ≠ [] ∧ ∀ ch ∈ cs, ch.isDigit = true

instance IsNumeral.decidable (cs : List Char) : Decidable (IsNumeral cs) := by
  unfold IsNumeral; infer_instance
```

Docstrings: "`cs` is a non-empty run of the digits `0` to `9`, such as `0`, `12` or `007`. Leading
zeros and arbitrarily large values are allowed; the value is never read." and "Whether a list of characters is a
numeral is decided character by character."

### D4.2 `ClockFields (fs : List (List Char)) : Prop`, with a `Decidable` instance

```lean
def ClockFields (fs : List (List Char)) : Prop :=
  fs = [] ∨ (fs.length = 2 ∧ ∀ w ∈ fs, IsNumeral w)

instance ClockFields.decidable (fs : List (List Char)) : Decidable (ClockFields fs) := by
  unfold ClockFields; infer_instance
```

Docstrings: "`fs` are acceptable clock fields for the end of a FEN: none at all, or exactly two
numerals (the halfmove clock and the move number). Their values are not read or checked: a move
number of `0`, which FEN forbids, is accepted." and "Whether the
fields are acceptable clock fields is decided field by field."

### D4.2a `IsFEN (s : String) (p : Position) : Prop` (Round 4)

```lean
def IsFEN (s : String) (p : Position) : Prop :=
  ∃ cl, ClockFields cl ∧ s.toList = [' '].intercalate (p.fenFields ++ cl)
```

Docstring: "`IsFEN s p`: `s` is a FEN of `p`. Its characters are the four FEN fields of `p`
(`Position.fenFields`) followed by acceptable clock fields, joined by single spaces. The clock
fields are not part of the position, so a position has many FENs, which differ only in their
clocks."

Notes. The one trusted statement of what FEN text is. Until Round 3 its right-hand side was written
out three times (L5.3, L5.8, L5.23); naming it makes the contract three short statements:
`readFEN s = some p ↔ IsFEN s p` (L5.23), `IsFEN s p → IsFEN s q → p = q` (L5.23a), and
`fen s h = p ↔ p.Sane ∧ IsFEN s p` (L5.25). It is not decidable as written (the clock list is
existential), and it does not need to be: `readFEN` decides it (L5.23). ***Canonical FEN*** means a
string `s` with `IsFEN s p` for some position `p`.

### D4.5 `Position.Sane (p : Position) : Prop`, a structure, with a `Decidable` instance

```lean
structure Position.Sane (p : Position) : Prop where
  one_king : ∀ c, (p.board.squaresOf ⟨c, .king⟩).length = 1
  not_kingAttacked_other : ¬ p.board.KingAttacked p.turn.other
  epTarget_relRank : ∀ t, p.epTarget = some t → t.relRank p.turn = 5

instance Position.Sane.decidable (p : Position) : Decidable p.Sane :=
  -- The three conditions are restated on purpose: if they drift from the fields of `Sane`, the
  -- anonymous constructors below stop type-checking.
  decidable_of_iff ((∀ c, (p.board.squaresOf ⟨c, .king⟩).length = 1) ∧
      ¬ p.board.KingAttacked p.turn.other ∧ ∀ t, p.epTarget = some t → t.relRank p.turn = 5)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
```

Docstrings:
- structure: "`p` passes the sanity checks that `parseFEN` makes: each side has exactly one king,
  the side not to move is not in check, and an en passant target, if any, lies on the rank that a
  pawn of the side not to move crosses in a two-square advance. This is weaker than
  well-formedness (Stage 2)."
- `one_king`: "Each colour has exactly one king on the board."
- `not_kingAttacked_other`: "The side not to move is not in check: no king of its colour is
  attacked by the side to move."
- `epTarget_relRank`: "The en passant target, if there is one, is on the sixth rank counted from
  the side to move (`relRank p.turn = 5`, counting from 0): rank 6 when White is to move, rank 3
  when Black is. That is the rank a pawn of the other colour crosses in a two-square advance."
- instance: "Whether a position is sane is decided by counting kings, looking for an attack on the
  king of the side not to move, and reading the rank of the en passant target."

Notes, one per condition (DESIGN §6.4).
- `one_king`: with no king of the side to move, `InCheck` is false and the side can never be mated,
  so the semantics could never award a win against it; with two kings, "in check" means "one of
  them attacked". Neither is chess.
- `not_kingAttacked_other`: `PseudoLegal` allows capturing a king (DESIGN §5.4). If the side not to
  move were in check, the side to move could capture its king, and the kingless side would then
  never be mated. That cannot produce a false win, but it is not chess.
- `epTarget_relRank`: a target on any other rank cannot be captured onto (`EnPassantMove` requires
  the target on the sixth rank counted from the mover, relative rank index 5), so it changes no legal move; it is checked because a wrong-rank target is the
  signature of a FEN whose side to move is wrong (e3 with White to move), a common transcription
  error that would otherwise give a headline about the wrong position. This condition is FEN's own
  rule for the en passant field, stated with `relRank`.
- Not checked here (Stage 2's `WellFormed`): pawns on the back ranks, castling rights without the
  king and rook at home, an en passant target with no pawn in front of it. None of them can make a
  rule fire wrongly: `CastleMove` and `EnPassantMove` check the pieces themselves (Rules §5.4).
- A structure with named fields, not a conjunction, so that proofs say `h.one_king` and each
  condition carries its docstring. The `Decidable` instance goes through the conjunction, which is
  decided by the instances of `Color` quantifiers, `Board.KingAttacked` and `Square` quantifiers
  *(checked: `Position.initial.Sane` by `decide +kernel` in 1.5 s)*.

### D4.4 (moved) `Board.squaresOf`

Moved to `Chess.Position` (Position D1.6, with its lemma `Board.mem_squaresOf`, Position P1.8,
formerly L5.13) in the readability round of 2026-11-02. It is trusted there; `MoveGen`'s
king-safety test also uses it, in place of its own copy `Board.kingSquares`.

### D4.3 `readFEN (s : String) : Option Position`

```lean
def readFEN (s : String) : Option Position :=
  let fs := splitOn ' ' s.toList
  let p := readFields fs
  if p.fenFields = fs.take 4 ∧ ClockFields (fs.drop 4) then some p else none
```

Docstring: "Reads the FEN `s`. Its fields are the pieces of `s` between occurrences of the space
character; two adjacent spaces give an empty field, which no writer produces, so such a string is
rejected, and tabs and other whitespace are not separators. The result is the position `p` proposed by the first four fields, provided those four fields are exactly the
FEN writing of `p` (`Position.fenFields p`) and the remaining fields are acceptable clock fields;
otherwise `none`. So `readFEN s = some p` exactly when `IsFEN s p` (`readFEN_eq_some_iff`)."

Notes.
- The guard `p.fenFields = fs.take 4` does all the syntax checking: wrong number of ranks, a rank of
  the wrong length, an unknown letter, two adjacent digits (`44`), a digit `9` or `0`, castling
  letters out of order (`kqKQ`) or repeated, Chess960 castling letters, a side to move other than `w`
  or `b`, an en passant field that is not a square name or `-`, and fewer than four fields all fail
  it, because no writer produces them *(each checked by a test, §6)*.
- Every accepted string is canonical, that is, a FEN of some position (D4.2a, L5.3), and every
  canonical string is accepted (L5.19). Stockfish, python-chess and Lichess
  write canonical FEN for the board, side to move and castling fields; for the en passant field,
  see choice 8.
- `fenFields` has length 4, so the guard's first conjunct also says there are at least four fields;
  `ClockFields (fs.drop 4)` then allows exactly four or exactly six.
- `readFEN` does not judge the position; `parseFEN` (D4.6) does. Keeping the two apart makes
  L5.19 and L5.20 (`readFEN p.toFEN = some p`) true for every position, sane or not.

### D4.6 `parseFEN (s : String) : Option Position`

```lean
def parseFEN (s : String) : Option Position :=
  match readFEN s with
  | some p => if p.Sane then some p else none
  | none => none
```

Docstring: "Parses the FEN `s`: the position whose FEN is `s` (`readFEN`), if it is sane
(`Position.Sane`); otherwise `none`. The clock fields, if present, must be numerals and are
ignored."

### D4.7 `fen (s : String) (h : (parseFEN s).isSome = true := by decide +kernel) : Position`

```lean
def fen (s : String) (h : (parseFEN s).isSome = true := by decide +kernel) : Position :=
  (parseFEN s).get h
```

Docstring: "The position whose FEN is `s`, for use in statements: `fen "…"`. It is the one sane
position of which `s` is a FEN (`fen_eq_iff`; there is only one by `IsFEN.unique`). The clocks are
not part of the position: `s` may end in any two numerals, or in none (see THEOREMS G15). The proof
that `s` parses is found automatically, by evaluation, when the term is elaborated; a string that is
not a FEN of a sane position is a compile-time error, never a default position. The en passant field
is read as written: after a two-square advance it must name the square passed over even when no
capture is possible (`Position.fenFields`), which Stockfish, Lichess and python-chess's default
output do not do."

Notes.
- The last sentence of the docstring was added in the readability round of 2026-11-02 (ChessGame
  review C6, recommendation (a)): the `fen` docstring is where a headline's author looks. A FEN
  copied from Lichess after `1. e4` (`… b KQkq - 0 1`) is accepted, but it denotes a position
  whose `epTarget` is `none`, which is not `Position.initial.play (uci "e2e4")` (checked by `decide
  +kernel` in the round's scratch file). Both positions have the same legal moves.
- `by decide +kernel` rather than `by decide`: the same answer, measured 1.9 s against 2.9 s for
  parsing and sanity-checking Kiwipete, and it does not depend on the elaborator's reduction of the
  `Decidable` instances. A bad string fails with "Tactic `decide` proved that the proposition
  `(parseFEN "…").isSome = true` is false" *(checked)*.
- In the kernel, `fen s h` reduces by `Option.get` of `parseFEN s`, which reduces to `some p` by
  evaluation. So `rfl`, `decide` and `decide +kernel` see through `fen` *(checked: `(fen
  "…").turn = .white := rfl`; `fen "<start>" = Position.initial` by `decide +kernel`)*.
- The proof is an ordinary explicit argument with a default tactic (`(h : … := by …)`), not a
  type class or a hidden side condition, so `#check @fen` shows the whole contract, and a proof can
  also be passed by hand: `fen s h`.

### D4.8 `parseUCI (s : String) : Option Move`

```lean
def parseUCI (s : String) : Option Move :=
  let m := readMove s.toList
  if m.toUCI.toList = s.toList then some m else none
```

Docstring: "Parses the UCI move `s`, such as `e2e4` or `e7e8q`: the move proposed by `readMove`,
provided `s` is exactly that move's UCI writing (`Move.toUCI`); otherwise `none`. So it accepts
exactly the texts `Move.toUCI` writes: two square names, then optionally one of `n b r q`. This
includes moves that are never legal, such as `e2e2`. A pawn move to the last rank must carry its
letter: `e7e8` denotes a move with no promotion choice, which `legalMoves` never lists. Castling is
the king's two-square move (`e1g1`, see `Move`); `e1h1` is accepted and simply never listed.
Whether the move is legal is not checked: that belongs to the claim the move appears in."

Notes. Rejected, because `Move.toUCI` never writes them: upper-case promotion letters (`e7e8Q`),
the null move `0000`, anything off the board (`e2e9`), trailing spaces, and SAN (`Nf3`) *(checked,
§6)*.

### D4.9 `uci (s : String) (h : (parseUCI s).isSome = true := by decide +kernel) : Move`

```lean
def uci (s : String) (h : (parseUCI s).isSome = true := by decide +kernel) : Move :=
  (parseUCI s).get h
```

Docstring: "The move with UCI notation `s`, for use in statements: `uci "…"`. The proof that `s`
parses is found automatically when the term is elaborated; a string that does not parse is a
compile-time error."

---

## 5. Lemmas about notation

`section Notation`, opening with
`variable {s : String} {p q : Position} {m : Move} {sep : Char} {pc : Piece}`

(Round 4: `{cs : List Char}` was dropped; every lemma that mentions `cs` binds it explicitly, §0
"Binders".) Every lemma of this section is proved. L5.1–L5.14e were [core] or [sanity] from Round 1;
L5.15–L5.24 were [target] until Round 4 and are [core] now; L5.11a, L5.19a, L5.23a and L5.25–L5.28
were added in Round 4.

### Soundness: what an accepted string means

| ID | English | Lean | Tag |
|---|---|---|---|
| L5.1 | Joining `w` and the lists `ws` with the separator `sep` is `w` followed by `sep` and each list of `ws` in turn. | `theorem intercalate_singleton_cons {α : Type} (sep : α) (w : List α) (ws : List (List α)) : [sep].intercalate (w :: ws) = w ++ ws.flatMap (sep :: ·)` | [core] *(checked: induction on `ws` generalizing `w`, `simp_all [List.intercalate]`)* |
| L5.2a | Joining the pieces `splitOn.go` returns, the first one and then each of the rest after a `sep`, gives the list back. | `theorem splitOn_go_join (sep : Char) (cs : List Char) : (splitOn.go sep cs).1 ++ (splitOn.go sep cs).2.flatMap (sep :: ·) = cs` | [core] (Round 3: the induction L5.2's proof needs, made a named lemma so that it carries a docstring) |
| L5.2 | Joining the pieces of `cs` with `sep` gives `cs` back: splitting loses and invents nothing. | `theorem intercalate_splitOn (sep : Char) (cs : List Char) : [sep].intercalate (splitOn sep cs) = cs` | [core] *(checked: first `∀ cs, (splitOn.go sep cs).1 ++ (splitOn.go sep cs).2.flatMap (sep :: ·) = cs` by induction, `split <;> simp_all`; then L5.1)* |
| L5.3 | If `readFEN` accepts `s` with position `p`, then `s` is a FEN of `p`. | `theorem readFEN_sound (h : readFEN s = some p) : IsFEN s p` | [core] *(checked: `dsimp only [readFEN] at h; split at h`, then `List.take_append_drop` and L5.2)* |
| L5.4 | `parseFEN` accepts `s` with `p` exactly when `readFEN` does and `p` is sane. | `theorem parseFEN_eq_some_iff : parseFEN s = some p ↔ readFEN s = some p ∧ p.Sane` | [core] *(checked: `cases hr : readFEN s`, then `by_cases h : q.Sane`)* |
| L5.5 | A position `parseFEN` returns is sane. | `theorem parseFEN_sane (h : parseFEN s = some p) : p.Sane := (parseFEN_eq_some_iff.1 h).2` | [core] *(checked)* |
| L5.6 | `parseFEN s` returns `fen s`: it is `some (fen s h)`. | `theorem parseFEN_fen (h : (parseFEN s).isSome = true) : parseFEN s = some (fen s h)` | [core] *(Round 4 proof: `(Option.some_get h).symm`)* |
| L5.7 | The position `fen s` is sane. | `theorem fen_sane (h : (parseFEN s).isSome = true) : (fen s h).Sane` | [core] *(checked)* |
| L5.8 | `s` is a FEN of the position `fen s`. | `theorem fen_spec (h : (parseFEN s).isSome = true) : IsFEN s (fen s h)` | [core] *(checked: L5.3 after L5.4, L5.6)* |
| L5.9 | The name of a square is its file letter followed by its rank digit. | `theorem Square.toList_name (t : Square) : t.name.toList = [t.fileChar, t.rankChar]` | [core] *(checked: `revert t; decide +kernel`, under 1 s)* |
| L5.10 | The UCI text of a move is the source square's name, the destination square's name, and the promotion letter if there is one. | `theorem Move.toList_toUCI (m : Move) : m.toUCI.toList = m.src.name.toList ++ m.dst.name.toList ++ (m.promo.map PromoKind.letter).toList` | [core] *(checked: `rcases m with ⟨t, t', _ \| pk⟩ <;> simp [Move.toUCI, String.toList_append, Char.toString]`)* |
| L5.11 | If `parseUCI` accepts `s` with move `m`, then `s` is the UCI writing of `m`. | `theorem parseUCI_sound (h : parseUCI s = some m) : m.toUCI = s` | [core] *(checked: `dsimp only [parseUCI] at h; split at h`, then `String.toList_inj`)* |
| L5.11a | `parseUCI s` returns `uci s`: it is `some (uci s h)`. | `theorem parseUCI_uci (h : (parseUCI s).isSome = true) : parseUCI s = some (uci s h)` | [core] (Round 4: the UCI twin of L5.6, `(Option.some_get h).symm`) |
| L5.12 | The UCI writing of `uci s` is `s`. | `theorem toUCI_uci (h : (parseUCI s).isSome = true) : (uci s h).toUCI = s` | [core] *(Round 4 proof: `parseUCI_sound (parseUCI_uci h)`)* |
| L5.13 | (moved to Position P1.8, `Board.mem_squaresOf`) | | |
| L5.14a, L5.14b | (moved to Position P4.3a, `CastlingRights.mem_all` and `length_all`) | | |
| L5.14c | Every piece is read back from its letter. | `theorem Piece.ofLetter?_letter (pc : Piece) : Piece.ofLetter? pc.letter = some pc` | [sanity] *(checked by `revert pc; decide`)* |
| L5.14d | `emptyCount?` reads no piece letter as a run of empty squares. | `theorem emptyCount?_letter (pc : Piece) : emptyCount? pc.letter = none` | [sanity] *(checked by `revert pc; decide`)* |
| L5.14e | For `k` from 1 to 8, the digit `k` is read back as `k` empty squares. | `theorem emptyCount?_digitChar : ∀ k ∈ List.range' 1 8, emptyCount? k.digitChar = some k` | [sanity] *(checked by `decide`)* |

Notes. L5.3, L5.8 and L5.11 are the **soundness half of M11**, proved in Stage 1 because the
readers propose and the guards dispose. L5.8 says what `fen "…"` denotes without mentioning any
reader; L5.25 (below) adds that it is the only such position, and is the one statement a reader of a
headline needs. `Position.initial_sane` is a test (§6),
not a lemma.

### Completeness: the writers lose nothing (proved in Round 3; [core] since Round 4)

The rows marked *(helper)* were not in the Round 1 draft; the translation needed them as named
steps (process log, Round 3). They are listed in file order with the lemmas they serve.

| ID | English | Lean | Tag |
|---|---|---|---|
| L5.15a | Every character of a row's FEN text has a property `P` that the digits `0` to `8` and every piece letter have, provided the pending count plus the row's length is at most 8. *(helper)* | `theorem forall_mem_rowChars (P : Char → Prop) (hd : ∀ k < 9, P k.digitChar) (hl : ∀ pc : Piece, P pc.letter) {k : Nat} {row : List (Option Piece)} (h : k + row.length ≤ 8) : ∀ ch ∈ rowChars k row, P ch` | [core] |
| L5.15b | Reading back the text `emptyRun` writes for at most eight empty squares gives those squares. *(helper)* | `theorem readRow_emptyRun {k : Nat} (h : k ≤ 8) : readRow (emptyRun k) = List.replicate k none` | [core] |
| L5.15 | Reading back the FEN text of a row, written when `k` empty squares were pending, gives those `k` empty squares followed by the row, provided `k` plus the number of squares in the row is at most 8. | `theorem readRow_rowChars {row : List (Option Piece)} {k : Nat} (h : k + row.length ≤ 8) : readRow (rowChars k row) = List.replicate k none ++ row` | [core] |
| L5.16a | `splitOn.go` passes over a list with no `sep` in it, adding it to the first piece. *(helper)* | `theorem splitOn_go_append {w : List Char} (h : sep ∉ w) (cs : List Char) : splitOn.go sep (w ++ cs) = (w ++ (splitOn.go sep cs).1, (splitOn.go sep cs).2)` | [core] |
| L5.16b | Splitting `w`, then `sep` and each piece of `ws` in turn, gives `w` and `ws` back, provided no piece contains `sep`. *(helper)* | `theorem splitOn_go_join_pieces {w : List Char} {ws : List (List Char)} (hw : sep ∉ w) (h : ∀ v ∈ ws, sep ∉ v) : splitOn.go sep (w ++ ws.flatMap (sep :: ·)) = (w, ws)` | [core] |
| L5.16 | Splitting a non-empty list of pieces joined with `sep` gives back the pieces, provided no piece contains `sep`. | `theorem splitOn_intercalate {ws : List (List Char)} (hne : ws ≠ []) (h : ∀ w ∈ ws, sep ∉ w) : splitOn sep ([sep].intercalate ws) = ws` | [core] |
| L5.16c | A character of a list joined with `sep` is `sep` or a character of one of the pieces. *(helper)* | `theorem mem_intercalate {α : Type} {sep x : α} {ws : List (List α)} (h : x ∈ [sep].intercalate ws) : x = sep ∨ ∃ w ∈ ws, x ∈ w` | [core] |
| L5.17a | Reading the board field of `b` gives `b` back. *(helper)* | `theorem readBoard_fenChars (b : Board) : readBoard b.fenChars = b` | [core] |
| L5.17b | No character of the board field is a space. *(helper)* | `theorem Board.space_not_mem_fenChars (b : Board) : ' ' ∉ b.fenChars` | [core] |
| L5.17c | The side to move is read back from its letter. *(helper)* | `theorem readTurn_fenChar : ∀ c : Color, readTurn [c.fenChar] = c` (`decide`) | [core] |
| L5.17d | Castling rights are read back from their letters. *(helper)* | `theorem readCastling_letters : ∀ cr : CastlingRights, readCastling cr.letters.toList = cr` (`decide +kernel`) | [core] |
| L5.17e | A square is read back from its file letter and rank digit. *(helper)* | `theorem Square.ofName?_chars : ∀ t : Square, Square.ofName? [t.fileChar, t.rankChar] = some t` (`decide +kernel`) | [core] |
| L5.17f | A square is read back from its name. *(helper)* | `theorem Square.ofName?_name (t : Square) : Square.ofName? t.name.toList = some t` | [core] |
| L5.17g | The en passant target is read back from its field. *(helper)* | `theorem Square.ofName?_epChars (e : Option Square) : Square.ofName? (epChars e) = e` | [core] |
| L5.17 | Reading the four FEN fields of `p`, whatever follows them, gives `p` back. | `theorem readFields_fenFields (p : Position) (cl : List (List Char)) : readFields (p.fenFields ++ cl) = p` | [core] |
| L5.18 | Two positions with the same FEN fields are equal: the FEN writing loses no information. | `theorem Position.fenFields_injective (h : p.fenFields = q.fenFields) : p = q` | [core] |
| L5.18a | No FEN field of a position contains a space. *(helper)* | `theorem space_not_mem_fenFields (p : Position) : ∀ w ∈ p.fenFields, ' ' ∉ w` | [core] |
| L5.18b | No clock field contains a space. *(helper)* | `theorem space_not_mem_of_clockFields {cl : List (List Char)} (hcl : ClockFields cl) : ∀ w ∈ cl, ' ' ∉ w` | [core] |
| L5.19 | If `s` is a FEN of `p`, then `readFEN` accepts `s` with `p`: every canonical FEN is accepted. | `theorem readFEN_of_isFEN (h : IsFEN s p) : readFEN s = some p` (Round 4: was `readFEN_intercalate (p) (hcl : ClockFields cl) : readFEN (String.ofList ([' '].intercalate (p.fenFields ++ cl))) = some p`) | [core] |
| L5.19a | The text `toFEN` writes is a FEN of the position. *(helper, Round 4)* | `theorem Position.isFEN_toFEN (p : Position) : IsFEN p.toFEN p` | [core] |
| L5.20 | Reading the FEN of any position gives the position back. | `theorem readFEN_toFEN (p : Position) : readFEN p.toFEN = some p` (L5.19 and L5.19a) | [core] |
| L5.21 | Parsing the FEN of a sane position gives the position back. | `theorem parseFEN_toFEN (h : p.Sane) : parseFEN p.toFEN = some p` | [core] |
| L5.22a | The promotion choice is read back from its letter, or from nothing. *(helper)* | `theorem readPromo_toList (o : Option PromoKind) : readPromo (o.map PromoKind.letter).toList = o` | [core] |
| L5.22b | Reading the UCI writing of a move gives the move back. *(helper)* | `theorem readMove_toUCI (m : Move) : readMove m.toUCI.toList = m` | [core] |
| L5.22 | Parsing the UCI writing of any move gives the move back. | `theorem parseUCI_toUCI (m : Move) : parseUCI m.toUCI = some m` | [core] |
| L5.23 | `readFEN` accepts `s` with position `p` exactly when `s` is a FEN of `p`. | `theorem readFEN_eq_some_iff : readFEN s = some p ↔ IsFEN s p` (L5.3 and L5.19) | [core] |
| L5.23a | A string is a FEN of at most one position. *(Round 4)* | `theorem IsFEN.unique (hp : IsFEN s p) (hq : IsFEN s q) : p = q` (L5.19 twice) | [core] |
| L5.24 | `parseUCI` accepts `s` with move `m` exactly when `s` is the UCI writing of `m`. | `theorem parseUCI_eq_some_iff : parseUCI s = some m ↔ m.toUCI = s` (L5.11 and L5.22) | [core] |

Proof plan, for the translator (each step small; the whole group was estimated at 80–150 lines; in
Round 3 it took about 220 lines including docstrings and the helpers, all proved, so it was kept).
- L5.15: induction on `row` generalizing `k`. `readRow` is a `flatMap`, so `readRow (u ++ v) =
  readRow u ++ readRow v` (`List.flatMap_append`). Cases: `[]` uses `emptyCount?_digitChar` (L5.14e)
  for `1 ≤ k ≤ 8`; `none :: row` is the induction hypothesis at `k + 1`; `some pc :: row` uses
  `Piece.ofLetter?_letter` and `emptyCount?_letter` (L5.14c, L5.14d).
- L5.16: induction on `ws` through `splitOn.go`, as in L5.2.
- L5.17: field by field. Board: L5.16 with `sep := '/'` (no row text contains `/`: its characters are
  piece letters and the digits `0` to `8`, L5.15a; a bound is needed because `Nat.digitChar` is a
  sixteen-way `if` chain, so "no digit character is `/`" is not a finite check over all `k`, while
  `∀ k < 9` is), then L5.15 with `k := 0` for each row, then
  `Board.ext` and `List.getD` on `(List.finRange 8).reverse.map …` (`List.getD_eq_getElem?_getD`,
  `List.getElem?_map`, `List.getElem?_reverse`). Side to move, castling rights and en passant target:
  each is a finite check (`∀ c` by `decide`; `∀ cr` and `∀ t` by `decide +kernel`, because they
  reduce `String.toList`; `Option Square` has no `Decidable ∀` instance, so `e` is split into
  `none` and `some t`), using `CastlingRights.mem_all` (Position P4.3a, formerly L5.14a).
- L5.18 from L5.17 (apply `readFields` to both sides). L5.19 from L5.16 with `sep := ' '` (no field
  contains a space: finite checks, the row lemma, and for the clock fields `IsNumeral`, since a
  digit is not a space) and L5.17. L5.20 is L5.19 with the clocks `toFEN` writes. L5.21 from L5.20
  and L5.4.
- L5.22 from L5.10 and two finite checks: `Square.ofName? s.name.toList = some s` for every square
  (`decide +kernel`), and `readPromo ((o.map PromoKind.letter).toList) = o` for every `o`.

Together L5.3 and L5.19 give L5.23, and L5.19 applied twice gives L5.23a. L5.11 and L5.22 give
L5.24. In the Lean the UCI round trip (L5.22a, L5.22b, L5.22) comes before L5.23, so that the table
is in file order and in ID order (Round 4).

### Using `fen` and `uci` in proofs (Round 4)

For headline proofs that are not by evaluation: generated certificates can relate checkpoints
symbolically instead of re-evaluating `fen "…"` (about 0.5 s of kernel time per literal).

| ID | English | Lean | Tag |
|---|---|---|---|
| L5.25 | `fen s` is `p` exactly when `p` is sane and `s` is a FEN of `p`. | `theorem fen_eq_iff (h : (parseFEN s).isSome = true) : fen s h = p ↔ p.Sane ∧ IsFEN s p` (L5.6, L5.4, L5.23) | [core] |
| L5.26 | Taking `fen` of the FEN of a position gives the position back. | `theorem fen_toFEN (h : (parseFEN p.toFEN).isSome = true) : fen p.toFEN h = p` (L5.8, L5.19a, L5.23a) | [core] |
| L5.27 | `uci s` is `m` exactly when `s` is the UCI writing of `m`. | `theorem uci_eq_iff (h : (parseUCI s).isSome = true) : uci s h = m ↔ m.toUCI = s` (L5.11a, L5.24) | [core] |
| L5.28 | Taking `uci` of the UCI writing of a move gives the move back. | `theorem uci_toUCI (h : (parseUCI m.toUCI).isSome = true) : uci m.toUCI h = m` (L5.27) | [core] |

L5.25 and L5.27 are the statements a headline reader trusts (header). With them, neither the
readers nor the guards' code is part of the meaning of `fen "…"` or `uci "…"`.

---

## 6. Section "Tests"

**Where they live (2026-11-02).** These tests are in `ChessTest/ChessGame.lean`, in the test
library `ChessTest` (`lake build ChessTest`; not built by `lake build`), which imports
`ChessTest/MoveGen.lean` for `epCheckPos` and `promoKnightPos` and `ChessTest/Rules.lean` for
`foolsMate`. They were about 10 s of this module's 11 s build, paid by every file that imports this
module, generated certificate files included (review C3). The module keeps only these cheap
`#guard`s under `/-! ## Tests -/`, as documentation (interpreted, about 0.1 s together):

```lean
-- Writing the initial position, and reading it back from four fields.
#guard Position.initial.toFEN == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#guard readFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -" == some Position.initial
-- Rejected: not canonical FEN (`44`), and not sane (no Black king).
#guard (parseFEN "rnbqkbnr/pppppppp/44/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone
#guard (parseFEN "rnbqqbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone
-- UCI.
#guard parseUCI "e7e8q" == some ⟨⟨4, 6⟩, ⟨4, 7⟩, some .queen⟩  -- e7, e8
#guard (parseUCI "Nf3").isNone
```

What follows specifies `ChessTest/ChessGame.lean`, in this order. Kernel tests use
`decide +kernel`; `#guard` is evaluated by the interpreter. All passed in the scratch file; the
whole scratch module (definitions, lemmas, tests) elaborated in 21 s, of which about 20 s is kernel
checking of the tests.

```lean
-- Reading and writing the initial position.
example : fen "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1" = Position.initial := by
  decide +kernel
#guard Position.initial.toFEN == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
-- Four fields are accepted; the position is sane.
#guard readFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -" == some Position.initial
example : Position.initial.Sane := by decide +kernel
-- Writing and reading back the test positions of `Chess.MoveGen` (L5.20 on examples).
#guard [Position.initial, foolsMate, epCheckPos, promoKnightPos].all
  fun p => readFEN p.toFEN == some p
#guard epCheckPos.toFEN == "k7/8/8/3pP3/4K3/8/8/8 w - d6 0 1"
-- Rejected: not canonical FEN.
#guard (parseFEN "rnbqkbnr/pppppppp/44/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone   -- 44
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KqQk - 0 1").isNone   -- order
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0").isNone     -- 5 fields
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR  w KQkq - 0 1").isNone  -- 2 spaces
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 ").isNone  -- trailing
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBN w KQkq - 0 1").isNone    -- 7 files
-- Rejected: not sane.
#guard (parseFEN "rnbqqbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone   -- no k
#guard (parseFEN "4k3/8/8/8/8/8/4R3/4K3 w - - 0 1").isNone   -- Black, not to move, in check
#guard (parseFEN "4k3/8/8/8/8/8/4R3/4K3 b - - 0 1").isSome
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq e3 0 1").isNone  -- ep rank
#guard (parseFEN "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1").isSome
-- The clock fields are ignored: both strings denote the same position (THEOREMS G15).
example : fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 149 80" = fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1" :=
  by decide +kernel
-- UCI.
#guard parseUCI "e7e8q" == some ⟨⟨4, 6⟩, ⟨4, 7⟩, some .queen⟩  -- e7, e8
#guard (parseUCI "e7e8Q").isNone
#guard (parseUCI "e2e9").isNone
#guard (parseUCI "0000").isNone
#guard (parseUCI "e2e4 ").isNone
#guard (parseUCI "Nf3").isNone
-- Chess as a game: mate is a win, stalemate is not, and the headline vocabulary works.
example : WinsIn .black 0 (fen "rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 1 3") :=
  winsIn_zero_iff.2 ⟨rfl, by decide +kernel⟩                       -- Fool's mate
example : MateIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") := by decide +kernel
example : WinsIn .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1") :=
  Game.checkWin_sound (c := .move (uci "a1a8") .goal) (by decide +kernel)
example : ¬ Wins .white (fen "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1") :=  -- stalemate
  not_wins_of_stalemate (by decide +kernel) (by decide +kernel)
-- The diagnostic: nothing fails in the certificate above; `a1a7` is legal but does not mate, so
-- the leaf after it is not in the target; `a1h8` is not legal.
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1a8") .goal) == none
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1a7") .goal) == some ([uci "a1a7"], .notInTarget)
#guard Game.chess.firstFailureWin .white 1 (fen "6k1/5ppp/8/8/8/8/8/R5K1 w - - 0 1")
  (.move (uci "a1h8") .goal) == some ([], .unavailable (uci "a1h8"))
```

Notes.
- The three `firstFailureWin` guards (added in ROADMAP step 5, `docs/spec/Game.md` §4.2) run the
  diagnostic on chess: the accepted certificate of the example above, a legal move that does not
  mate, and an illegal move. They are interpreted (`#guard`), as the generator would run them.
- The `MateIn` example decides "not within 0" by search (`searchForces`) and is the module's one
  exact-distance check; it takes about 3 s. `#print axioms` on it shows `propext`,
  `Classical.choice` and `Quot.sound` *(checked)*, so it is [kernel].
- The two `#guard`s on `parseFEN … isSome` are the positive controls of the two rejections above
  them: the same strings with only the offending detail changed are accepted.
- `MoveGen`'s perft and agreement tests that need FEN (DESIGN §8.4's standard perft positions) live
  in the test library (`ChessTest/Perft.lean`), which imports this module; they are not repeated
  here.

---

## 7. Stage 2: G8, the chess game means FIDE chess (done, in two other files)

"FIDE chess" here means FIDE's rules of movement and checkmate (Articles 3 and 5.1), without the
rules of Articles 5.2.2 (dead position) and 9 (repetition, fifty and seventy-five moves).

*Round 1 planned this section at the end of `Chess/ChessGame.lean`. On 2026-11-02 it was carried
out in two separate files instead (ChessGame review C2, open item 2 below), and this section now
only records where each planned item went.* The English and Lean of each item are in
`docs/spec/Spec.Winning.md` and `docs/spec/ChessGame.Fide.md`.

| Round 1 plan | Now | Where |
|---|---|---|
| D7.1 `SpecForces` | `SpecForces`, as planned, with constructor docstrings | `Chess.Spec.Winning`, D1.1 |
| D7.2 `SpecWinsIn` | `SpecWinsIn`, an `abbrev` | `Chess.Spec.Winning`, D1.2 |
| D7.3 `SpecWins` | `SpecWins` | `Chess.Spec.Winning`, D1.3 |
| (not planned) | `SpecMateIn`, so that L7.5's `MateIn` half reads like the others | `Chess.Spec.Winning`, D1.4 |
| D7.4 `SpecOnlyWinningMove` | `SpecOnlyWinningMove`, as planned | `Chess.Spec.Winning`, D1.5 |
| L7.1 `mem_chess_moves` | as planned | `Chess.ChessGame.Fide`, L1.1 |
| L7.2 `chess_mated_iff_checkmate` | as planned | `Chess.ChessGame.Fide`, L1.2 |
| L7.3 `forces_iff_specForces` | as planned | `Chess.ChessGame.Fide`, L1.3 |
| L7.4 `winsIn_iff_specWinsIn` | as planned (THEOREMS G8) | `Chess.ChessGame.Fide`, L1.4 |
| L7.5 `wins_iff_specWins`; `mateIn_iff_spec` | `wins_iff_specWins`; `mateIn_iff_specMateIn` | `Chess.ChessGame.Fide`, L1.5, L1.6 |
| L7.6 `onlyWinningMove_iff_spec` | `onlyWinningMove_iff_specOnlyWinningMove` | `Chess.ChessGame.Fide`, L1.7 |

Also added: `specWinsIn_zero_iff` and `not_specWins_of_stalemate` (THEOREMS G2 in FIDE terms,
`Chess.Spec.Winning` L2.1, L2.2), proved from the definitions without the generator.

After these, a reader of a headline can read `SpecWinsIn`, `SpecMateIn` and `SpecOnlyWinningMove`
instead of `Chess.Game`, `legalMoves` and the abbreviations; no statement of this module changed.

### Stage 2 and the sanity filter: an open owner decision

*Undecided (2026-11-02).* This section was written in Round 2 as the plan. ChessGame review C4
recommends the opposite: keep `fen`'s filter at `Sane` for good, and check `WellFormed (fen "…")`
per literal, by `decide`, where a lemma needs it. Until the owner decides (ROADMAP §5, open owner
decisions), a Stage 2 worker must not change `parseFEN`: either choice changes what M11.1 can say,
and the first changes the trusted statement `fen_eq_iff`. The two options:

- *Keep `Sane` (review C4).* `fen_eq_iff` and the meaning of every `fen "…"` literal stay as they
  are. M11.1 as stated (`parseFEN s = some p → WellFormed p`) is then false, for any `WellFormed`
  that checks castling rights, pawn ranks or the en passant victim: today `parseFEN` accepts
  `4k3/8/8/8/8/8/8/4K3 w KQkq - 0 1` (castling rights with no rook), `k7/8/8/8/8/8/8/K6P w - - 0 1`
  (a pawn on the last rank) and `4k3/8/8/8/8/8/8/4K3 w - e6 0 1` (an en passant target with no
  pawn). M11.1 is dropped or restated as the per-literal check.
- *Strengthen the filter (the Round 2 plan, below).* `fen_eq_iff` gains a conjunct, and the
  literals whose positions are not `WellFormed` become compile-time errors.

The Round 2 plan, kept as written: when `Chess/Invariants.lean` defines `WellFormed` (R9),
`parseFEN`'s filter is strengthened from `p.Sane` to `p.Sane ∧ WellFormed p`, and M11.1 (`parseFEN_wellFormed : parseFEN s = some p →
WellFormed p`) is proved beside L5.5. The new filter never accepts a string that Stage 1 rejected,
and an accepted string still denotes the same position, because the position comes from `readFEN`.
Stage 1 strings whose positions are not `WellFormed` (for example castling rights `KQkq` with no
rook on h1) become compile-time errors; the Stage 2 translator re-runs every `fen "…"` literal of
the library to find them. Using the conjunction keeps `parseFEN_sane` and `fen_sane` true without
needing `WellFormed → Sane`.

---

## 8. Design choices, with reasons

1. **The chess game is built from the generator, and `Mated` is executable** (DESIGN §6.4,
   THEOREMS open question 3). Stage 1 was not blocked on M4; G8 (`Chess.ChessGame.Fide`) links
   both to FIDE with no statement changing.
2. **`decMated` and `decEqMove` are explicit** (D1.1 notes; Game review C1.1): a change of `Mated`
   must not silently change the decision procedure every certificate runs.
3. **`abbrev` for `Game.chess` and the four chess names** (Game review C1.2): positions and moves
   pass where game states and game moves are expected, and the generic theorems apply by dot
   notation *(checked)*.
4. **Readers propose; the guard (writing back) disposes.** Parsing is the classic place for silent errors (the
   prototype's `fenChars` returned the default position on anything it did not recognise, and its
   `epSquare` returned 64). Here the trusted meaning of a string is "the position whose writing it
   is", stated by L5.8 and L5.25 and proved in Stage 1, and the readers can be as lenient as convenient
   because they decide nothing. Reasons:
   - *Smaller trusted base.* A writer is a total function with no error cases; auditing it means
     reading eight short definitions. The readers (fourteen definitions, `splitOn` included) are out
     of the trusted base, and since the characterisations were proved (Round 3) so is the guards'
     code: what remains is the writers, four predicates (D4.1, D4.2, D4.2a, D4.5) and the statements
     of L5.25 and L5.27.
   - *Soundness of M11 in Stage 1, for free.* L5.3 and L5.11 are a few lines each; THEOREMS put M11
     in Stage 5.
   - *The same pattern as the generator* (MoveGen design choice 1), so the library has one idea for
     "compute, then check against the specification", not two.
   - *Cost, measured.* The guard writes the proposed position again and compares the lists: about
     0.5 s of kernel time per `fen "…"` literal, including the sanity check, paid once when the
     literal is elaborated (the auto-proof) and once more when a proof by evaluation reduces it.
   - *Rejected:* a strict parser that checks each field's grammar itself (the prototype's shape,
     made strict). It is about as long as reader plus guard, and all of it is trusted.
5. **Only canonical FEN is accepted** (a consequence of 4): castling letters in `KQkq` order, runs of
   empty squares as one digit, single spaces, lower-case `w`/`b`. This is what every engine and
   library writes for the board, side to move and castling fields. For the en passant field, see
   choice 8. A non-canonical string is a compile-time error, the safe direction. The gain is
   that a position has exactly one FEN up to its clock fields (its four fields are a function of
   it, `Position.fenFields`), and a string is a FEN of at most one position (L5.18, L5.23a). So the
   four-field text, or `toFEN` with its fixed `0 1`, can serve as a key in generated files. The
   full string cannot: `IsFEN` accepts any two numerals as clocks, or none (choice 6), so one
   position has many FENs.
6. **Four or six fields; clocks read as numerals and ignored** (DESIGN §8.6 said six until
   2026-11-02; it now says four or six). `Position` has no clock (DESIGN §4.6), and puzzle collections and EPD-style
   sources often omit the clock fields. `toFEN` writes six, with `0 1`. The clocks are not useless:
   the halfmove clock is exactly what THEOREMS G15 needs (`Fide.winsIn_of … (hc : c + 2 * n ≤ L)`)
   and M11 assigns it to the game layer (G12). In Stage 1 it is dropped, so a `WinsIn` stated with
   `fen "…"` says nothing about the fifty- and seventy-five-move rules (D1.1 notes); reading the
   clock is open item 5.
7. **The sanity filter is three named conditions, separate from reading** (D4.5): reading is the
   exact inverse of writing for every position (L5.19), and judging is a decidable predicate a
   reader can check against DESIGN §6.4. The third condition (en passant rank) is added to the two
   of DESIGN §6.4 because it catches a real transcription error at no cost and FEN itself requires
   it. DESIGN §6.4 and §8.6 name all three since 2026-11-02.
8. **The en passant target is written as stored** (D2.7), after every double push, matching
   `play` (DESIGN §4.6). Stockfish, Lichess and python-chess's default `en_passant="legal"` write `-`
   when no en passant capture is possible. Such a FEN is accepted, but it denotes a *different*
   `Position` from the one `play` produces: after 1.e4, Stockfish's FEN has `epTarget = none`, which
   is not `Position.initial.play (uci "e2e4")`. This matters for checkpoint equalities in generated
   certificates (DESIGN §7.4) and for any headline that equates `fen "…"` with a played position.
   Two FENs that differ only in an unusable en passant target denote different positions, and no
   Stage 1 lemma says they have the same game value (checked in the Round 4 critique: the Lichess
   FEN after 1.e4 is `≠ Position.initial.play (uci "e2e4")` by `decide +kernel`). The lemma that
   closes this gap is THEOREMS G16: `Position.normalize` drops an unusable target, and
   `legalMoves_normalize`, `play_normalize` make normalization a game morphism (G7), so `Wins`,
   `WinsIn` and `OnlyWinningMove` agree on `p` and `p.normalize`. With it, headlines stated with
   tool-produced FENs transfer, and certificate checkpoints can be compared after `normalize`.
   Until then, an author pasting a FEN from those tools after a double push should restore the
   target.
9. **Everything over `List Char`.** `String.toList` of a literal reduces quickly in the Lean 4.28
   kernel (a 56-character FEN in well under a second, measured), while `String` operations such as
   `String.splitOn` work on byte positions. The writers, the readers and the guards all work on
   lists. The only `String` values met are the input string itself (through `String.toList`), the
   output of `toFEN` (through `String.ofList`), and three writers of other modules, each read
   through `String.toList`: `Square.name` of `Chess.Basic` (L5.9), and `CastlingRights.letters` and
   `Move.toUCI` of `Chess.Position` (L5.10).
10. **`fen` and `uci` take a proof, discharged by `decide +kernel`** (DESIGN §8.6): no default
    position, no `Option` in statements, and the failure message names the string.
11. **The parsed board is a list lookup** (D3.5), resolving DESIGN §10's open question by
    measurement: as fast as `Board.unpack`, and readable.
12. **`uci` does not check legality.** A move is data; whether it is legal is part of the claim
    (`OnlyWinningMove` requires `m ∈ legalMoves p`). A `uci` that consulted a position would tie
    notation to the rules.
13. **No SAN.** SAN depends on the position and on disambiguation, and identifies moves badly (the
    dwrensha pitfall, *prior-work* §5). Moves in statements are UCI; a SAN printer for display is
    future, untrusted work.

---

## 9. Requests to other modules, and deviations from DESIGN and THEOREMS

Requests (not made here; each owner decides):

1. **`Chess.Position`, the "Display" heading** (Position review C3). This module makes
   `Kind.letter`, `Piece.letter`, `PromoKind.letter`, `CastlingRights.letters` and `Move.toUCI`
   trusted: the guards compare against them. The heading "Display (untrusted: nothing in the
   specification reads it)" becomes false when this module is written. Split it into "Notation
   (trusted: the FEN and UCI guards of `Chess.ChessGame` compare against these)" and "Display"
   (`rankLine`, `diagram`, the `Repr` and `ToString` instances). The same holds for `Square.name`,
   `Square.fileChar` and `Square.rankChar` in `Chess.Basic`. **Still open at Round 4**: the heading
   stands at `Chess/Position.lean` line 548 and `Chess/Basic.lean` line 1036. This is the most
   important fidelity defect outside this file: a reader told those definitions are untrusted would
   skip auditing part of the meaning of `fen` and `uci`.
2. ~~**`Chess.Position`, `CastlingRights.all`.**~~ Done in the readability round of 2026-11-02:
   D3.8 and its two lemmas are Position D4.6a and P4.3a, and `Board.squaresOf` (D4.4, L5.13) is
   Position D1.6 and P1.8.
3. **`Chess.Invariants` (Stage 2), `WellFormed`** (optional). Including "the en passant target is on
   the sixth rank counted from the side to move" (D4.5's third condition) and proving
   `WellFormed.sane` would let a strengthened Stage 2 filter (§7, undecided) be `WellFormed` alone.
   It is not needed: that plan's filter is `p.Sane ∧ WellFormed p`. Under review C4's option the
   filter stays `p.Sane`, and `WellFormed.sane` would only let a lemma that has `WellFormed` skip
   `Sane`.

Deviations:

- DESIGN §8.6 said `parseFEN` "reads and ignores the two clock fields"; here the clock fields may
  also be absent (choice 6), and a third rejection is added (choice 7). (DESIGN §6.4, §6.5 and
  §8.6 were brought in line on 2026-11-02, `docs/process/ChessGame.md` Round 8.)
- DESIGN §10 open question "board through `unpack` or `set`s": resolved, neither (D3.5).
- THEOREMS M11.2 was `parseFEN_toFEN (h : WellFormed p) : parseFEN (toFEN p) = some p.normalize`.
  Here it is L5.21 with `p.Sane` and no `normalize`, because `toFEN` writes the stored target, so
  nothing is lost. THEOREMS M11's soundness parts move to Stage 1 (L5.3, L5.8, L5.11). (Round 4:
  THEOREMS M11 now states what is proved.)
- G8 names, here: `mem_chess_moves`, `chess_mated_iff_checkmate`, `winsIn_iff_specWinsIn` (§7; since
  2026-11-02 also `wins_iff_specWins`, `mateIn_iff_specMateIn`,
  `onlyWinningMove_iff_specOnlyWinningMove`), so that the names say which side of the `↔` is which;
  G1's chess game is `Game.chess` (DESIGN §2). (Round 4: THEOREMS was updated to these names; it
  used `Chess.mem_moves_iff`, `Chess.mated_iff`, `Chess.winsIn_iff_spec` and `Chess.game`.)
- THEOREMS M11.3 includes `parseSAN_toSAN`. There is no SAN here (choice 13), so it is dropped.

---

## 10. Open items

1. **A diagnostic for rejected strings.** When `fen "…"` fails, the error says only that parsing
   failed. An untrusted `#eval`-able `explainFEN : String → String` that names the first failing
   check (which field differs from its writing, or which sanity condition fails) would help
   authors. Not needed for correctness.
2. **Where G8 lives.** *Decided 2026-11-02* (ChessGame review C2): not in this file. The FIDE
   definitions are in `Chess/Spec/Winning.lean` (imports `Chess.Rules` only) and the equivalences
   in `Chess/ChessGame/Fide.lean` (imports this module and `Chess.Spec.Winning`; M4 is in
   `Chess.MoveGen` itself, so no `MoveGen.Correct` file exists). This module did not change except
   for comments and two docstrings, so certificate files that import it do not depend on G8.
3. **Headlines checkable without the reader.** THEOREMS M11 suggests that until M11 is proved, each
   headline's position also be checkable as a literal. With L5.25 proved in Stage 1 the reader is
   already out of the trusted base, so this is optional; the pattern, if wanted, is a test
   `fen "…" = ⟨Board.unpack 0x…, turn, rights, ep⟩` by `decide +kernel`, as in §6 for the initial
   position.
4. **Whether to keep the four-field FEN** (choice 6). One extra case in `ClockFields`; drop it if
   the owner prefers exactly six. Open item 5 weighs against keeping it.
5. **Reading the halfmove clock** (Round 4; THEOREMS M11, G12, G15). Today the halfmove clock in a
   headline's own FEN string cannot be read anywhere, and a four-field FEN has none. Plan: an
   untrusted reader `fenClock : String → Option Nat` with a writing-back guard, as for positions,
   and a trusted statement in the style of `IsFEN` (`s` ends in the numerals of `c` and of some move
   number). G15 headlines then take their clock from the same string, and need six-field FENs.
6. **Where the generic list lemmas live** (Round 4 critique E3). `intercalate_singleton_cons` (L5.1)
   and `mem_intercalate` (L5.16c) are about `List α`, not chess, yet are named `Chess.…`. Moving
   them to a `Chess/Util/List.lean` (or into `List` names) is a library-layout decision for DESIGN;
   until then they stay here, where their only users are.

---

## 11. Checklist for the translator

- `import Chess.MoveGen`, `import Chess.Game.Search` and `import Chess.Game.Cert`; add
  `import Chess.ChessGame` to `Chess.lean`.
- Module docstring `/-! # ChessGame … -/` with `## Main definitions` (`Game.chess`; `WinsIn`,
  `Wins`, `MateIn`, `OnlyWinningMove`; `Position.toFEN`, `Position.fenFields`; `readFEN`,
  `Position.Sane`, `parseFEN`, `fen`; `parseUCI`, `uci`; since Round 4 also `IsFEN`), `## Main
  statements` (since Round 4, led by `fen_eq_iff`, `uci_eq_iff`, the three characterisations
  `readFEN_eq_some_iff`, `parseFEN_eq_some_iff`, `parseUCI_eq_some_iff`, then `IsFEN.unique`,
  `Position.fenFields_injective`, the round trips, and `winsIn_zero_iff`, `not_wins_of_stalemate`),
  and `## Implementation notes` summarizing design choices 1, 2, 3, 4 (readers propose, the guard
  disposes, with the list of what is trusted from the header of this spec), 5, 6 (the clocks) and 7,
  and saying where G8 is proved (`Chess.ChessGame.Fide`, since 2026-11-02) and that no statement of
  this file depends on it.
- Section order as in "Contents"; each a `/-! ## … -/` heading; §3's heading says
  "Reading (untrusted: the guards check every result)"; §4's heading is "Accepting", followed by
  the comment quoted at the start of §4. Lemmas in `section Notation` (§5), with its
  `variable` line.
- `Chess.Move` qualified inside every `Game.…` declaration (§0).
- Every `def`, `abbrev`, `structure`, structure field, `instance` and `theorem` carries the docstring
  given here, word for word. `splitOn.go` carries the docstring in D3.0. Nothing is `sorry`; no
  `native_decide`. No [later] lemmas remain in this file; §7 records where they went.
- No `@[simp]` (Round 4: it was on L1.1–L1.4, where `simp` did not use it; L1 notes).
- Instances: `IsNumeral.decidable`, `ClockFields.decidable`, `Position.Sane.decidable`. No others.
- Tests at the end under `/-! ## Tests -/`, as in §6, in that order. The module should elaborate in
  under 40 s; if it does not, demote the slowest kernel examples to `#guard` and record it in the
  process log.
- Lines at most 100 characters.
- Record in `docs/process/ChessGame.md` every place where the Lean forced the English to change.
