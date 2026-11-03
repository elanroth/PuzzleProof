import Chess.MoveGen
import Chess.Game.Search
import Chess.Game.Cert

/-!
# ChessGame

Chess as a game of `Chess.Game`, the vocabulary of headline theorems, and the FEN and UCI notation
in which their positions and moves are written. Specification: `docs/spec/ChessGame.md`; every
definition below carries the docstring given there.

## Main definitions

* `Game.chess`: chess as a game. The states are positions, the available moves are those listed by
  `legalMoves`, a move is played by `Position.play`, and the side to move has been mated when it is
  in check and no move is listed.
* `WinsIn`, `Wins`, `MateIn`, `OnlyWinningMove`: the four notions of `Chess.Game`, specialised to
  chess, so that a headline reads
  `OnlyWinningMove (fen "…") (uci "…") ∧ WinsIn .black 11 (fen "…")`.
* `Position.fenFields`, `Position.toFEN`: how a position is written in FEN.
* `IsFEN`, `Position.Sane`: when a string is a FEN of a position, and which positions are accepted.
* `readFEN`, `parseFEN`, `fen`: reading a FEN, and the notation `fen "…"`, whose proof of parsing is
  found by evaluation.
* `parseUCI`, `uci`: reading a UCI move, and the notation `uci "…"`.

## Main statements

* `fen_eq_iff`, `uci_eq_iff`: what the notation means. `fen s` is `p` exactly when `p` is sane and
  `s` is a FEN of `p`; `uci s` is `m` exactly when `s` is the UCI writing of `m`.
* `readFEN_eq_some_iff`, `parseFEN_eq_some_iff`, `parseUCI_eq_some_iff`: the parsers accept exactly
  what `IsFEN`, `Position.Sane` and `Move.toUCI` describe.
* `IsFEN.unique`, `Position.fenFields_injective`: a string is a FEN of at most one position, because
  the FEN writing loses no information.
* `readFEN_toFEN`, `parseFEN_toFEN`, `parseUCI_toUCI`: the parsers read back what the writers write.
* `winsIn_zero_iff`, `not_wins_of_stalemate` (G2 in chess): mate is a win, stalemate is not.

## Implementation notes

* The chess game is built from the move generator, and `Mated` is the executable
  `InCheck p ∧ legalMoves p = []`, decided through the generator. G8, in
  `Chess.ChessGame.Fide`, proves that the listed moves are exactly the FIDE-legal ones
  (`mem_legalMoves`, M4), that being mated is `Checkmate`, and that `WinsIn`, `Wins`, `MateIn` and
  `OnlyWinningMove` are equivalent to `SpecWinsIn`, `SpecWins`, `SpecMateIn` and
  `SpecOnlyWinningMove` of `Chess.Spec.Winning`, which are written with `Chess.Rules` alone. No
  statement of this file depends on G8.
* `decMated` and `decEqMove` are given explicitly in `Game.chess`, so that a change of `Mated`
  visibly changes the decision procedure every certificate runs.
* `Game.chess` and the four chess names are `abbrev`s, so that positions and moves pass where game
  states and game moves are expected, and the theorems of `Chess.Game` apply by dot notation.
* Readers propose; the guard (writing back) disposes. A reader (section "Reading") turns text into
  a proposed position or move, and a string is accepted only if writing the proposal back gives the
  string. The characterisations above are proved, so neither the readers nor the guards are
  trusted. What a reader of a headline must trust is: the definition of `Game.chess` and the four
  abbreviations, or instead, through the equivalences of `Chess.ChessGame.Fide`, the definitions
  of `Chess.Spec.Winning`; the writers (section "Writing", with the letters of `Chess.Position` and
  the square names of `Chess.Basic` that they use); the predicates `IsNumeral`, `ClockFields`,
  `IsFEN` and `Position.Sane` (section "Accepting"); and the statements of `fen_eq_iff` and
  `uci_eq_iff`.
* A position records no clocks. The clock fields of a FEN must be two numerals, or absent, and are
  ignored, so a `WinsIn` stated with `fen "…"` may still be a draw under FIDE's fifty- and
  seventy-five-move rules (THEOREMS G15).
* Only canonical FEN is accepted: castling letters in `KQkq` order, runs of empty squares as one
  digit, single spaces. The en passant target is written as stored, after every two-square advance,
  which Stockfish and Lichess do not do when no capture is possible.
* The sanity filter `Position.Sane` is three named conditions, kept apart from reading: one king per
  side, the side not to move not in check, and an en passant target on the right rank.
-/

namespace Chess

/-! ## Chess as a game -/

section ChessAsAGame

variable {a : Color} {n : Nat} {p : Position}

/-- Chess as a game: the states are positions, the moves are values of `Chess.Move`
(source, destination, promotion choice), the side to move is the position's turn, the available
moves are those listed by the move generator `legalMoves`, a move is played by `Position.play`, and
the side to move has been mated when it is in check and the generator lists no move for it. Play
ends only by mate or by the side to move having no listed move. There is no clock, no fifty- or
seventy-five-move rule, no repetition rule and no dead-position rule, so a win here is a win under
FIDE only when those rules do not intervene (THEOREMS G15). The listed moves are exactly the legal
moves of `Chess.Rules` (`mem_legalMoves`), and `Chess.ChessGame.Fide` restates the notions of this
game with `Legal` and `Checkmate` (THEOREMS G8). -/
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

/-- `WinsIn a n p`: from position `p`, whichever side is to move there, the side `a` can
force the other side to be mated using at most `n` moves of its own, the mating move included,
whatever the other side plays. This is chess as computed by the move generator (moves are those
listed by `legalMoves`; 'mated' means in check with no listed move, as in `Game.chess`), without
move-count or repetition rules. -/
abbrev WinsIn (a : Color) (n : Nat) (p : Position) : Prop := Game.chess.WinsIn a n p

/-- `Wins a p`: from position `p`, the side `a` can force the other side to be mated within
some number of its own moves, a bound fixed in advance (`∃ n, WinsIn a n p`). This is chess as
computed by the move generator (moves are those listed by `legalMoves`; 'mated' means in check with
no listed move, as in `Game.chess`), without move-count or repetition rules. -/
abbrev Wins (a : Color) (p : Position) : Prop := Game.chess.Wins a p

/-- `MateIn a n p`: from position `p`, the side `a` mates in exactly `n`: it can force the
other side to be mated within `n` moves of its own, and not within fewer. This is chess as computed
by the move generator (moves are those listed by `legalMoves`; 'mated' means in check with no
listed move, as in `Game.chess`), without move-count or repetition rules. -/
abbrev MateIn (a : Color) (n : Nat) (p : Position) : Prop := Game.chess.MateIn a n p

/-- `OnlyWinningMove p m`: `m` is listed by `legalMoves p`, the side to move wins after `m`,
and after every other listed move it does not win. 'Other' means a different move value: promotions
to different pieces are different moves, so if `e7e8q` and `e7e8r` both win, neither is the only
winning move. An alternative that wins only slowly still counts as winning, so it makes this false.
This is chess as computed by the move generator (moves are those listed by `legalMoves`; 'mated'
means in check with no listed move, as in `Game.chess`), without move-count or repetition rules. -/
abbrev OnlyWinningMove (p : Position) (m : Move) : Prop := Game.chess.OnlyWinningMove p m

/-- The moves available in chess at `p` are the moves listed by `legalMoves p`. -/
theorem Game.chess_moves (p : Position) : Game.chess.moves p = legalMoves p := rfl

/-- Playing a move in chess is `Position.play`. -/
theorem Game.chess_play (p : Position) (m : Chess.Move) :
    Game.chess.play p m = p.play m := rfl

/-- The side to move in chess is the position's turn. -/
theorem Game.chess_turn (p : Position) : Game.chess.turn p = p.turn := rfl

/-- In chess the side to move has been mated exactly when it is in check and `legalMoves` lists no
move. -/
theorem Game.chess_mated (p : Position) :
    Game.chess.Mated p ↔ InCheck p ∧ legalMoves p = [] := Iff.rfl

/-- `WinsIn a 0 p` holds exactly when the other side is to move at `p`, is in check, and has no
listed move: `a` has already won. (THEOREMS G2, read in chess.) -/
theorem winsIn_zero_iff : WinsIn a 0 p ↔ p.turn = a.other ∧ InCheck p ∧ legalMoves p = [] :=
  Game.winsIn_zero_iff

/-- In a position where the side to move is not in check and has no listed move (stalemate, as the
generator sees it; `stalemate_iff` (M6) says it is FIDE stalemate), neither side wins. (THEOREMS
G2.) -/
theorem not_wins_of_stalemate (hc : ¬ InCheck p) (hl : legalMoves p = []) : ¬ Wins a p :=
  Game.not_wins_of_stalemate (G := Game.chess) (fun h => hc h.1) hl

end ChessAsAGame

/-! ## Writing (trusted) -/

/-- How FEN writes a run of `k` empty squares inside a row: nothing if `k = 0`, otherwise
the single character `k.digitChar`, which is the digit `k` when `1 ≤ k ≤ 9`. `rowChars` calls it
only with `k ≤ 8` when the row has at most eight squares. -/
def emptyRun (k : Nat) : List Char := if k = 0 then [] else [k.digitChar]

/-- `rowChars k row`: the FEN text of the squares `row`, from left to right, when `k` empty
squares have just been passed and not yet written. Each piece is written as its letter (upper case
for White, lower case for Black), and each maximal run of empty squares as one digit, its length;
the first run includes the `k` pending squares. (A board row has eight squares and is written with
`rowChars 0`, so every run is one of the digits `1` to `8`.) -/
def rowChars : Nat → List (Option Piece) → List Char
  | k, [] => emptyRun k
  | k, none :: row => rowChars (k + 1) row
  | k, some pc :: row => emptyRun k ++ pc.letter :: rowChars 0 row

/-- The contents of the eight squares of `b` whose rank index is `r` (rank `r + 1`), from
the a-file to the h-file. -/
def Board.row (b : Board) (r : Fin 8) : List (Option Piece) :=
  (List.finRange 8).map fun f => b ⟨f, r⟩

/-- The first field of FEN, the board: its eight ranks from rank 8 down to rank 1, each
written by `rowChars`, separated by `/`. -/
def Board.fenChars (b : Board) : List Char :=
  ['/'].intercalate ((List.finRange 8).reverse.map fun r => rowChars 0 (b.row r))

/-- The FEN letter of the side to move: `w` for White, `b` for Black. -/
def Color.fenChar (c : Color) : Char :=
  match c with
  | .white => 'w'
  | .black => 'b'

/-- The fourth field of FEN, the en passant target: the square's name, such as `e3`, or `-`
if there is none. -/
def epChars (e : Option Square) : List Char :=
  match e with
  | none => ['-']
  | some t => t.name.toList

/-- The four FEN fields of `p` that describe the position itself: the board, the side to
move, the castling rights (the letters `KQkq` of the rights held, in that order, or `-`), and the
en passant target as `p` stores it. Positions produced by `Position.play` store a target after
every two-square pawn advance, whether or not a capture is possible (the convention of the PGN
standard's FEN section). -/
def Position.fenFields (p : Position) : List (List Char) :=
  [p.board.fenChars, [p.turn.fenChar], p.castling.letters.toList, epChars p.epTarget]

/-- The FEN of `p`: its four fields, then the clock fields `0 1`, separated by single
spaces. A position records no clocks, so the halfmove clock is written as 0 and the move number as
1. -/
def Position.toFEN (p : Position) : String :=
  String.ofList ([' '].intercalate (p.fenFields ++ [['0'], ['1']]))

/-! ## Reading (untrusted: the guards check every result) -/

/-- The pieces of `cs` between the occurrences of `sep`, in order: one more piece than there
are occurrences of `sep`, and empty pieces kept, so that joining the pieces with `sep` gives `cs`
back (`intercalate_splitOn`). -/
def splitOn (sep : Char) (cs : List Char) : List (List Char) :=
  (go cs).1 :: (go cs).2
where
  /-- The first piece of the list (up to the first `sep`), and the remaining pieces in order. -/
  go : List Char → List Char × List (List Char)
    | [] => ([], [])
    | ch :: cs =>
      let (w, ws) := go cs
      if ch = sep then ([], w :: ws) else (ch :: w, ws)

/-- The number of empty squares that the FEN digit `ch` stands for, if `ch` is one of the
digits `1` to `8`. -/
def emptyCount? (ch : Char) : Option Nat := (List.range' 1 8).find? fun k => k.digitChar = ch

/-- The piece whose FEN letter is `ch`, if any. -/
def Piece.ofLetter? (ch : Char) : Option Piece := Piece.all.find? fun pc => pc.letter = ch

/-- The squares that one character of a FEN row proposes: `k` empty squares for a digit
`k`, otherwise one square holding the piece with that letter, or one empty square if no piece has
that letter. -/
def readChar (ch : Char) : List (Option Piece) :=
  match emptyCount? ch with
  | some k => List.replicate k none
  | none => [Piece.ofLetter? ch]

/-- The squares that a FEN row proposes, from left to right: the squares of each character
in turn. The result may be shorter or longer than eight squares; the guard rejects such a row. -/
def readRow (cs : List Char) : List (Option Piece) := cs.flatMap readChar

/-- The board whose square `s` holds entry number `s.file` of row number `7 − s.rank` of
`rows`, both counting from 0, the rows being listed from rank 8 down to rank 1 as in FEN; empty
where `rows` has no such entry. -/
def Board.ofRows (rows : List (List (Option Piece))) : Board :=
  fun s => (rows.getD s.rank.rev.val []).getD s.file.val none

/-- The board that a FEN board field proposes: its rows, separated by `/`, each read by
`readRow`. -/
def readBoard (cs : List Char) : Board := Board.ofRows ((splitOn '/' cs).map readRow)

/-- The side to move that a FEN field proposes: the colour whose letter the field is, or
White if there is none. -/
def readTurn (cs : List Char) : Color :=
  (Color.all.find? fun c => [c.fenChar] = cs).getD .white

/-- The castling rights that a FEN field proposes: the rights whose FEN letters the field
is, or no rights if there are none. -/
def readCastling (cs : List Char) : CastlingRights :=
  (CastlingRights.all.find? fun cr => cr.letters.toList = cs).getD .none

/-- The square whose name, such as `e4`, is `cs`, if any. -/
def Square.ofName? (cs : List Char) : Option Square :=
  Square.all.find? fun s => s.name.toList = cs

/-- The position that the first four fields of a FEN propose: board, side to move,
castling rights and en passant target, each read from its field. Missing fields read as empty. -/
def readFields (fs : List (List Char)) : Position :=
  ⟨readBoard (fs.getD 0 []), readTurn (fs.getD 1 []), readCastling (fs.getD 2 []),
    Square.ofName? (fs.getD 3 [])⟩

/-- The promotion choice that the end of a UCI move proposes: the kind whose letter (`n`,
`b`, `r` or `q`) the text is, or none. -/
def readPromo (cs : List Char) : Option PromoKind :=
  PromoKind.all.find? fun pk => [pk.letter] = cs

/-- The move that UCI text proposes: the source square from its first two characters, the
destination square from the next two, and the promotion choice from the rest. A square that cannot
be read is proposed as a1. -/
def readMove (cs : List Char) : Move :=
  ⟨(Square.ofName? (cs.take 2)).getD ⟨0, 0⟩, (Square.ofName? ((cs.drop 2).take 2)).getD ⟨0, 0⟩,
    readPromo (cs.drop 4)⟩

/-! ## Accepting

The predicates `IsNumeral`, `ClockFields`, `IsFEN` and `Position.Sane` are trusted: they say what an
accepted string means. The parsers `readFEN`, `parseFEN` and `parseUCI` are not:
`readFEN_eq_some_iff`, `parseFEN_eq_some_iff` and `parseUCI_eq_some_iff` prove that they accept
exactly what those predicates and `Move.toUCI` describe. -/

/-- `cs` is a non-empty run of the digits `0` to `9`, such as `0`, `12` or `007`. Leading
zeros and arbitrarily large values are allowed; the value is never read. -/
def IsNumeral (cs : List Char) : Prop := cs ≠ [] ∧ ∀ ch ∈ cs, ch.isDigit = true

/-- Whether a list of characters is a numeral is decided character by character. -/
instance IsNumeral.decidable (cs : List Char) : Decidable (IsNumeral cs) := by
  unfold IsNumeral; infer_instance

/-- `fs` are acceptable clock fields for the end of a FEN: none at all, or exactly two
numerals (the halfmove clock and the move number). Their values are not read or checked: a move
number of `0`, which FEN forbids, is accepted. -/
def ClockFields (fs : List (List Char)) : Prop :=
  fs = [] ∨ (fs.length = 2 ∧ ∀ w ∈ fs, IsNumeral w)

/-- Whether the fields are acceptable clock fields is decided field by field. -/
instance ClockFields.decidable (fs : List (List Char)) : Decidable (ClockFields fs) := by
  unfold ClockFields; infer_instance

/-- `IsFEN s p`: `s` is a FEN of `p`. Its characters are the four FEN fields of `p`
(`Position.fenFields`) followed by acceptable clock fields, joined by single spaces. The clock
fields are not part of the position, so a position has many FENs, which differ only in their
clocks. -/
def IsFEN (s : String) (p : Position) : Prop :=
  ∃ cl, ClockFields cl ∧ s.toList = [' '].intercalate (p.fenFields ++ cl)

/-- `p` passes the sanity checks that `parseFEN` makes: each side has exactly one king,
the side not to move is not in check, and an en passant target, if any, lies on the rank that a
pawn of the side not to move crosses in a two-square advance. This is weaker than
well-formedness (Stage 2). -/
structure Position.Sane (p : Position) : Prop where
  /-- Each colour has exactly one king on the board. -/
  one_king : ∀ c, (p.board.squaresOf ⟨c, .king⟩).length = 1
  /-- The side not to move is not in check: no king of its colour is attacked by the side to
  move. -/
  not_kingAttacked_other : ¬ p.board.KingAttacked p.turn.other
  /-- The en passant target, if there is one, is on the sixth rank counted from the side to move
  (`relRank p.turn = 5`, counting from 0): rank 6 when White is to move, rank 3 when Black is.
  That is the rank a pawn of the other colour crosses in a two-square advance. -/
  epTarget_relRank : ∀ t, p.epTarget = some t → t.relRank p.turn = 5

/-- Whether a position is sane is decided by counting kings, looking for an attack on the
king of the side not to move, and reading the rank of the en passant target. -/
instance Position.Sane.decidable (p : Position) : Decidable p.Sane :=
  -- The three conditions are restated on purpose: if they drift from the fields of `Sane`, the
  -- anonymous constructors below stop type-checking.
  decidable_of_iff ((∀ c, (p.board.squaresOf ⟨c, .king⟩).length = 1) ∧
      ¬ p.board.KingAttacked p.turn.other ∧ ∀ t, p.epTarget = some t → t.relRank p.turn = 5)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- Reads the FEN `s`. Its fields are the pieces of `s` between occurrences of the space
character; two adjacent spaces give an empty field, which no writer produces, so such a string is
rejected, and tabs and other whitespace are not separators. The result is the position `p` proposed
by the first four fields, provided those four fields are exactly the FEN writing of `p`
(`Position.fenFields p`) and the remaining fields are acceptable clock fields; otherwise `none`. So
`readFEN s = some p` exactly when `IsFEN s p` (`readFEN_eq_some_iff`). -/
def readFEN (s : String) : Option Position :=
  let fs := splitOn ' ' s.toList
  let p := readFields fs
  if p.fenFields = fs.take 4 ∧ ClockFields (fs.drop 4) then some p else none

/-- Parses the FEN `s`: the position whose FEN is `s` (`readFEN`), if it is sane
(`Position.Sane`); otherwise `none`. The clock fields, if present, must be numerals and are
ignored. -/
def parseFEN (s : String) : Option Position :=
  match readFEN s with
  | some p => if p.Sane then some p else none
  | none => none

/-- The position whose FEN is `s`, for use in statements: `fen "…"`. It is the one sane position
of which `s` is a FEN (`fen_eq_iff`; there is only one by `IsFEN.unique`). The clocks are not part
of the position: `s` may end in any two numerals, or in none (see THEOREMS G15). The proof that `s`
parses is found automatically, by evaluation, when the term is elaborated; a string that is not a
FEN of a sane position is a compile-time error, never a default position. The en passant field is
read as written: after a two-square advance it must name the square passed over even when no
capture is possible (`Position.fenFields`), which Stockfish, Lichess and python-chess's default
output do not do. -/
def fen (s : String) (h : (parseFEN s).isSome = true := by decide +kernel) : Position :=
  (parseFEN s).get h

/-- Parses the UCI move `s`, such as `e2e4` or `e7e8q`: the move proposed by `readMove`,
provided `s` is exactly that move's UCI writing (`Move.toUCI`); otherwise `none`. So it accepts
exactly the texts `Move.toUCI` writes: two square names, then optionally one of `n b r q`. This
includes moves that are never legal, such as `e2e2`. A pawn move to the last rank must carry its
letter: `e7e8` denotes a move with no promotion choice, which `legalMoves` never lists. Castling is
the king's two-square move (`e1g1`, see `Move`); `e1h1` is accepted and simply never listed.
Whether the move is legal is not checked: that belongs to the claim the move appears in. -/
def parseUCI (s : String) : Option Move :=
  let m := readMove s.toList
  if m.toUCI.toList = s.toList then some m else none

/-- The move with UCI notation `s`, for use in statements: `uci "…"`. The proof that `s`
parses is found automatically when the term is elaborated; a string that does not parse is a
compile-time error. -/
def uci (s : String) (h : (parseUCI s).isSome = true := by decide +kernel) : Move :=
  (parseUCI s).get h

/-! ## Lemmas about notation -/

section Notation

variable {s : String} {p q : Position} {m : Move} {sep : Char} {pc : Piece}

/-! ### Soundness: what an accepted string means -/

/-- Joining `w` and the lists `ws` with the separator `sep` is `w` followed by `sep` and each list
of `ws` in turn. -/
theorem intercalate_singleton_cons {α : Type} (sep : α) (w : List α) (ws : List (List α)) :
    [sep].intercalate (w :: ws) = w ++ ws.flatMap (sep :: ·) := by
  induction ws generalizing w with
  | nil => simp [List.intercalate]
  | cons v vs ih =>
    have := ih v
    simp_all [List.intercalate]

/-- Joining the pieces `splitOn.go` returns, the first one and then each of the rest after a
`sep`, gives the list back. -/
theorem splitOn_go_join (sep : Char) (cs : List Char) :
    (splitOn.go sep cs).1 ++ (splitOn.go sep cs).2.flatMap (sep :: ·) = cs := by
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    simp only [splitOn.go]
    split <;> simp_all

/-- Joining the pieces of `cs` with `sep` gives `cs` back: splitting loses and invents nothing. -/
theorem intercalate_splitOn (sep : Char) (cs : List Char) :
    [sep].intercalate (splitOn sep cs) = cs := by
  rw [splitOn, intercalate_singleton_cons, splitOn_go_join]

/-- If `readFEN` accepts `s` with position `p`, then `s` is a FEN of `p`. -/
theorem readFEN_sound (h : readFEN s = some p) : IsFEN s p := by
  dsimp only [readFEN] at h
  split at h
  · next hg =>
    cases h
    refine ⟨_, hg.2, ?_⟩
    rw [hg.1, List.take_append_drop, intercalate_splitOn]
  · cases h

/-- `parseFEN` accepts `s` with `p` exactly when `readFEN` does and `p` is sane. -/
theorem parseFEN_eq_some_iff : parseFEN s = some p ↔ readFEN s = some p ∧ p.Sane := by
  unfold parseFEN
  cases readFEN s with
  | none => simp
  | some q =>
    by_cases h : q.Sane
    · simp only [h, if_true, Option.some.injEq]
      exact ⟨fun e => e ▸ ⟨rfl, h⟩, fun e => e.1⟩
    · simp only [h, if_false, reduceCtorEq, Option.some.injEq, false_iff]
      exact fun ⟨e, hs⟩ => h (e ▸ hs)

/-- A position `parseFEN` returns is sane. -/
theorem parseFEN_sane (h : parseFEN s = some p) : p.Sane := (parseFEN_eq_some_iff.1 h).2

/-- `parseFEN s` returns `fen s`: it is `some (fen s h)`. -/
theorem parseFEN_fen (h : (parseFEN s).isSome = true) : parseFEN s = some (fen s h) :=
  (Option.some_get h).symm

/-- The position `fen s` is sane. -/
theorem fen_sane (h : (parseFEN s).isSome = true) : (fen s h).Sane :=
  parseFEN_sane (parseFEN_fen h)

/-- `s` is a FEN of the position `fen s`. -/
theorem fen_spec (h : (parseFEN s).isSome = true) : IsFEN s (fen s h) :=
  readFEN_sound (parseFEN_eq_some_iff.1 (parseFEN_fen h)).1

/-- The name of a square is its file letter followed by its rank digit. -/
theorem Square.toList_name (t : Square) : t.name.toList = [t.fileChar, t.rankChar] := by
  revert t; decide +kernel

/-- The UCI text of a move is the source square's name, the destination square's name, and the
promotion letter if there is one. -/
theorem Move.toList_toUCI (m : Move) :
    m.toUCI.toList = m.src.name.toList ++ m.dst.name.toList ++ (m.promo.map PromoKind.letter).toList
    := by
  rcases m with ⟨t, t', _ | pk⟩ <;> simp [Move.toUCI, String.toList_append, Char.toString]

/-- If `parseUCI` accepts `s` with move `m`, then `s` is the UCI writing of `m`. -/
theorem parseUCI_sound (h : parseUCI s = some m) : m.toUCI = s := by
  dsimp only [parseUCI] at h
  split at h
  · next hg =>
    cases h
    exact String.toList_inj.1 hg
  · cases h

/-- `parseUCI s` returns `uci s`: it is `some (uci s h)`. -/
theorem parseUCI_uci (h : (parseUCI s).isSome = true) : parseUCI s = some (uci s h) :=
  (Option.some_get h).symm

/-- The UCI writing of `uci s` is `s`. -/
theorem toUCI_uci (h : (parseUCI s).isSome = true) : (uci s h).toUCI = s :=
  parseUCI_sound (parseUCI_uci h)

/-- Every piece is read back from its letter. -/
theorem Piece.ofLetter?_letter (pc : Piece) : Piece.ofLetter? pc.letter = some pc := by
  revert pc; decide

/-- `emptyCount?` reads no piece letter as a run of empty squares. -/
theorem emptyCount?_letter (pc : Piece) : emptyCount? pc.letter = none := by
  revert pc; decide

/-- For `k` from 1 to 8, the digit `k` is read back as `k` empty squares. -/
theorem emptyCount?_digitChar : ∀ k ∈ List.range' 1 8, emptyCount? k.digitChar = some k := by
  decide

/-! ### Completeness: the writers lose nothing -/

/-- Every character of a row's FEN text has a property `P` that the digits `0` to `8` and every
piece letter have, provided the pending count plus the row's length is at most 8. -/
theorem forall_mem_rowChars (P : Char → Prop) (hd : ∀ k < 9, P k.digitChar)
    (hl : ∀ pc : Piece, P pc.letter) {k : Nat} {row : List (Option Piece)}
    (h : k + row.length ≤ 8) : ∀ ch ∈ rowChars k row, P ch := by
  induction row generalizing k with
  | nil => simp only [rowChars, emptyRun]; split <;> simp [hd k (by simp at h; omega)]
  | cons x row ih =>
    simp only [List.length_cons] at h
    cases x with
    | none => exact ih (by omega)
    | some pc =>
      simp only [rowChars, emptyRun, List.mem_append, List.mem_cons]
      rintro ch (hch | rfl | hch)
      · split at hch
        · simp at hch
        · simp only [List.mem_singleton] at hch; exact hch ▸ hd k (by omega)
      · exact hl pc
      · exact ih (by omega) ch hch

/-- Reading back the text `emptyRun` writes for at most eight empty squares gives those squares. -/
theorem readRow_emptyRun {k : Nat} (h : k ≤ 8) : readRow (emptyRun k) = List.replicate k none := by
  unfold emptyRun
  split
  · simp_all [readRow]
  · have hk : emptyCount? k.digitChar = some k := emptyCount?_digitChar k (by simp; omega)
    simp [readRow, readChar, hk]

/-- Reading back the FEN text of a row, written when `k` empty squares were pending, gives those
`k` empty squares followed by the row, provided `k` plus the number of squares in the row is at
most 8. -/
theorem readRow_rowChars {row : List (Option Piece)} {k : Nat} (h : k + row.length ≤ 8) :
    readRow (rowChars k row) = List.replicate k none ++ row := by
  induction row generalizing k with
  | nil => simpa [rowChars] using readRow_emptyRun (by simpa using h)
  | cons x row ih =>
    simp only [List.length_cons] at h
    cases x with
    | none =>
      rw [rowChars, ih (by omega), List.replicate_succ', List.append_assoc]
      rfl
    | some pc =>
      have hc : readChar pc.letter = [some pc] := by
        simp [readChar, emptyCount?_letter, Piece.ofLetter?_letter]
      rw [rowChars, readRow, List.flatMap_append, List.flatMap_cons, ← readRow, ← readRow,
        readRow_emptyRun (by omega), hc, ih (by omega)]
      simp

/-- `splitOn.go` passes over a list with no `sep` in it, adding it to the first piece. -/
theorem splitOn_go_append {w : List Char} (h : sep ∉ w) (cs : List Char) :
    splitOn.go sep (w ++ cs) = (w ++ (splitOn.go sep cs).1, (splitOn.go sep cs).2) := by
  induction w with
  | nil => rfl
  | cons ch w ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, splitOn.go, ih h.2]
    rw [if_neg (Ne.symm h.1)]

/-- Splitting `w`, then `sep` and each piece of `ws` in turn, gives `w` and `ws` back, provided no
piece contains `sep`. -/
theorem splitOn_go_join_pieces {w : List Char} {ws : List (List Char)} (hw : sep ∉ w)
    (h : ∀ v ∈ ws, sep ∉ v) : splitOn.go sep (w ++ ws.flatMap (sep :: ·)) = (w, ws) := by
  induction ws generalizing w with
  | nil => simpa [splitOn.go] using splitOn_go_append hw []
  | cons v vs ih =>
    have hv : sep ∉ v := h v (List.mem_cons_self ..)
    rw [splitOn_go_append hw, List.flatMap_cons, List.cons_append, splitOn.go,
      ih hv fun u hu => h u (List.mem_cons_of_mem _ hu)]
    simp

/-- Splitting a non-empty list of pieces joined with `sep` gives back the pieces, provided no
piece contains `sep`. -/
theorem splitOn_intercalate {ws : List (List Char)} (hne : ws ≠ []) (h : ∀ w ∈ ws, sep ∉ w) :
    splitOn sep ([sep].intercalate ws) = ws := by
  obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [intercalate_singleton_cons, splitOn,
    splitOn_go_join_pieces (h w (List.mem_cons_self ..))
      fun v hv => h v (List.mem_cons_of_mem _ hv)]

/-- A character of a list joined with `sep` is `sep` or a character of one of the pieces. -/
theorem mem_intercalate {α : Type} {sep x : α} {ws : List (List α)}
    (h : x ∈ [sep].intercalate ws) : x = sep ∨ ∃ w ∈ ws, x ∈ w := by
  cases ws with
  | nil => simp [List.intercalate] at h
  | cons w ws =>
    rw [intercalate_singleton_cons] at h
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons] at h
    rcases h with h | ⟨v, hv, rfl | h⟩
    · exact .inr ⟨w, List.mem_cons_self .., h⟩
    · exact .inl rfl
    · exact .inr ⟨v, List.mem_cons_of_mem _ hv, h⟩

/-- Reading the board field of `b` gives `b` back. -/
theorem readBoard_fenChars (b : Board) : readBoard b.fenChars = b := by
  have hrows : ∀ r, readRow (rowChars 0 (b.row r)) = b.row r := fun r => by
    simpa using readRow_rowChars (k := 0) (row := b.row r) (by simp [Board.row])
  have hsep : ∀ w ∈ (List.finRange 8).reverse.map fun r => rowChars 0 (b.row r), '/' ∉ w := by
    simp only [List.mem_map, List.mem_reverse]
    rintro _ ⟨r, -, rfl⟩ hmem
    exact forall_mem_rowChars (· ≠ '/') (by decide) (by decide) (by simp [Board.row]) _ hmem rfl
  funext t
  rw [readBoard, Board.fenChars, splitOn_intercalate (by simp [List.finRange]) hsep, Board.ofRows,
    List.map_map]
  simp only [Function.comp_def, hrows, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_reverse (by simp; omega : t.rank.rev.val < (List.finRange 8).length)]
  have hr : 7 - (7 - t.rank.val) = t.rank.val := by omega
  simp [Board.row, Fin.rev, hr]

/-- No character of the board field is a space. -/
theorem Board.space_not_mem_fenChars (b : Board) : ' ' ∉ b.fenChars := by
  intro hmem
  rcases mem_intercalate hmem with h | ⟨w, hw, hmem⟩
  · exact absurd h (by decide)
  · simp only [List.mem_map, List.mem_reverse] at hw
    obtain ⟨r, -, rfl⟩ := hw
    exact forall_mem_rowChars (· ≠ ' ') (by decide) (by decide) (by simp [Board.row]) _ hmem rfl

/-- The side to move is read back from its letter. -/
theorem readTurn_fenChar : ∀ c : Color, readTurn [c.fenChar] = c := by decide

/-- Castling rights are read back from their letters. -/
theorem readCastling_letters : ∀ cr : CastlingRights, readCastling cr.letters.toList = cr := by
  decide +kernel

/-- A square is read back from its file letter and rank digit. -/
theorem Square.ofName?_chars : ∀ t : Square, Square.ofName? [t.fileChar, t.rankChar] = some t := by
  decide +kernel

/-- A square is read back from its name. -/
theorem Square.ofName?_name (t : Square) : Square.ofName? t.name.toList = some t := by
  rw [Square.toList_name, Square.ofName?_chars]

/-- The en passant target is read back from its field. -/
theorem Square.ofName?_epChars (e : Option Square) : Square.ofName? (epChars e) = e := by
  cases e with
  | none => decide +kernel
  | some t => exact Square.ofName?_name t

/-- Reading the four FEN fields of `p`, whatever follows them, gives `p` back. -/
theorem readFields_fenFields (p : Position) (cl : List (List Char)) :
    readFields (p.fenFields ++ cl) = p := by
  rcases p with ⟨b, c, cr, e⟩
  show (⟨readBoard b.fenChars, readTurn [c.fenChar], readCastling cr.letters.toList,
    Square.ofName? (epChars e)⟩ : Position) = ⟨b, c, cr, e⟩
  rw [readBoard_fenChars, readTurn_fenChar, readCastling_letters, Square.ofName?_epChars]

/-- Two positions with the same FEN fields are equal: the FEN writing loses no information. -/
theorem Position.fenFields_injective (h : p.fenFields = q.fenFields) : p = q := by
  rw [← readFields_fenFields p [], ← readFields_fenFields q [], h]

/-- No FEN field of a position contains a space. -/
theorem space_not_mem_fenFields (p : Position) : ∀ w ∈ p.fenFields, ' ' ∉ w := by
  have hc : ∀ c : Color, c.fenChar ≠ ' ' := by decide
  have hcr : ∀ cr : CastlingRights, ' ' ∉ cr.letters.toList := by decide +kernel
  have ht : ∀ t : Square, ' ' ∉ [t.fileChar, t.rankChar] := by decide +kernel
  simp only [Position.fenFields, List.mem_cons, List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl)
  · exact p.board.space_not_mem_fenChars
  · simpa using (hc p.turn).symm
  · exact hcr p.castling
  · cases p.epTarget with
    | none => decide
    | some t => rw [epChars, Square.toList_name]; exact ht t

/-- No clock field contains a space. -/
theorem space_not_mem_of_clockFields {cl : List (List Char)} (hcl : ClockFields cl) :
    ∀ w ∈ cl, ' ' ∉ w := by
  intro w hw hmem
  rcases hcl with rfl | ⟨-, hnum⟩
  · simp at hw
  · exact absurd ((hnum w hw).2 ' ' hmem) (by decide)

/-- If `s` is a FEN of `p`, then `readFEN` accepts `s` with `p`: every canonical FEN is
accepted. -/
theorem readFEN_of_isFEN (h : IsFEN s p) : readFEN s = some p := by
  obtain ⟨cl, hcl, hs⟩ := h
  have hsp : ∀ w ∈ p.fenFields ++ cl, ' ' ∉ w := by
    simp only [List.mem_append]
    rintro w (hw | hw)
    · exact space_not_mem_fenFields p w hw
    · exact space_not_mem_of_clockFields hcl w hw
  have h4 : p.fenFields.length = 4 := rfl
  simp only [readFEN, hs, splitOn_intercalate (by simp [Position.fenFields]) hsp,
    readFields_fenFields, List.take_left' h4, List.drop_left' h4]
  simp [hcl]

/-- The text `toFEN` writes is a FEN of the position. -/
theorem Position.isFEN_toFEN (p : Position) : IsFEN p.toFEN p :=
  ⟨[['0'], ['1']], .inr ⟨rfl, by decide⟩, String.toList_ofList⟩

/-- Reading the FEN of any position gives the position back. -/
theorem readFEN_toFEN (p : Position) : readFEN p.toFEN = some p :=
  readFEN_of_isFEN p.isFEN_toFEN

/-- Parsing the FEN of a sane position gives the position back. -/
theorem parseFEN_toFEN (h : p.Sane) : parseFEN p.toFEN = some p :=
  parseFEN_eq_some_iff.2 ⟨readFEN_toFEN p, h⟩

/-- The promotion choice is read back from its letter, or from nothing. -/
theorem readPromo_toList (o : Option PromoKind) :
    readPromo (o.map PromoKind.letter).toList = o := by
  cases o with
  | none => rfl
  | some pk => revert pk; decide

/-- Reading the UCI writing of a move gives the move back. -/
theorem readMove_toUCI (m : Move) : readMove m.toUCI.toList = m := by
  rcases m with ⟨t, t', o⟩
  simp [readMove, Move.toList_toUCI, Square.toList_name, Square.ofName?_chars, readPromo_toList]

/-- Parsing the UCI writing of any move gives the move back. -/
theorem parseUCI_toUCI (m : Move) : parseUCI m.toUCI = some m := by
  simp [parseUCI, readMove_toUCI]

/-- `readFEN` accepts `s` with position `p` exactly when `s` is a FEN of `p`. -/
theorem readFEN_eq_some_iff : readFEN s = some p ↔ IsFEN s p :=
  ⟨readFEN_sound, readFEN_of_isFEN⟩

/-- A string is a FEN of at most one position. -/
theorem IsFEN.unique (hp : IsFEN s p) (hq : IsFEN s q) : p = q :=
  Option.some_inj.1 ((readFEN_of_isFEN hp).symm.trans (readFEN_of_isFEN hq))

/-- `parseUCI` accepts `s` with move `m` exactly when `s` is the UCI writing of `m`. -/
theorem parseUCI_eq_some_iff : parseUCI s = some m ↔ m.toUCI = s :=
  ⟨parseUCI_sound, fun h => h ▸ parseUCI_toUCI m⟩

/-! ### Using `fen` and `uci` in proofs -/

/-- `fen s` is `p` exactly when `p` is sane and `s` is a FEN of `p`. -/
theorem fen_eq_iff (h : (parseFEN s).isSome = true) : fen s h = p ↔ p.Sane ∧ IsFEN s p := by
  rw [← Option.some_inj, ← parseFEN_fen h, parseFEN_eq_some_iff, readFEN_eq_some_iff, and_comm]

/-- Taking `fen` of the FEN of a position gives the position back. -/
theorem fen_toFEN (h : (parseFEN p.toFEN).isSome = true) : fen p.toFEN h = p :=
  (fen_spec h).unique p.isFEN_toFEN

/-- `uci s` is `m` exactly when `s` is the UCI writing of `m`. -/
theorem uci_eq_iff (h : (parseUCI s).isSome = true) : uci s h = m ↔ m.toUCI = s := by
  rw [← Option.some_inj, ← parseUCI_uci h, parseUCI_eq_some_iff]

/-- Taking `uci` of the UCI writing of a move gives the move back. -/
theorem uci_toUCI (h : (parseUCI m.toUCI).isSome = true) : uci m.toUCI h = m :=
  (uci_eq_iff h).2 rfl

end Notation

/-! ## Tests

The tests of this module are in `ChessTest/ChessGame.lean` (`lake build ChessTest`). The checks
below stay here as documentation; they are cheap. -/

-- Writing the initial position, and reading it back from four fields.
#guard Position.initial.toFEN == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#guard readFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -" == some Position.initial
-- Rejected: not canonical FEN (`44`), and not sane (no Black king).
#guard (parseFEN "rnbqkbnr/pppppppp/44/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone
#guard (parseFEN "rnbqqbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").isNone
-- UCI.
#guard parseUCI "e7e8q" == some ⟨⟨4, 6⟩, ⟨4, 7⟩, some .queen⟩  -- e7, e8
#guard (parseUCI "Nf3").isNone

end Chess
