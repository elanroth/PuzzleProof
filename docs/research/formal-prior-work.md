# Formal prior work on chess and two-player games

How earlier formal developments define positions, moves, game trees and outcomes,
which theorems they state, and how they divide trust between proof and computation.
Each section separates **Facts** (what the source says or the code does, checked
against the source) from **Assessment** (my judgment). The lessons are collected in
"Cross-cutting lessons" and "Recommendations for this library" at the end.

Researched 2026-11-01. Code was read from source: the local clones of `Chess.lean` and
`Lean-Hackathon` in `~/chess-lean-research/`, the prototype in `../chess-lean`, and
`coqtbgen`, `coqchess`, `games` and `combinatorial-games` through the GitHub API. Papers
were read as full text where available.

---

## 0. Summary table

| Work | System | Rules covered | Outcome notion | What is proved | Trusted beyond the kernel |
|---|---|---|---|---|---|
| Hurd, endgame DBs | HOL4 + BuDDy | pawnless, no castling | `win1_by`/`win2_by n` sets, plus `win1`/`win2` = ∃n | every 4-piece pawnless DB entry; stability (max DTM); exact DTM bounds | BDD engine (theorems tagged `HOL+BDD`) |
| Marzion, coqtbgen/coqchess | Coq (Rocq) | generic games; chess: pawnless, no castling/e.p. | inductive `win` (in `Type`), coinductive `draw`, `mate p s n` = minimal-depth win | tablebase sound **and** complete for mate-in-n and for draws | OCaml extraction, a postulated finite map |
| Marić, Janičić, Maliković, KRK | Isabelle/HOL + Z3; also C and URSA/SAT | KRK only, on an n×n board | inductive "winning" | a concrete human strategy wins KRK on every n×n board with n ≥ 4 | SMT proof reconstruction (or oracle mode) |
| Nipkow, alpha-beta | Isabelle/HOL (AFP) | abstract game trees | minimax `val` over a bounded linear order or distributive lattice | fail-hard and fail-soft alpha-beta correct relative to `val` | none |
| dwrensha/Chess.lean | Lean 4 + Mathlib | no castling; e.p. yes | inductive `ForcedWin` (no depth) | textbook mates (Morphy mate in 2, Emms puzzles) via custom tactics | kernel `decide`; Stockfish only suggests moves |
| aastha-guptaa/Lean-Hackathon | Lean 4 | castling, e.p., promotion | none (one move line ending in mate) | local lemmas (bishop keeps colour, no friendly capture) | an `#eval` run; the LLM's line is checked, not proved |
| vihdzp/combinatorial-games (formerly Mathlib CGT) | Lean 4 + Mathlib | normal-play games; loopy games | `≤`, `⧏` on `IGame`; `IsWin`/`IsLoss` on `LGame` | Conway theory, nimbers, surreals | none |
| Prototype `chess-lean` (ours) | Lean 4 core | full rules except 50-move and repetition | inductive `WinsIn a n p` | `check_sound`, `not_both`, `onlyMove_sound`; Gotham mate in 11 | `native_decide`, or ~80 s and ~5.7 GB with kernel-only checking |

---

## 1. Joe Hurd: Formal Verification of Chess Endgame Databases (HOL4)

Source: <http://www.gilith.com/papers/chess.pdf> (Oxford Computing Laboratory, c. 2005);
companion pages <http://www.gilith.com/chess/endgames>.

### Facts

**Generic game layer first, chess second.** A two-player game is a 4-tuple
`(L, M_I, M_II, W)`: `L` is a legality predicate on positions, `M_I` and `M_II` are the
move relations of the two players, and `W` is the set of positions won for Player I.
Positions have a type variable `α`. The game is *well-formed* (`two_player G`) when
the move relations and `W` are false on illegal positions.

**Outcomes are depth-indexed sets defined by recursion.**
- `terminal2 G = {p | L p ∧ ∀p'. ¬M_II(p,p')}`: Player II has no move.
- `win2_by G 0 = {p | W p}`.
- `win1_by G n = {p | ∃p'. M_I(p,p') ∧ p' ∈ win2_by G n}`.
- `win2_by G (n+1) = win2_by G n ∪ {p | L p ∧ ∀p'. M_II(p,p') ⇒ p' ∈ win1_by G n} − terminal2 G`.
- `win1 G = {p | ∃n. p ∈ win1_by G n}`, and `win2` likewise.

Two features are deliberate. `win2_by (n+1)` includes `win2_by n` ("within n"), so the
sets are monotone. Subtracting `terminal2` keeps a stalemated defender from counting as
a loss: without it, the vacuous `∀` would make every stalemate a win.

**A chess model meant to be read beside the FIDE articles.**
`position ≡ side × (square → (side × piece) option)` with `square ≡ ℕ × ℕ`. The basic
movement predicates (`rook_attacks`, `knight_attacks` and so on) are written as a
beginner's book would put them: the queen moves like a rook or a bishop, and the knight
moves in an L. A footnote rejects the shorter set-based knight definition because it
"requires a moment's thought to see that it is correct". Line-of-sight is a separate
`clear_line`. Legality is `chess_legal p ≡ all_on_board p ∧ ¬in_check (opponent (to_move p)) p`:
a position is legal when the side that just moved is not in check. The extra
`all_on_board` conjunct exists because `ℕ × ℕ` squares would otherwise allow "chess on
an infinite board". A move is a relation between two *legal* positions, so "you may not
leave your king in check" follows from legality of the target position and is not a
separate rule. Then `checkmated p ≡ game_over p ∧ in_check (to_move p) p` and
`chess_win p ≡ to_move p = Black ∧ checkmated p`. Pawns, castling, en passant and the
draw rules are out of scope: only pawnless positions without castling are handled.

**Specification and encoding are separate types, connected by a theorem.** For BDDs,
a second type `posn ≡ side × ((side × piece) × square) list` gets its own legality,
move and win predicates. A function `abstract : posn → position` lifts it, and the two
versions are proved identical through `abstract` ("a useful check for both versions",
in the paper's words). Positions are grouped into *categories* (side to move plus a
piece list), and each category is encoded as a fixed-length boolean vector.

**Theorem shapes produced.**
- Membership with exact distance to mate:
  `⊢HOL+BDD win2_by chess 15 p ∧ ¬(win2_by chess 14 p)`.
  The negative half is a lower bound on distance to mate.
- Stability, the maximum distance to mate of a category: for every legal KRK position
  with Black to move, `p ∈ win2 chess ⇔ p ∈ win2_by chess 16`.
- A witness that the bound is tight: an explicit position in `win2_by 16` and not in
  `win2_by 15`.
- A hand-proved structural fact: a side with only a king can never win.

**Pitfall the prover caught.** For KQRK with White to move, the BDD iteration
stabilises after 6 moves. Captures, however, drop into KRK, which needs 16 moves. The
stability theorem therefore has to be proved at 16 first and then brought down to 6.
Smaller categories must be solved first.

**Trust split.** Every theorem carries the tag `⊢HOL+BDD`: it depends on HOL4's
kernel plus the results of the BuDDy BDD engine. Scale: all four-piece pawnless
endgames took 18,540 s, 82.7M primitive inferences and 883M BDD nodes. The BDD
variable order changed run time by about 3×.

### Assessment
- This is the best template for faithfulness. Write the specification as a generic game
  plus a chess instance, phrase the chess definitions so a chess player can check them
  against the rules article by article, keep a separate encoding type for computation,
  and connect the two with an `abstract`/refinement theorem.
- Defining legal moves as relations between legal positions is a clean way to state the
  king-safety rule. It is worth copying in the specification layer.
- `win2_by (n+1) ⊇ win2_by n` and the explicit `terminal` subtraction are the two
  details that every later work below either gets right or gets wrong.
- A pitfall in the text: as typeset in Appendix A, `chess_move p p' ≡ chess_legal p ∧
  chess_legal p' ∧ (to_move p' = …) ∧ simple_move p p' ∨ capture_move p p'` parses as
  `(… ∧ simple_move) ∨ capture_move` under the usual precedence. That reading would
  drop the legality and turn conditions on captures. It is almost certainly missing
  parentheses in typesetting, not in the HOL source, but it shows why our English spec
  should be checked against the Lean term (`#print`) and not against a prettified
  rendering.
- Negative facts (`¬ win2_by 14 p`) came for free because the database computes the
  whole set. A certificate checker that only verifies a strategy cannot produce them. We
  need a separate, computable characterisation of `WinsIn` (see Recommendations).

---

## 2. Evan Marzion: coqtbgen, games and coqchess (Coq/Rocq)

Sources: <https://github.com/emarzion/coqtbgen> (generic verified tablebase generator),
<https://github.com/emarzion/games> (game-theory library, a submodule),
<https://github.com/emarzion/coqchess> ("rocq formalization of chess tablebases"),
blog post <https://emarzion.github.io/TB-Generator/>, demo frontend
<https://emarzion.github.io/coqtbgen/>.

### Facts

**Abstract game interface (`games/theory/Game/Game.v`).** A `Record Game` with:
`GameState : Type`; `Move : GameState → Type` (dependent: the moves of a given state);
`to_play`; `exec_move : Move b → GameState`; `atomic_res : GameState → option Result`
where `Result = Win Player | Draw`; `enum_moves b : list (Move b)`; and four proof
fields:
- `enum_all`: every move is enumerated;
- `to_play_exec_move`: turns alternate;
- `atomic_res_nil`: a decided position has no moves;
- `nil_atomic_res`: a position with no moves is decided.

The last field makes stalemate impossible to mishandle: a dead end must have a result.

**Outcomes (`Win.v`, `Draw.v`, `Strategy.v`, `NoWorse.v`).**
- `win p : GameState → Type` is *inductive* with three constructors: `atom_win`
  (atomic result is `Win p`); `eloise_win` (p to play, there is a move to a winning
  state); `abelard_win` (opponent to play, all moves lead to winning states). It lives
  in `Type`, not `Prop`, so a proof of a win *is* a strategy tree. `strategy_of_win`
  extracts it.
- `depth w` is computed from the tree. `minimal w := ∀ w', depth w ≤ depth w'`.
  `mate p s n := {w : win p s & depth w = n ∧ minimal w}` is exact distance to mate.
- `draw` is **coinductive**: either the atomic result is `Draw` (stalemate), or the game
  is ongoing, every move of the player to move leaves the opponent "no worse"
  (coinductive `no_worse`), and some move keeps the draw going. Infinite play is
  therefore a draw.
- `strategy p s` is coinductive. `winning_strategy` is inductive, while
  `no_worse_strategy` and `drawing_strategy` are coinductive. `play_game` runs two
  strategies against each other to a coinductive `outcome` (`W p` or `step …`, with
  `D := step D`).
- Theorems: `unique_winner` (no state is won by both players), `win_not_draw`,
  `both_no_worse_draw`, `mate_eq` (distance to mate is unique).

**Tablebase layer (`coqtbgen/theory/TB/TB.v`).** Extra type classes describe what
retrograde analysis needs: `FinGame` (enumerate all atomic wins, with soundness and
completeness proofs), `NiceGame` (an atomic win for `pl` occurs with the opponent to
move), and `Reversible` (`enum_preds`, with both correctness directions). There is also
an `IntHash` on states and an abstract `IntMap`. The generator iterates "Eloise" and
"Abelard" steps. Validity is a record invariant `TB_valid` preserved by each step, and
termination follows from finiteness. The four headline theorems:
- `TB_final_lookup_mate : tb_lookup TB_final s = Some (pl, n) → mate pl s n`
- `mate_TB_final_lookup : mate pl s n → tb_lookup TB_final s = Some (pl, n)`
- `TB_final_lookup_draw : tb_lookup TB_final s = None → draw s`
- `draw_TB_final_lookup : draw s → tb_lookup TB_final s = None`

`SymTB` and `StratSymTB` are later variants (symmetry-reduced, then stratified by
material) with the same theorem shapes, restricted to states satisfying a predicate `P`.

**Chess instance (`coqchess/theory/Chess/Chess.v`, about 115 KB).**
- `ChessState` is a record that carries its invariants as proof fields: both kings'
  squares, `lookup_white_king`/`lookup_black_king`, `kings_unique`, and
  `opp_to_play_not_in_check`. Ill-formed states cannot be constructed.
- Movement is declarative and stated in `Prop`. `diag_preadj`, `L_preadj` and the other
  pre-adjacencies describe movement on an empty board. `diag_adj` and its relatives add
  "every square strictly between is empty", using `file_sbetween`/`rank_sbetween`.
  `non_pawn_piece_adj` dispatches on the piece.
- `legal st pm` is a `Record` of propositions: the piece is on the origin, the
  destination is open, origin and destination are adjacent for that piece, and no
  resulting check. `RegularMove st := {pm : PreMove & legal st pm}` bundles the proof.
  Equality of moves needs `UIP` (`RegularMove_ext`).
- Execution: `candidate_destinations` per piece, each with `_correct1`/`_correct2`
  lemmas (sound and complete against the `Prop` adjacency), and fast attack tests such
  as `is_threatened_by_knight_iff`. Enumeration has a completeness proof,
  `enum_chess_moves_all`.
- `atomic_chess_res`: no moves and in check gives `Win (opp to_play)`; no moves and not
  in check gives `Draw`.
- Coverage: the piece set has no pawn moves (`non_pawn_piece_adj`), and there is no
  castling or en passant. Material modules exist for KvK and KRvK, with
  `checkmates_correct1/2/3` showing the enumerated mates are sound and complete under
  `KRvK_bound`.

**Trust split.** The Coq kernel checks the generator's correctness proofs. The
tablebase itself is computed by **extracting to OCaml**: `bin/gen`, `uint63.ml` and a
JSON writer. The finite map is axiomatised and implemented by OCaml's `Map`. The blog
says an association-list implementation shows the map axioms are consistent. Trusted
base: Coq's extraction, the OCaml compiler and runtime, the hand-written `uint63.ml`,
and the map axioms. The blog also says the unstratified approach "is probably not
feasible beyond four pieces" and that chess would need stratification, symmetry and
bitboard-style optimisations.

### Assessment
- This is the most complete *semantic* framework in the survey. It has a win/draw
  dichotomy with draws, exact distance to mate, uniqueness theorems, and a tablebase
  proved sound **and complete**. We should copy the shapes of its theorems even though
  we are not building a tablebase generator now.
- `nil_atomic_res`/`atomic_res_nil` are the right way to make terminal positions
  explicit. Our `Outcome`/`terminal` definitions should satisfy the same two laws.
- Wins in `Type` and dependent `Move : GameState → Type` are elegant in Coq, but they
  cost us kernel computation in Lean, and the dependent move types brought `UIP` and
  extensionality bookkeeping. With `decide` as our main engine, a `Prop`-valued
  `WinsIn` plus a separate certificate type (as in the prototype) is the better fit.
  `Move` should stay a plain data type, with legality as a predicate
  (`m ∈ legalMoves p`) and not a subtype.
- Invariants stored as proof fields in `ChessState` give correctness by construction
  but make states hard to write literally and to `decide` on. Hurd's style (plain data
  plus a `Legal` predicate, with moves defined only between legal positions) composes
  better with kernel evaluation.
- A coinductive draw is the honest game-theoretic notion when there is no 50-move or
  repetition rule. A finite certificate form is needed in practice: a set of positions
  closed under the defender's moves (see Recommendations).
- Splitting `candidate_destinations` into `_correct1` (sound) and `_correct2` (complete)
  is exactly the refinement pattern we want between `Spec` and `Impl`.

---

## 3. Marić, Janičić, Maliković: KRK strategy correctness (Isabelle/HOL + SMT)

Sources:
- CADE-25 (2015), "Proving Correctness of a KRK Chess Endgame Strategy by using
  Isabelle/HOL and Z3", LNCS 9195, pp. 256–271,
  <https://doi.org/10.1007/978-3-319-21401-6_17> (record:
  <https://research.matf.bg.ac.rs/handle/123456789/515>).
- Janičić, Marić, Maliković, "Computer-Assisted Proving of Combinatorial Conjectures
  Over Finite Domains: A Case Study of a Chess Conjecture", LMCS 15(1:34) 2019,
  <https://arxiv.org/abs/1801.07528>.
- Earlier work on a related strategy:
  <https://poincare.matf.bg.ac.rs/~janicic/papers/2012-ceciis-chess.pdf>.

### Facts
- The object is a **human-readable strategy**, not a database. A priority list of
  seven rules (ImmediateMate, ReadyToMate, Squeeze, Approach, KeepRoom, RookHome,
  RookSafe) is applied first-match. It is close in spirit to Bratko's strategy, but not
  identical.
- Positions are records: white king, black king, optional rook (`None` once captured),
  side to move. The board size is a parameter. Their legality is deliberately *weaker*
  than FIDE's, so the results transfer to FIDE positions.
- "Winning" is inductive: an immediate mate, or every Black reply leads to a winning
  position. Lemmas have the shape `Pre ⇒ (strategy move; Black reply)* ⇒ Post`, and they
  are chained into the main theorem. On 8×8, White mates within 33 moves (65 plies).
- They used three engines. A C program and an Isabelle-side retrograde analysis check a
  fixed board in seconds. URSA bit-blasts fixed sizes to SAT. For arbitrary n, all
  strategy conditions are linear integer arithmetic, so one Isabelle theorem covers
  every n ≥ 4, with the obligations discharged by Z3. Oracle mode took 136 s; full
  proof reconstruction took 2,202 s.
- The general-n strategy needed an extra rule, RookSafeSmallBoards, because the
  original left some 4×4 and 5×5 positions without a move.
- Lessons the authors state: retrograde analysis "revealed some bugs in the initial
  implementation"; fixing what counterexamples exposed "took majority of our time and
  effort"; "Try to make definitions independent of the problem dimensions"; proof
  assistants have more expressive power than the alternatives, but automation "is far
  from being able to replace mathematician".

### Assessment
- This is a third mode of proof, alongside "database" (Hurd, Marzion) and "certificate"
  (our prototype). Here the *strategy is the program*, and the proof is an invariant
  plus a decreasing measure. It is the only route to statements about *all* positions
  of a material class without enumerating them, and it is the natural shape for
  textbook endgame technique (KQK, KRK, the Lucena position).
- Their main pitfall applies directly to us: specification bugs (a missing rule, an
  under-defined case) were found by fast exhaustive testing *before* proof. We should
  keep a cheap exhaustive or differential check (perft, retrograde counts) beside every
  definition.
- Defining legality more weakly than FIDE so that results transfer is a useful trick:
  prove theorems for a superset of positions when that costs nothing.

---

## 4. Tobias Nipkow: Alpha-Beta Pruning Verified (ITP 2024, Isabelle AFP)

Sources: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.1/LIPIcs.ITP.2024.1.pdf>;
AFP entry <https://isa-afp.org/entries/Alpha_Beta_Pruning.html>;
overview theory <https://devel.isa-afp.org/browser_info/current/AFP/Alpha_Beta_Pruning/Alpha_Beta_Overview.html>.

### Facts
- The model is an abstract finite game tree. Values lie in a **bounded linear order**
  (⊥, ⊤), generalised later to bounded **distributive lattices** and to De Morgan
  algebras for negamax. `val`/`maxmin` is the specification; every search variant is
  called as `f a b t` with window `(a, b)`.
- Correctness is a *relation to the true value within the window*, not equality.
  Knuth–Moore's relation `x ≅ y (a,b)` is
  `(y ≤ a → x ≤ a) ∧ (a < y < b → x = y) ∧ (y ≥ b → x ≥ b)`.
  Fail-hard satisfies `val t ≅ hard a b t (a,b)`, which gives `hard ⊥ ⊤ t = val t`.
- Fishburn's stronger relation `y ≤ x (a,b)` is
  `(y ≤ a → x ≤ y) ∧ (a < y < b → x = y) ∧ (y ≥ b → x ≥ y)`. Fail-soft satisfies it.
  So does fail-hard, which undercuts Fishburn's argument. The precise sense in which
  fail-soft is better: `hard a b t ≤ soft a b t (a,b)`, so it is at least as close to
  `val`. The two variants were also verified to search the same part of the tree.
- Negamax needs only `-(min x y) = max (-x) (-y)` and `-(-x) = x`. Lattice version:
  `y ⊑ x (a,b) ⇔ x ⊓ b ≤ y ≤ x ⊔ a`, and both variants satisfy it.
- `ab_twice_lb`: a cached result can tighten a later window. This is the formal basis
  for transposition-table reuse.
- An extra finding: the program Hughes derived in "Why Functional Programming Matters"
  prunes less than canonical alpha-beta, which a QuickCheck comparison confirmed.

### Assessment
- We do not need to verify a search, because the engine is an untrusted oracle and we
  check certificates. But if we want an "evaluate to depth d" function inside Lean
  (for example a fallback prover for short mates), Nipkow gives the specification to
  aim for: prove `≅`/`⊑` against a declarative `val`, never just "returns the same
  number on tests".
- His values-in-a-lattice view suits outcomes such as
  `Loss < Draw < Win` refined by distance to mate (`WinIn k` better than `WinIn (k+1)`).
  That is the ordered type an "optimal move" theorem quantifies over.
- Negamax is only valid under the two negation laws. If we write a symmetric
  `value : Pos → Outcome` with `negate`, those two laws are the obligations.

---

## 5. dwrensha/Chess.lean (Lean 4)

Source: <https://github.com/dwrensha/Chess.lean> (clone at
`~/chess-lean-research/Chess.lean`, toolchain v4.15.0, uses Mathlib in its tactics),
from <https://github.com/dwrensha/animate-lean-proofs>.

### Facts
- `Position = { squares : List (List (Option (Piece × Side))), turn, en_passant : Option Coords }`.
  `Coords` is `{row col : Nat}`, with (0,0) = a8. A comment explains why `List` and not
  `Array`: in the kernel an `Array` is a wrapper around a `List` and needs well-founded
  recursion, which blocks `decide`.
- There are no castling rights in `Position`. `ChessMove.CastleShort`/`CastleLong` exist
  as syntax but are never generated.
- `valid_moves : Position → List (ChessMove × Position)` produces SAN-like moves paired
  with their result positions. `ambiguate` throws away disambiguation, and its docstring
  admits this "can cause collisions".
- Outcome:
  ```lean
  inductive ForcedWin : Side → Position → Prop where
  | Checkmate (p) : IsCheckmate p → ForcedWin p.turn.other p
  | Self (p m p1) : (m, p1) ∈ valid_moves p → ForcedWin p.turn p1 → ForcedWin p.turn p
  | Opponent (p) : (∀ vm ∈ valid_moves p, ForcedWin p.turn.other vm.snd) → ForcedWin p.turn.other p
    -- FIXME: This is wrong because it considers a stalemate to be a win for the side
    --        who doesn't have the move.
  ```
  There is no depth index, so "mate in n" is not expressible.
- `IsReachable` is defined inductively from `game_start`.
- UX: the board is a Unicode literal with custom syntax and a delaborator (`♔}` marks
  the side to move). Tactics `move "Qb8"`, `opponent_move` and `checkmate` drive
  `ForcedWin` goals by kernel `decide` at each step. `guess_next_move` calls
  `scripts/get_next_move.py` (Stockfish) and inserts a `Try this:` suggestion. The
  engine only *proposes*; the kernel checks.
- Theorems: textbook positions (Morphy's mate in two, smothered mate, en-passant mate,
  several Emms puzzles).

### Assessment
- The `FIXME` is the canonical pitfall: `∀ m ∈ moves, …` is vacuously true when there
  are no moves. Every "for all defender replies" clause must also require that a reply
  exists, or terminal positions must be handled separately (Hurd's `− terminal2`,
  Marzion's `atomic_res = None`, our prototype's `legal p ≠ []`).
- Without a depth index, the library cannot state "mate in n", "fastest mate" or "no
  mate in n−1". Index from the start.
- Using notation as the move identifier (SAN with lossy disambiguation) mixes
  presentation with semantics. Identify a move by its data (from, to, promotion) and
  keep SAN/UCI as a parser that is proved or tested against it.
- The board-literal syntax and the tactic proof style are good for readability, and are
  probably the most "Lean-native" idea here. A small proof-mode front end over our
  certificate checker would be welcome later.
- The `Array`-vs-`List` kernel note is still relevant: specification definitions must
  reduce structurally if we want `decide` on them.

---

## 6. aastha-guptaa/Lean-Hackathon (Lean 4)

Source: <https://github.com/aastha-guptaa/Lean-Hackathon> (clone at
`~/chess-lean-research/Lean-Hackathon`, toolchain v4.30.0-rc2, no Mathlib). Built at the
IISc "LeanLang for Verified Autonomy" hackathon, April 2026.

### Facts
- `Board := Vector (Vector (Option ColourPiece) 8) 8`, `Pos := {row col : Fin 8}`.
  `GameState` holds castling rights, an en-passant *file*, `moveNum`, a `history`, and an
  in-band `valid : Bool` flag.
- Legality is checked per piece by geometry (`isValidRookMove`, `isPathClear` with a
  fuel-bounded loop), then king safety after the move, then castling transit squares.
- The pipeline: an LLM (OpenAI API through `script.py`) proposes a *single move line*.
  `Main.lean` replays it with `GameState.isValidMoves` and tests `isAnyCheckmate` on the
  final state. This is an `#eval`/executable check, not a theorem, and it does not
  quantify over defender replies. It verifies "a mating line exists", not "mate is
  forced".
- Theorems (`Proofs.lean`, `LegalProofs.lean`): `bishop_stays_on_colour`,
  `no_friendly_fire`, frame lemmas such as `makeMove_*_of_pseudoLegal`, and unfoldings
  such as `isCheckmate_implies_noLegalMoves`.
- **Two parallel legality definitions.** `Chess/Model.lean` defines `isInCheck`,
  `isLegalMoveInternal`, `GameState.isLegalMove` and `GameState.isCheckmate` in the root
  namespace. `Chess/Legal.lean` defines `Chess.isInCheck`, `Chess.isLegalMove` and
  `Chess.isCheckmate`. `LegalProofs.lean` proves facts about the `Chess.*` versions,
  while `Main` runs the `GameState.*` versions.
- **A likely soundness bug in the mate test.** `hasAnyLegalMove` enumerates from/to
  pairs through `mkMoveFromBoard?`, which always sets `promotion := none`.
  `isValidPawnMove` rejects a move to the last rank with `promotion = none`. So a
  position whose only legal moves are promotions is reported as having no legal move.
  If that side is in check, this gives a false "checkmate". I found this by reading the
  code and did not run it.

### Assessment
- This is a cautionary example. It shows four failure modes in one place:
  1. Checking a line instead of a strategy.
  2. Proofs about a definition that the pipeline does not run.
  3. Several hand-written move enumerations that drift apart.
  4. In-band error flags (`valid : Bool`) instead of `Option`/`Except` or a predicate.
- Its "sanity theorems" (bishop parity, no friendly capture) are a good *genre*,
  though. Cheap theorems like these check that the specification says what we think.
  We should have a file of them.

---

## 7. Combinatorial game theory in Lean: Mathlib `SetTheory.PGame`, now vihdzp/combinatorial-games

Sources: <https://github.com/vihdzp/combinatorial-games>,
<https://reservoir.lean-lang.org/@vihdzp/CombinatorialGames>. The deprecated CGT was
removed from Mathlib by "chore: remove deprecated material from CGT" (#35550,
2026-02-20). `Mathlib/SetTheory/` no longer has a `Game` directory.

### Facts
- Conway games are the main object: `IGame` is built from two `Small` sets of options
  (`!{s | t}`), and its quotient `Game` is an ordered abelian group. The ordering
  encodes outcomes under **normal play** (the last player to move wins): `0 < x` means
  Left wins, `0 ≤ x` means Left wins going second, and `x ⧏ y` abbreviates `¬ y ≤ x`.
  The docstring notes that the theory is developed "without the concept of a strategy":
  the strategy is implicit in `≤`.
- The project explicitly excludes chess, because it "can end in a tie".
- *Loopy* games (`LGame`, `Game/Loopy/Outcome.lean`) define a mutual inductive pair:
  ```lean
  inductive IsWin  : Player → LGame → Prop | intro : y ∈ x.moves p → IsLoss (-p) y → IsWin p x
  inductive IsLoss : Player → LGame → Prop | intro : (∀ y ∈ x.moves p, IsWin (-p) y) → IsLoss p x
  ```
  A draw is then "neither", with surviving strategies developed from there.
  `isWin_iff_exists`, `isLoss_iff_forall`, `not_isWin_iff_forall` and
  `not_isLoss_iff_exists` are the basic API.
- Related Lean work: Borel determinacy (Manthe, <https://arxiv.org/abs/2502.03432>),
  whose closed-game case is Zermelo's argument; and `elazarg/GameTheory`
  (<https://reservoir.lean-lang.org/@elazarg/GameTheory>), with backward induction for
  finite perfect-information games. Both depend on Mathlib.

### Assessment
- Normal-play CGT is the wrong semantics for chess: the player left without a move is
  not simply the loser, because stalemate is a draw, and there are draws and sums we do
  not need. We should not depend on it, and we cannot, since we use no Mathlib.
- The `IsWin`/`IsLoss` mutual-inductive pair, with names relative to the player to
  move, is the cleanest notation in the survey. A side-relative
  "the player to move wins/loses" API has half the case splits of a White/Black-indexed
  one and gives negamax-style symmetry for free. It is worth mirroring in naming
  (`WinsIn`/`LosesIn`), adapted to chess terminal positions: checkmate is a loss for
  the player to move, stalemate is neither.

---

## 8. Our prototype: `chess-lean` (Lean 4, core only)

Source: `/Users/elanroth/ACM/.claude/worktrees/chess-lean-proofs-f678ef/chess-lean`.

### Facts
- The board is a single `Nat` of 64 nibbles (codes 0, 1–6, 9–14). Castling rights are a
  4-bit `Nat`, the e.p. square is a `Nat` with 64 meaning none, and
  `Move = {src dst promo : Nat}`. Movement uses biased direction offsets (`shift s df dr`
  with +2 bias), `rayHit`, `attacked`, `pseudo`, `play`, and
  `legal = pseudo.filter (kingSafe ∘ play)`. The move generator matches python-chess
  perft counts on the chessprogramming suite (<https://www.chessprogramming.org/Perft>).
  It is not proved against any declarative rule set. The 50-move and repetition rules
  are not modelled.
- Semantics:
  ```lean
  inductive WinsIn (a : Side) : Nat → Pos → Prop
  | mate : p.turn = a.other → mated p → WinsIn a n p
  | att (m) : p.turn = a → m ∈ legal p → WinsIn a n (play p m) → WinsIn a (n+1) p
  | dfd : p.turn = a.other → legal p ≠ [] → (∀ m ∈ legal p, WinsIn a n (play p m)) → WinsIn a n p
  ```
  `mate` at any `n` makes "within n" monotone. `dfd` requires `legal p ≠ []`, so
  stalemate is not a win.
- `Cert` (mate / att move / dfd replies) is generated by Stockfish plus python-chess.
  `check fuel a n p c : Bool` uses fuel to stay structural. Proved theorems:
  `check_sound`, `not_both` (no position is a forced win for both sides), and
  `onlyMove_sound`, which says `best` wins and every other legal move hands the
  opponent a forced win, hence `Wins p.turn (play p m) ↔ m = best`.
- Trust: `native_decide` in `Gotham.lean`/`Line.lean`. `GothamKernel.lean` is a
  generated, kernel-only version with 320 per-node theorems (about 80 s, about 5.7 GB
  RSS per `scratch/kernel.log`). `scratch/Neg.lean` holds negative tests: a budget one
  too small fails, a dropped refutation fails, a wrong best move fails, and stalemate is
  not mate.
- Recorded limitation (`Line.lean`): only-move theorems are impossible at plies where
  some alternative is a *draw* or an unforced advantage, because "no mate tree can
  refute" a drawing alternative.

### Assessment
- What to keep: the `WinsIn` shape (Hurd-equivalent and stalemate-safe), the
  certificate-plus-checker architecture with a soundness theorem, `not_both` as the
  bridge from "wins" to "optimal", negative tests, and the `native_decide` /
  kernel-only split.
- What to change:
  1. **The specification is the implementation.** The nibble encoding, biased offsets
     and magic numbers (`rightsMask` 12/13/14/3/7/11) *are* the definition of chess, so
     faithfulness rests on perft alone. Hurd and coqchess both show the remedy: a
     declarative specification with a refinement theorem.
  2. **Junk values.** Any `Nat` is a "board", including codes 7, 8 and 15. `findKing`
     returns 64 when there is no king. `promo` is any `Nat`. Typed `Square := Fin 64`,
     `Piece`/`Color` inductives and an `Option Piece` promotion remove whole classes of
     theorems that would otherwise need hypotheses.
  3. **Only mate-shaped refutations.** We need a certificate for "this alternative does
     not win", meaning a draw or at least no forced win. That is the dual (Marzion's
     coinductive draw), represented finitely.
  4. **Position identity.** `ep` is set after every double push, even when no capture
     is possible, so FEN-equal positions can differ. This matters as soon as
     transpositions, repetition or tablebase lookup appear.
  5. **No negative distance-to-mate facts.** `WinsIn a n p` can be certified, but
     `¬ WinsIn a (n-1) p` (Hurd's lower bound, needed for "fastest mate") cannot. That
     needs a decidable characterisation.

---

## 9. Other items found

- Maliković and Čubrilo, "What Were the Last Moves?", a formal system for retrograde
  chess problems in Coq (<https://www.bib.irb.hr/445958>). It concerns reachability and
  retro-analysis, not move generation. It is relevant if we ever state `IsReachable`
  theorems (dwrensha has the definition).
- I found no formally verified full-rules chess move generator in any proof assistant.
  The engine community's standard check is perft
  (<https://www.chessprogramming.org/Perft>). A refinement proof of a complete move
  generator, pawns and castling included, against a declarative specification would
  therefore be new.

---

## 10. Cross-cutting lessons

**L1. Separate the game from chess.** Hurd's `(L, M_I, M_II, W)` and Marzion's
`Game` record both prove the outcome theory once, abstractly. Every theorem in it
(`not_both`/`unique_winner`, monotonicity, `win_not_draw`, `mate_eq`) is independent of
the chess rules and much easier to prove at that level.

**L2. Terminal positions must be explicit.** Every working semantics guards the
defender's `∀` with "there is a move" or with an explicit terminal result. The one that
does not (dwrensha's) is wrong and says so in a comment.

**L3. Index by depth, and include "within".** `WinsIn n` with `n ≤ n' → WinsIn n →
WinsIn n'` gives "mate in n", exact distance to mate (`WinsIn n ∧ ¬WinsIn (n-1)`),
Marzion's `minimal`, and stability bounds. An unindexed `ForcedWin` cannot express them.

**L4. Specification and implementation are different types joined by a theorem.**
Hurd has `abstract : posn → position` with predicate equivalence. coqchess has `Prop`
adjacency plus `candidate_destinations_correct1/2`. Lean-Hackathon shows what happens
without this: proofs about one definition while another one runs.

**L5. Trust is always split, so label it.** Hurd tags theorems `⊢HOL+BDD`. Marzion
trusts extraction and a map axiom. KRK distinguishes SMT oracle mode from
reconstruction mode. Our prototype has `native_decide` versus kernel-only. In Lean the
label is `#print axioms` (`Lean.ofReduceBool` appears exactly when `native_decide` was
used). It should be checked in CI for every headline theorem.

**L6. Positive facts need strategies; negative facts need search or closed sets.**
"Wins" is witnessed by a tree. "Does not win within n" needs exhaustive bounded search
(Hurd's sets, or a verified Boolean `winsInB` with `winsInB_iff`). "Draw" or "never
loses" needs a coinductive object or its finite form: a set of positions closed under
the right moves. Only-move and optimality theorems need *both* kinds.

**L7. Order of solving matters when material changes.** Hurd's KQRK result had to be
iterated to the depth of the KRK sub-endgame first. Any distance-to-mate claim
involving captures or promotions depends on the sub-endgames' bounds.

**L8. Test the specification cheaply and early.** KRK's bugs came out of retrograde
analysis, our prototype's out of perft, and Hurd's out of comparing two encodings.
Sanity theorems such as "a bishop never changes colour" or "a bare king cannot win" are
cheap ways to catch a specification that says the wrong thing.

**L9. Kernel computability shapes the data types.** Structural recursion, `List`/`Nat`/
`Fin` over `Array` and well-founded recursion, no proof fields inside states that the
kernel must compare, and `Decidable` instances that reduce. dwrensha's `Array` note and
our prototype's 5.7 GB kernel run are both data points.

**L10. Readable front ends help.** dwrensha's board literals, delaborator and `move`
tactic make a proof look like a game score. The oracle-suggests, kernel-checks pattern
(`guess_next_move` with `Try this`) is the right UX for Stockfish.

---

## Recommendations for this library

These are judgments, ordered roughly by when they bite.

1. **Layer the library as Hurd and Marzion did, keeping each layer small.**
   - `Chess.Game` (or `Chess.Outcome`): an abstract finite-branching two-player game
     with `toMove`, `moves : State → List Move`, `play`, and `terminal : State → Option
     Result`. It has Marzion's two laws: terminal ⇔ no moves.
   - `Chess.Spec.*`: declarative rules. Squares are `Fin 8 × Fin 8` or `Fin 64`, pieces
     and colours are inductives, the board is `Square → Option (Color × Piece)`
     (Hurd's representation). Movement is defined geometrically (`SameDiagonal`,
     `Between`, `ClearPath`), with one definition per FIDE article, phrased as a chess
     book would phrase it. Legal positions are a predicate. Following Hurd, a legal move
     is a pseudo-move whose result is a legal position.
   - `Chess.Impl.*`: the executable generator (mailbox first; bitboards later if
     needed), with a refinement theorem `m ∈ Impl.legalMoves p ↔ Spec.LegalMove p m` and
     `Impl.play` agreeing with `Spec.play`, proved per piece as `_sound`/`_complete`
     pairs, as coqchess does. Until it is proved, the theorem is a named `sorry`-free
     *conjecture* tracked in `docs/THEOREMS.md`, backed by perft differential tests.

2. **Plain data plus predicates, not subtypes with proof fields.** `Position` is a
   structure of data (board, side to move, castling rights as four `Bool`s, `Option`
   e.p. file, clocks if modelled). `Position.WellFormed` (exactly one king per side, no
   pawns on the back ranks, rights consistent with the board) and `Position.Legal`
   (side not to move is not in check) are separate `Prop`s, with
   `play_preserves_wellFormed` as a theorem. States stay `decide`-friendly and
   `DecidableEq` stays structural. Normalise e.p. so that it is only recorded when a
   capture is pseudo-legally possible, or define position equality modulo e.p. (L4,
   prototype item 4).

3. **Moves are data, notation is a parser.** `Move := {from to : Square, promo : Option
   PromotionPiece}`. Castling is a king move of two files and en passant a pawn
   capture, interpreted by `play`. UCI and SAN parsing live in their own module, with
   round-trip tests. Never identify moves by SAN (dwrensha pitfall).

4. **One semantic core, stated side-relatively, with depth.** Keep the prototype's
   `WinsIn a n p`, or the side-relative pair `WinsIn n p` / `LosesIn n p` ("the player
   to move wins/loses within n"), patterned on CGT's `IsWin`/`IsLoss`. Prove once, in
   the abstract layer:
   - `WinsIn.mono : n ≤ n' → WinsIn n p → WinsIn n' p`
   - `not_both` (Marzion's `unique_winner`)
   - an exact distance-to-mate predicate `MateIn n p := WinsIn n p ∧ ∀ k < n, ¬WinsIn k p`
     with uniqueness (Marzion's `mate_eq`)
   - **a decidability bridge** `winsInB n p = true ↔ WinsIn n p` for a structurally
     recursive bounded search. This gives Hurd-style negative facts
     (`¬WinsIn (n-1) p`), so "mate in exactly n" and "fastest mate" become checkable.

5. **Add a finite draw certificate.** This is the dual the prototype lacked. A
   *fortress certificate* for side `a` at `p` is a finite list `S` of positions with
   `p ∈ S` such that, for every `q ∈ S`:
   - `q` is not checkmate against the defender;
   - if the defender is to move, some legal move stays in `S` or reaches stalemate;
   - if the attacker is to move, every legal move stays in `S` or reaches a
     stalemate/dead position.

   The checker is a `Bool`. The soundness theorem is `∀ n, ¬WinsIn a n p`, proved by
   induction on the `WinsIn` derivation, generalising over `q ∈ S`. Induction on `n`
   does not work, because the prototype's `dfd` constructor does not decrease `n`. This
   is a finite version of Marzion's coinductive `draw`/`no_worse`. With
   `not_both`, this upgrades `onlyMove` to *optimal-move* theorems where alternatives
   only draw: the best move wins, and every other move gets either a winning
   refutation or a fortress.

6. **Optimality as an order on outcomes (Nipkow's view).** Define `Outcome :=
   loss k | draw | win k`, ordered with faster wins and slower losses better, plus
   `negate` satisfying `-(-x) = x` and `-(min x y) = max (-x) (-y)`. State the
   long-term goal as a theorem schema, `IsOptimal p m := ∀ m' ∈ legal p, value (play p
   m') ≤ value (play p m)`, and prove the parts we can: win versus not-win now, exact
   distance to mate via (4), and draws via (5). Evaluations from Stockfish never appear
   in statements, only in certificate generation.

7. **The 50-move and repetition rules: decide explicitly and record it in
   `docs/THEOREMS.md`.** Every prior work omits them (Marzion treats infinite play as a
   draw). My suggestion: make the primary game history-free, as the prototype and Hurd
   do, and add a bridging theorem later. A depth-minimal winning strategy never repeats
   a position along a line. If it did, the later occurrence would have the same
   distance to mate with less budget left, which is a contradiction. So threefold
   repetition after the root cannot rescue the defender, and a halfmove clock
   `h + 2n < 100` makes the 50-move rule irrelevant. Pre-root history needs a stated
   assumption. This argument is my own and needs checking in Lean.

8. **Trust policy, enforced mechanically.**
   - Headline theorems come in a kernel-only version (`decide +kernel` or structural
     `rfl`), and a `#print axioms` check in a test file fails if `Lean.ofReduceBool`
     appears where it should not.
   - `native_decide` is allowed only in theorems whose names or namespaces say so
     (`…_native`), following the prototype's split.
   - Stockfish and python-chess are certificate generators only. Their output is data
     checked by a proved-sound checker (L5, L10).

9. **A specification sanity file from day one** (`Chess/Spec/Sanity.lean`). Short
   theorems that test that the English specification became the right Lean:
   - bishops keep square colour;
   - knight moves are symmetric;
   - after a legal move, the mover is not in check and the kings are not adjacent;
   - material never increases except by promotion;
   - a bare king never wins (Hurd);
   - stalemate is not mate;
   - the initial position has 20 legal moves.

   Plus perft differential tests against python-chess for the implementation (L8).

10. **Plan, but do not build yet, the third proof mode: verified strategies.** For
    textbook endgames (KQK, KRK), the KRK work shows that a short rule-based strategy
    plus an invariant and a decreasing measure proves a theorem about *every* position
    of a material class. That is more elegant than any table. Keep `Spec` definitions
    independent of fixed coordinates where it costs nothing ("make definitions
    independent of the problem dimensions"), so that such proofs stay possible.

11. **Ergonomics later, modelled on dwrensha.** A board literal or `fen!"…"` elaborator,
    a delaborator, and a small tactic mode (`attack "Qh8+"`, `defend_all`, `mate`) over
    the same `WinsIn` constructors, with a `stockfish_suggest` tactic that only emits
    `Try this:`.

---

## Sources

- J. Hurd, *Formal Verification of Chess Endgame Databases*: <http://www.gilith.com/papers/chess.pdf>; <http://www.gilith.com/chess/endgames>
- E. Marzion, coqtbgen: <https://github.com/emarzion/coqtbgen>; games: <https://github.com/emarzion/games>; coqchess: <https://github.com/emarzion/coqchess>; blog: <https://emarzion.github.io/TB-Generator/>; frontend: <https://emarzion.github.io/coqtbgen/>
- F. Marić, P. Janičić, M. Maliković, CADE-25 (2015): <https://doi.org/10.1007/978-3-319-21401-6_17>, <https://research.matf.bg.ac.rs/handle/123456789/515>
- P. Janičić, F. Marić, M. Maliković, LMCS 15(1:34) 2019: <https://arxiv.org/abs/1801.07528>
- Janičić et al. 2012 (CECIIS): <https://poincare.matf.bg.ac.rs/~janicic/papers/2012-ceciis-chess.pdf>
- T. Nipkow, *Alpha-Beta Pruning Verified*, ITP 2024: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.1/LIPIcs.ITP.2024.1.pdf>; AFP: <https://isa-afp.org/entries/Alpha_Beta_Pruning.html>; <https://devel.isa-afp.org/browser_info/current/AFP/Alpha_Beta_Pruning/Alpha_Beta_Overview.html>
- D. Renshaw, Chess.lean: <https://github.com/dwrensha/Chess.lean>; <https://github.com/dwrensha/animate-lean-proofs>
- Lean-Hackathon: <https://github.com/aastha-guptaa/Lean-Hackathon>
- Combinatorial games in Lean: <https://github.com/vihdzp/combinatorial-games>; <https://reservoir.lean-lang.org/@vihdzp/CombinatorialGames>; Mathlib PR #35550: <https://github.com/leanprover-community/mathlib4/pull/35550>
- S. Manthe, Borel determinacy in Lean: <https://arxiv.org/abs/2502.03432>
- elazarg/GameTheory: <https://reservoir.lean-lang.org/@elazarg/GameTheory>
- Maliković and Čubrilo, *What Were the Last Moves?*: <https://www.bib.irb.hr/445958>
- Perft: <https://www.chessprogramming.org/Perft>
- Prototype: `/Users/elanroth/ACM/.claude/worktrees/chess-lean-proofs-f678ef/chess-lean`
