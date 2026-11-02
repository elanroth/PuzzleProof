# Theorem landscape: what is worth proving about chess, and how to phrase it

Researcher role: theorem landscape. Date: 2026-11-01.

This note surveys which theorems about chess are meaningful and provable in Lean 4 (core + Std,
no Mathlib), from single-move rules up to "this move is optimal". For each family it gives:
the English statement, a Lean *shape* (a sketch, not compiled code), a difficulty rating, what
it depends on, and the places where English and Lean most easily drift apart.

Conventions used throughout:

- **Fact** marks something established by a cited source (or by reading the prototype at
  `prototype/`). **Judgment** marks this researcher's assessment. Lean sketches are
  judgments about good shapes, not code that has been compiled.
- Difficulty scale (judgment):
  - **D0**: closed by computation on concrete data (`decide`, `decide +kernel`, `native_decide`).
  - **D1**: routine induction or case analysis once the definitions are right (tens of lines).
  - **D2**: needs a planned lemma library or proof architecture (hundreds to low thousands of lines).
  - **D3**: research-level, or computationally out of reach in Lean today.
- "Mover" means the side to move in the position under discussion; "attacker" and "defender"
  are the two roles in a forced-win statement.

---

## 1. Prior art (facts)

| Work | System | What was proved | Relevance |
|---|---|---|---|
| Hurd, *Formal Verification of Chess Endgame Databases* (TPHOLs 2005) | HOL4 + BuDDy BDDs | Endgame databases for all pawnless endgames with at most four pieces, as theorems that "logically follow from the laws of chess"; trust base is HOL4's inference rules plus the BDD engine. | The only prior work that ties *exact game values* to a formal rule set. Shows tablebase verification is feasible for tiny material and that the rules must be formalized first. |
| Maric, Janicic, Malikovic, *Computer-Assisted Proving of Combinatorial Conjectures Over Finite Domains: A Case Study of a Chess Conjecture* (LMCS 2019) | Isabelle/HOL (+ Z3 in the CADE 2015 version) | A winning strategy for White in KRK on an n x n board; KRK-specific definitions were proved "in accordance with the general chess rules". | Shows the value of a *declarative* rule layer that specialized definitions are proved against; reports that exhaustive retrograde analysis does not scale to large boards. |
| Malikovic and Cubrilo, Coq retrograde / shortest-proof-game systems (CECIIS 2008, 2010) | Coq | Formal systems for reasoning about retrograde problems and searching for shortest proof games via piece trajectories. | Prior art for reachability and proof games in a proof assistant. |
| dwrensha, `Chess.lean` | Lean 4 | An "(incomplete) implementation of chess"; `ForcedWin .white` stated for a mate-in-two (`morphy_mates_in_two`) proved with tactics `move`, `opponent_move`, `checkmate`; optional Stockfish hint tactic. | The closest Lean 4 prior art. Tactic-driven, interactive proofs; complements our certificate approach. |
| *Lean Across the Board* | Lean (3-era docs) | Chessboard puzzles from the book *Across the Board* (piece placement, Guarini). | Combinatorics on boards, not game rules. |
| Mathlib `SetTheory.Game.PGame`; vihdzp `CombinatorialGames` | Lean | Conway's combinatorial game theory (normal play, no draws). | Not a fit: chess is not normal-play (it has draws and a terminal win condition), and Mathlib is out of scope here. |
| Ambrona, *A Practical Algorithm for Chess Unwinnability* (FUN 2022) | Java (CHA) | Claims a sound, complete and practically efficient algorithm for unwinnability; ran over the whole Lichess database (3+ billion games). | Defines the target for "dead position" theorems; an untrusted oracle we could certify against. |
| Prototype `prototype/` (this repo) | Lean 4.28 | `WinsIn` semantics; `Cert` checker with `check_sound`; `not_both`; `onlyMove_sound`; a mate in 11 and an only-move theorem, both via `native_decide` and kernel-only (~80 s, ~6 GB, 320 generated per-node theorems); perft matching python-chess on the standard suite. | Our starting point. Its README states the move generator is *not* proved against a declarative rule set and the 50-move and repetition rules are not modelled. |

Fact (search result): no formally verified chess *move generator* in Lean, Coq, Dafny or Agda
turned up in searches; published verification work is endgame- or retrograde-focused.

Rule-text facts used below, from the FIDE Laws of Chess (handbook chapter E012023):

- 3.9.1: a king is in check when attacked by an opposing piece, *even if that piece could not
  legally move* (pins do not prevent giving check).
- 3.10.1-3.10.3: a move is legal if it satisfies Articles 3.1-3.9; **a position is illegal if
  no series of legal moves could have produced it.**
- 5.1.1 checkmate; 5.2.1 stalemate; 5.2.2 dead position (no series of legal moves leads to mate
  for either side): each ends the game immediately.
- 9.2.3: "same position" means same side to move, same pieces on same squares, *and the same
  possible moves*; en passant and castling rights can make otherwise identical boards differ.
- 9.3: the 50-move rule is a *claim*. 9.6.1 / 9.6.2: fivefold repetition and the 75-move rule
  are *automatic*, and a mate on the 75th move takes precedence.

---

## 2. The definitional layer every theorem depends on

Judgment: almost every theorem below is easy *or* impossible depending on choices made here.
The list is short on purpose.

1. **`Position`**: board, side to move, castling rights, en passant target, halfmove clock.
   (The fullmove number is display-only; no theorem needs it.)
2. **`WellFormed p`**: the static sanity predicate (exactly one king per side, no pawns on
   ranks 1/8, castling rights consistent with king/rook placement, en passant target consistent
   with a just-made double push, side not to move not in check, clock <= 150).
3. **`Attacks p s t`**: the piece on `s` attacks `t` *geometrically*, ignoring pins (FIDE 3.9.1).
4. **`Legal p m : Prop`**: declarative legality, written to read like Article 3:
   `PseudoLegal p m` (geometry, occupancy, special-move preconditions including castling's
   "king not in check / does not cross an attacked square") **and** "after `p.play m`, the
   mover's king is not attacked".
5. **`play p m : Position`**: the effect of a move. Total, but only specified on legal moves.
6. **`legalMoves p : List Move`**: the executable generator, proved against `Legal`.
7. **Game layer** (separate from the move layer): `GameState` = position + history (for
   repetition), and the result rules of Articles 5 and 9.

Judgment: keep (1)-(6), the *move rules* (FIDE Art. 3), strictly separate from (7), the
*result rules* (Art. 5, 9). Perft, move generation and most invariants live entirely in the
move layer; termination, repetition and "optimal" live in the game layer. The prototype mixes
them only by omission (no clock, no history), which is why its README has to disclaim the
50-move and repetition rules.

Lesson from the prototype (fact, from `Basic.lean`): `findKing` returns 64 when there is no
king, so `inCheck` is `false` and `kingSafe` is `false` on a kingless board; such a position
silently has no legal moves and is "stalemate". Judgment: partial behaviour like this is fine in
an executable layer, but every spec-level theorem must carry a `WellFormed` hypothesis, or the
representation must make the bad state unrepresentable (e.g. store the two king squares as
fields). Storing king squares as fields makes "exactly one king per side" true by construction
and makes `kingSquare` total, at the cost of a check in the FEN parser.

---

## 3. Theorem catalogue

### 3.1 Rule-level lemmas (geometry and symmetry)

| Theorem (English) | Lean shape | Difficulty | Depends on |
|---|---|---|---|
| Attack symmetry: a non-pawn piece of kind k on s attacks t iff a piece of kind k on t would attack s (same occupancy). For pawns, a white pawn on s attacks t iff a black pawn on t attacks s. | `attacksFrom k occ s t ↔ attacksFrom k occ t s` | D1 | squares, rays |
| Colour-flip symmetry: mirroring the board top-to-bottom and swapping colours maps legal moves to legal moves. | `Legal p m ↔ Legal p.flip m.flip`, hence `perft p.flip n = perft p n` | D1-D2 | `Legal`, `play` commute with `flip` |
| A bishop move preserves square colour. | `PseudoLegal p m → p.pieceAt m.src = bishop → color m.src = color m.dst` | D1 | square arithmetic |
| A knight move always changes square colour. | similar | D1 | |

Fact: the Chess Programming Wiki lists a mirrored Position 4 that gives the same perft counts as
the original, which is exactly the colour-flip theorem applied to perft.

Judgment: attack symmetry is the lemma that makes check detection cheap ("put a super-piece on
the king square") and it is also what lets a fast `inCheck` be proved equal to the declarative
"some enemy piece attacks the king". It deserves to be proved early. Colour-flip symmetry halves
testing and many case analyses (white-pawn and black-pawn lemmas become one).

Phrasing hazard: "left-right mirroring" is a symmetry only without castling rights (the king
starts on the e-file). State it with a hypothesis `p.castling = none`, or not at all.

### 3.2 Invariants of reachable positions

Define reachability once, from FIDE 3.10.3:

```lean
inductive Reachable : Position → Prop where
  | start : Reachable Position.initial
  | step  : Reachable p → Legal p m → Reachable (p.play m)
```

Judgment: prove each invariant as **preservation over well-formed positions**, not only over
reachable ones:

```lean
theorem WellFormed.play (h : WellFormed p) (hm : Legal p m) : WellFormed (p.play m)
theorem Reachable.wellFormed : Reachable p → WellFormed p   -- one-line corollary
```

because positions loaded from FEN are not known to be reachable, but can be checked well formed
by `decide`. Reachability is then a corollary, not the foundation.

| Invariant (English) | Precise phrasing | Difficulty | Notes |
|---|---|---|---|
| Exactly one king per side. | `(p.squaresWith (c, king)).length = 1` for both colours | D1 (D0 if king squares are fields) | Kings are never captured because a legal move never leaves one's own king attacked, and the opponent's king is never on a capturable square in a well-formed position. |
| The side *not* to move is not in check. | `¬ p.inCheck p.turn.other` | D1 | This is the real content of "legal": it is preserved because the mover's own king is safe after the move. It is also the hypothesis that makes "king capture" impossible. |
| Kings are never adjacent. | `kingDist ≥ 2` | D1 | Follows from the previous invariant. |
| No pawn on rank 1 or rank 8. | `∀ s, p.pieceAt s = some (c, pawn) → s.rank ∉ {0, 7}` | D1 | Promotion is mandatory (FIDE 3.7.3.3); en passant and pushes never reach rank 1 for White. |
| The number of men never increases. | `(p.play m).men ≤ p.men`, strict iff capture | D1 | Promotion replaces one man with one man. This is the clean form of "piece counts only decrease except promotion". |
| Pawns per side never increase. | `(p.play m).pawns c ≤ p.pawns c` | D1 | |
| Promotions are paid for by missing pawns. | `p.excess c + p.pawns c ≤ 8`, where `excess c = (Q−1)⁺ + (R−2)⁺ + (N−2)⁺ + (Bₗ−1)⁺ + (B_d−1)⁺` | D1-D2 | **This is the correct form of "bishops stay on their colour."** See the hazard below. |
| Castling rights only disappear. | `(p.play m).castling ⊆ p.castling` | D1 | |
| Castling rights imply home squares. | right K ⇒ white king on e1 and rook on h1, and so on | D1 | Part of `WellFormed`. |
| En passant target is consistent. | `ep = some t →` an enemy pawn stands just beyond `t`, and `t` and the square behind it are empty | D1 | |
| At most two checkers; double check only by specific geometry. | `checkers.length ≤ 2` | D2 | True for reachable positions; *false* for arbitrary well-formed ones, so it needs the reachable induction and a discovered-check case analysis. |

**Phrasing hazard: bishops and colours.** The English "bishops stay on their colour" is a
statement about *piece identity over time*, but a `Position` does not record which bishop is
which. The faithful position-level statements are:

- per move: a bishop move does not change square colour (Section 3.1);
- per position: light-squared bishops `Bₗ ≤ 1 + promotions`, and promotions are bounded by
  missing pawns, which gives the `excess` inequality above.

A promoted bishop may land on either colour, so the naive invariant "at most one white bishop
per colour" is **false** for reachable positions. That is exactly the kind of English-to-Lean
mismatch the process should catch.

Judgment: the `excess` invariant is the most useful single legality filter (it rejects most
"impossible material" FENs) and is a clean preservation proof: a capture can only lower an
`excess` term, and a promotion lowers `pawns` by one and raises one `excess` term by at most one.

### 3.3 Move generation: soundness, completeness, refinement

The central correctness theorem of the library (judgment):

```lean
theorem mem_legalMoves (h : WellFormed p) : m ∈ legalMoves p ↔ Legal p m
theorem legalMoves_nodup (h : WellFormed p) : (legalMoves p).Nodup
```

- **Soundness** (`→`): every generated move is legal. Difficulty D2: it splits per piece kind,
  and castling, en passant and promotion are the costly cases.
- **Completeness** (`←`): every legal move is generated. D2, and harder than soundness because
  it needs a characterization lemma per piece: "if `PseudoLegal p m` for a rook, then `m.dst`
  is on one of the four rays from `m.src`, and `m` appears in that ray's output."
- **Nodup** (D1-D2) matters because perft *counts*. Without it, a duplicated move inflates
  perft while soundness and completeness still hold.

Phrase completeness with `↔` on membership plus `Nodup`, not equality of lists, so that move
ordering stays an implementation freedom.

**Refinement to an efficient layer** (bitboards, judgment):

```lean
theorem Fast.legalMoves_perm (h : b.Represents p) :
    (Fast.legalMoves b).map Fast.Move.toSpec ~ legalMoves p      -- List.Perm
theorem Fast.play_represents (h : b.Represents p) (hm : Legal p (m.toSpec)) :
    (Fast.play b m).Represents (p.play m.toSpec)
```

Difficulty D2 overall. Precomputed attack tables (knight, king, magic or ray tables) are D0
per table, by exhaustive comparison against the ray-walking spec over all 64 squares; for
sliders with occupancy subsets this is about 10^5 entries, which suits `native_decide` and is
heavy for the kernel. Algebraic sliding-attack methods (for example a subtraction trick on
`BitVec 64`) avoid tables, but their proofs are D2 bit-level reasoning (`bv_decide` may help;
see the trust note in Section 4).

Judgment: once `mem_legalMoves` is proved, the move layer has a single trusted definition,
`Legal`, which a chess player can review by reading it next to FIDE Article 3.

### 3.4 Perft: specification and differential testing

```lean
def perft : Nat → Position → Nat
  | 0, _ => 1
  | n+1, p => ((legalMoves p).map fun m => perft n (p.play m)).sum

/-- perft counts legal move sequences of length n. -/
theorem perft_spec (h : WellFormed p) :
    perft n p = (legalSeqs p n).length          -- legalSeqs: all `ms` with `LegalSeq p ms ∧ ms.length = n`
```

`perft_spec` is D1 given `mem_legalMoves`, `legalMoves_nodup` and `WellFormed.play`.

Facts (Chess Programming Wiki, *Perft* and *Perft Results*): perft counts leaf nodes of the
strictly-legal move tree and is compared with published reference values. It deliberately
ignores repetition, the 50-move rule and insufficient material, and stops at mates and
stalemates. Reference counts include: start position 20 / 400 / 8,902 / 197,281 / 4,865,609
for depths 1-5; Kiwipete 48 / 2,039 / 97,862 / 4,085,603; Position 3 14 / 191 / 2,812 /
43,238 / 674,624; Position 4 6 / 264 / 9,467 / 422,333; Position 5 44 / 1,486 / 62,379 /
2,103,487, which "caught bugs in engines several years old at depth 3".

**How perft fits a proved library (judgment).** Before the generator is proved, perft
agreement is evidence that *the generator* is right. After `mem_legalMoves` is proved, perft
agreement is evidence that *the specification `Legal`* agrees with how the chess-programming
community reads the rules, which is the one thing no Lean proof can establish. So perft tests
stay valuable after verification; their target changes from the implementation to the spec.

Concrete perft facts as theorems: `perft 4 Position.initial = 197281 := by native_decide` is
D0. Kernel-only (`decide +kernel`) is plausible for depths 2-3: the prototype's scratch file
`scratch/Speed.lean` closes a single-position move count (`(legal g').length = 34`) with
`decide +kernel`. Cost grows roughly with the branching factor (about 30x) per ply.

Phrasing hazard: perft is defined over the *move layer*. It must not consult the halfmove clock
or history, or it stops matching the published numbers (for example, Position 5's FEN has
`1 8` clocks). This is another reason to keep the game layer separate.

### 3.5 Terminal positions: check, mate, stalemate, dead positions

Definitions written to match FIDE 3.9.1, 5.1.1, 5.2.1 word for word (judgment):

```lean
def InCheck (p : Position) : Prop := ∃ s, p.colorAt s = some p.turn.other ∧ Attacks p s (p.kingSquare p.turn)
def Checkmate (p : Position) : Prop := InCheck p ∧ ∀ m, ¬ Legal p m
def Stalemate (p : Position) : Prop := ¬ InCheck p ∧ ∀ m, ¬ Legal p m
```

| Theorem | Shape | Difficulty |
|---|---|---|
| Decidability via the generator. | `Checkmate p ↔ inCheck p = true ∧ legalMoves p = []` | D1 after `mem_legalMoves` |
| Trichotomy of a position with no legal moves. | `(∀ m, ¬ Legal p m) → Checkmate p ∨ Stalemate p` (exclusive) | D1 |
| A mated side was put in check by the last move. | `Legal p m → Checkmate (p.play m) → InCheck (p.play m)` (trivial), and: the moving side is never in check after its own move | D1 |
| **Dead position (FIDE 5.2.2).** | `Dead p := ¬ ∃ q, ReachableFrom p q ∧ Checkmate q` | definition D0; instances D2-D3 |
| Bare kings are dead. | `p.men = 2 → Dead p` | D1-D2: "only kings" is preserved (no captures are possible) and mate needs an attacker other than a king |
| K+B v K and K+N v K are dead; all bishops on one square colour with no pawns or other pieces is dead. | similar | D2: a geometric argument, or D0 by exhausting the about 10^5 to 10^6 three-man placements with `native_decide` |
| A forced win is never dead. | `WinsIn a n p → ¬ Dead p` | D1: a mating line is a witness |

Phrasing hazard: **dead is existential, forced win is universal.** "Neither player can
checkmate *with any series of legal moves*" means even with the opponent's cooperation
(helpmate). A position can be non-dead and still a theoretical draw. Ambrona's paper also
separates *unwinnable for one player* (no helpmate for that player) from *dead* (unwinnable
for both); the library should define both.

### 3.6 Termination and game length under the result rules

Facts: the 50-move rule is claimable (FIDE 9.3), so it alone does **not** make games finite;
the 75-move rule and fivefold repetition are automatic (9.6). The longest possible game is
8,848.5 moves under the 75-move rule and 5,898.5 moves if the 50-move rule is treated as
automatic (Wismuth's analysis).

A clean, provable termination argument (judgment) that needs **no repetition reasoning**:
model the 75-move rule as "the game is over when the clock reaches 150 plies and the position
is not mate", and use the lexicographic measure

```
μ(p) = (men(p), pawnSteps(p), 150 − clock(p))
```

where `pawnSteps` is the total number of single-square advances all pawns still have before
promotion. Every legal move strictly decreases μ:

- a capture lowers `men`;
- a non-capturing pawn move (push, double push, or promotion) keeps `men` and lowers
  `pawnSteps`;
- any other move keeps both and increments the clock, which is below 150 while the game is in
  progress.

```lean
theorem play_measure_lt (h : WellFormed p) (hm : Legal p m) (hc : p.clock < 150) :
    Prod.Lex … (μ (p.play m)) (μ p)
theorem game_wf : WellFounded (fun q p => ∃ m, Legal p m ∧ p.clock < 150 ∧ q = p.play m)
```

Difficulty D1-D2. A crude explicit bound follows: about (30 captures + 96 pawn steps + 1)
x 150 plies, roughly 9,500 moves, the same order as Wismuth's exact 8,848.5.

Judgment: this is a high-value theorem. It is what makes "the value of a position" a
well-defined function by well-founded recursion (Zermelo-style determinacy, Section 3.8),
and it is cheap.

Repetition: fivefold repetition needs history in the state and a semantic notion of "same
position" (FIDE 9.2.3: same possible moves, so an en passant target counts only if an en
passant capture is actually legal). Judgment: define `Position.SameFIDE` explicitly instead of
reusing `=` on the record. Fivefold is not needed for termination once the 75-move clock is
modelled.

### 3.7 Reachability, retrograde analysis, proof games

| Theorem family | Shape | Difficulty |
|---|---|---|
| A given position is reachable (a proof game). | `Reachable (Position.initial.playList ms)` with `ms` given, checked by `decide`/`native_decide` | D0 per instance |
| A given position is unreachable. | `¬ Reachable p`, via a violated invariant from Section 3.2 | D0-D1 per instance, given the invariants |
| A proof game is **shortest**. | `∀ ms, ms.length < k → playList ms ≠ p` | D2-D3: exhaustive search; feasible only for tiny k |
| Retro-move generator spec. | `q ∈ unmoves p ↔ ∃ m, Legal q m ∧ q.play m = p` | D2: uncaptures, un-promotions, and recovering castling and en passant rights make this the hardest generator |
| Reachability is decidable in general. | `Decidable (Reachable p)` | D3 in practice |

Facts: FIDE defines an illegal position as one no series of legal moves could produce (3.10.3).
Shortest proof games are the problemists' standard device for proving a position legal (the
Wikipedia *Proof game* article; Malikovic and Cubrilo's Coq systems). Tromp's estimate of about
4.8 x 10^44 legal positions came from sampling random positions and checking legality, not
from a proof per position.

Judgment: reachability is mostly a *source of invariants* for this library, not a target. The
useful theorem is "every invariant in Section 3.2 holds for reachable positions", which turns
cheap computable checks into certified rejections of illegal FENs.

### 3.8 Forced-win semantics

The prototype's semantics (fact, `prototype/ChessProof/Cert.lean`) is an inductive predicate
`WinsIn a n p`, "side `a` can force checkmate from `p` using at most `n` of its own moves,
whatever the opponent does", with three constructors: `mate` (the defender is to move and
is mated), `att` (the attacker picks one legal move, budget `n+1 → n`), `dfd` (the defender has
at least one legal move and every one still loses, same budget).

Theorems, in order of how much they are worth (judgment):

| Theorem | Shape | Difficulty | Status |
|---|---|---|---|
| **Not both sides win.** | `WinsIn a n p → WinsIn a.other k p → False` | D1 | proved in prototype (`not_both`) |
| Monotonicity in the budget. | `WinsIn a n p → n ≤ n' → WinsIn a n' p` | D1 | missing |
| Decidability (bounded minimax). | `winsIn? a n p = true ↔ WinsIn a n p`, hence `Decidable (WinsIn a n p)` | D1-D2 | missing |
| Duality: the defender survives iff the attacker does not win. | `Survives a n p ↔ ¬ WinsIn a n p` with `Survives` an inductive with "defender picks one move, attacker's moves all covered" | D1-D2 | missing |
| A forced win is not dead (Section 3.5). | `WinsIn a n p → ¬ Dead p` | D1 | missing |
| **Determinacy** under the 75-move rule: every game state is a win for White, a win for Black, or neither side can force a win. | `value s ∈ {win, draw, loss}` with `value s = win ↔ Wins s.turn s`, defined by well-founded recursion on μ | D2 | needs Section 3.6 |
| Agreement with the FIDE game. | `WinsIn a n p → p.clock + 2n ≤ 150 → (∀ q, hist.count q ≤ 3) → FideWins a ⟨p, hist⟩` | D2 | missing; this is the theorem that discharges the prototype README's caveat |

Facts on determinacy: Zermelo's 1913 paper is often credited with proving that chess is
determined; Schwalbe and Walker (2001) argue that it contains the backward-induction idea
but never states that theorem formally. The chess statement (White can force a win, or Black
can, or both can force at least a draw) needs finiteness, which comes from the automatic draw
rules.

Judgment on the "agreement with FIDE" theorem: the 75-move rule is the only result rule that
can cancel a forced mate, and a clock-headroom hypothesis disposes of it. Repetition cannot,
except via prior history: if the attacker plays a strategy that always reduces its *minimal*
mate budget, positions along any line are pairwise distinct, so no position repeats inside the
line. A dead position never occurs inside a mating line (it reaches mate). Stating this
theorem precisely is the most direct way to make the library's `WinsIn` provably faithful to
real chess.

Phrasing hazards:

- "**Mate in n**" in chess usage means the attacker delivers mate on its n-th move.
  `WinsIn a n p` means *at most* n. A "mate in exactly n" theorem needs both
  `WinsIn a n p` and `¬ WinsIn a (n-1) p` (Section 3.9).
- `dfd` must require that the defender has a legal move. Otherwise a *stalemated* defender
  vacuously "loses". The prototype does this (`legal p ≠ []`); it must survive any rewrite.
- `att` with `n = 0`: the budget counts attacker moves, so `WinsIn a 0 p` holds only when
  the defender is already mated. Make this a stated lemma so readers see the convention.

### 3.9 Certificates: soundness, completeness, only-move, minimality, draws

The pattern (fact, prototype and the SAT-proof literature): an untrusted search emits a
certificate; a small checker function decides it; a soundness theorem lifts `check = true` to
the semantic claim. The same architecture is used for SAT proofs, where solvers emit DRAT
proofs, an untrusted tool turns them into LRAT, and a verified checker (`cake_lpr`, CakeML)
checks the result. The searcher stays out of the trust base.

| Theorem | Shape | Difficulty | Status |
|---|---|---|---|
| Soundness. | `check fuel a n p c = true → WinsIn a n p` | D1 | proved (`check_sound`) |
| **Completeness** (the format is not lossy). | `WinsIn a n p → ∃ c, check (2n+2) a n p c = true` | D1 | missing; cheap and worth having |
| Only move. | `onlyMove … = true → best ∈ legal p ∧ WinsIn p.turn n (play p best) ∧ ∀ m ∈ legal p, (Wins p.turn (play p m) ↔ m = best)` | D1 | proved (`onlyMove_sound`) |
| Minimality (exact distance to mate). | `checkSurvives … = true → ¬ WinsIn a (n-1) p`, via the duality of Section 3.8 | D1-D2 | missing; a defender certificate is the mirror-image tree |
| **Draw certificates** (a side *cannot* win). | Given a set `S` (as a decidable predicate) with: `p ∈ S`; nothing in `S` is checkmate of the defender; at every defender-to-move `q ∈ S` some legal reply stays in `S`; at every attacker-to-move `q ∈ S` every legal move stays in `S`; then `¬ Wins a p` | D1 to state and prove; D0-D2 per instance | missing |

Judgment on draw certificates: wins are certified by **finite trees** (induction); "cannot
win" is certified by **closed sets** (an invariant, which is coinduction). This is the missing
half of the semantics. It is what makes "every *other* move only draws" provable, so it is the
gateway to optimality claims that are not just "only winning move". For small endgames, a
closed set can be a tablebase slice. For fortresses, it can be a hand-written predicate
("the black king stays on the queenside light squares and the bishop holds the diagonal").

The prototype's per-node kernel proofs (fact: ~80 s, ~6 GB for the mate in 11) show that
certificate size, not checker complexity, is the cost driver. Judgment: certificate
compression (transpositions shared via a DAG, symmetry reduction) is a later optimization
that needs only a soundness proof for the compressed checker.

### 3.10 "Optimal move": what can actually be stated and proved

Exact optimality is a statement about the game value, defined once termination (3.6) gives
`value : GameState → Outcome` with `loss < draw < win`:

```lean
def Optimal (s : GameState) (m : Move) : Prop :=
  Legal s.pos m ∧ ∀ m', Legal s.pos m' → (s.play m').value.flip ≤ (s.play m).value.flip
```

(`flip` because the child's value is from the opponent's point of view.) Ways to obtain
instances, in increasing order of difficulty (judgment):

1. **Only winning move** (D0 per instance; exists). If `m` wins and every alternative hands
   the opponent a forced win, `m` is the unique optimal move. This is what the prototype proves.
2. **Winning move with draw-bounded alternatives** (D0-D2 per instance). `m` wins; every other
   move is refuted by either a win certificate for the opponent or a draw certificate
   (Section 3.9). Then `m` is the unique optimal move. This needs the draw certificates.
3. **Interval certificates** (D1 to state). Certify for each legal move an interval
   `[lo, hi] ⊆ {loss, draw, win}`: a lower bound comes from a win certificate (`win`) or a
   cannot-lose certificate (`draw`); an upper bound comes from an opponent's win certificate
   (`loss`) or a cannot-win certificate (`draw`). If `lo(m) ≥ hi(m')` for every `m'`, then `m`
   is optimal. This one framework covers (1) and (2) and degrades gracefully: when it cannot
   close, it still proves "`m` is no worse than a draw and every other move is at most a draw",
   a precise partial claim.
4. **Endgame-exact claims** (D2 per material signature). Verified tablebases (Hurd's HOL4
   route) give exact values for tiny material. Facts: Syzygy tables cover up to 7 pieces and
   exclude castling rights; their WDL distinguishes "cursed wins" and "blessed losses" (wins or
   losses that the 50-move rule turns into draws), and some DTZ values can be off by one ply.
   So "Syzygy says win" must be mapped carefully to a rule set: wins under the claimable
   50-move rule, the 75-move rule, and no clock rule are three different predicates.
   Judgment: use tablebases only as an *untrusted oracle* that proposes certificates, as with
   Stockfish.
5. **Goal-directed forcing** (D1 to define; D0 per instance). Generalize `WinsIn` from "mate"
   to an arbitrary decidable goal `G` (win material, promote, reach a position in a verified
   tablebase slice):
   `Forces a G n p`. `WinsIn a n p` is then `Forces a (Checkmate ∧ defender to move) n p`.
   Theorems such as "this move wins a piece by force within 3 moves, and no other move does"
   are what engine evaluations like "+3" informally claim. Caveat: these are claims about
   `G`, not about the game value, and the English must say so.
6. **Full optimality from the opening or a typical middlegame** (D3). Out of reach;
   computing a value requires solving the game.

Stockfish's role (judgment): it proposes the move, the principal variation, the refutation of
each alternative, and which alternatives are worth refuting at all. Its *numbers* never appear
in a theorem. The honest English for an engine-assisted result is, for example, "Lean checks
that Stockfish's choice is the only move that keeps a forced mate", never "Stockfish evaluates
this as +M11".

Curiosity fact: the maximum number of legal moves in a reachable position is 218 (Petrovic's
1964 position). In 2024 the Lichess blogger "Tobs40" claimed a proof of this upper bound via an
integer-programming model solved by Gurobi, conditional on the solver and on modelling
simplifications. Judgment: proving `(legalMoves p).length ≤ 218` for reachable `p` in Lean is
D3 and of little use. A loose bound (for example, at most a few hundred for any well-formed
position) is D1 if it is ever needed, say for array sizing in the fast layer.

### 3.11 I/O theorems (FEN, UCI, SAN)

| Theorem | Shape | Difficulty |
|---|---|---|
| FEN round trip. | `WellFormed p → parseFEN (toFEN p) = some p` | D1-D2 (string reasoning is tedious in core Lean) |
| FEN parser yields well-formed positions or fails. | `parseFEN s = some p → WellFormed p` (validate in the parser) | D1 |
| SAN round trip and unambiguity. | `Legal p m → parseSAN p (toSAN p m) = some m` | D2 (disambiguation by file, rank or square) |

Judgment: the round-trip theorems pay off because they make concrete theorem statements
readable (`fen "..."`, `san "Qxb4+"`) while remaining trustworthy: the reader trusts the
statement only if `fen` provably means what the string says.

---

## 4. Trust levels for computational proofs (facts and judgment)

- `decide +kernel` / `decide`: only the kernel is trusted. Fact (prototype): the kernel-only
  mate in 11 needed ~80 s and ~6 GB with 320 generated per-node theorems; the board as a single
  `Nat` exploits the kernel's GMP-accelerated `Nat` operations.
- `native_decide`: also trusts the Lean compiler; such theorems depend on the axiom
  `Lean.ofReduceBool`, visible with `#print axioms` (Lean reference and tactic docs). Fact
  (Lean Zulip, Feb 2026): a change in lean4 PR #12217 was announced to replace `ofReduceBool`
  with a per-use axiom. Whether it is in Lean 4.28 should be checked before documenting it.
- `bv_decide`: uses a verified LRAT checker but runs it natively, so it carries the same
  compiler trust (Lean v4.12.0 release notes).

Judgment: every headline theorem should state its trust level in its docstring, and the
library should keep a `#print axioms` regression file (an "axioms ledger") listing which
theorems use `ofReduceBool`.

---

## 5. English-to-Lean faithfulness hazards (summary checklist)

| English phrase | Trap | Faithful Lean phrasing |
|---|---|---|
| "in check" | Using legal attacks (respecting pins) | Geometric `Attacks`, per FIDE 3.9.1 |
| "legal move" | Implicitly assuming a well-formed position | `Legal p m` plus `WellFormed p` as a theorem hypothesis |
| "exactly one king" | Proving it for all positions (false) | For well-formed positions by preservation; reachable as a corollary |
| "bishops stay on their colour" | Position-level "at most one bishop per colour" is false after promotion | Per-move colour preservation, plus the `excess` inequality |
| "pieces only decrease" | Promotion changes kinds | Men are non-increasing; pawns are non-increasing; excess is bounded by missing pawns |
| "mate in n" | At most n versus exactly n | `WinsIn a n p ∧ ¬ WinsIn a (n-1) p` for exactly n |
| "forced win" | Stalemated defender counted as lost | `dfd` requires a legal move |
| "the game ends" | 50-move rule is a claim, not automatic | 75-move rule and fivefold as automatic; 50-move as a claim option if modelled |
| "same position" (repetition) | Record equality versus FIDE 9.2.3 | `SameFIDE`: en passant counts only if an en passant capture is legal |
| "dead position" | Confusing helpmate (exists) with forced (for all) | `Dead p := ¬ ∃ q, ReachableFrom p q ∧ Checkmate q` |
| "optimal move" | Engine score versus game value | `Optimal` over `value`; partial claims via interval certificates |
| "Stockfish says" | Engine numbers inside theorems | Engine output only as untrusted certificate input |

---

## 6. Dependency map (judgment)

```
Squares/rays ─► Attacks ─► PseudoLegal ─► Legal ◄── play
                                   │                │
                                   ▼                ▼
                         legalMoves (mem_legalMoves, nodup) ──► perft_spec ──► perft tests (D0)
                                   │
              WellFormed.play ◄────┘  (invariants; Reachable as corollary)
                     │
     ┌───────────────┼────────────────────────────┐
     ▼               ▼                            ▼
 Checkmate /     Termination μ (75-move)      WinsIn, not_both, monotone, decidable
 Stalemate /         │                            │
 Dead                ▼                            ▼
     │          value, determinacy ◄──── Survives duality, draw certificates
     │               │                            │
     └──────────────►┴──► Optimal, interval certificates, only-move, FIDE agreement
```

Fast layer (bitboards) attaches at `legalMoves` and `play` through the refinement theorems,
and nothing above depends on it.

---

## Recommendations for this library

1. **Define `Legal` declaratively and early, next to FIDE Article 3**, with `Attacks`
   geometric (FIDE 3.9.1). Make `mem_legalMoves : m ∈ legalMoves p ↔ Legal p m` plus
   `legalMoves_nodup` the first major milestone (D2). It is the theorem that retires the
   prototype's biggest caveat.
2. **Separate the move layer from the game layer.** `Position`, `Legal`, `play`,
   `legalMoves` and `perft` know nothing about the 75-move clock or history; `GameState` and
   the result rules (Art. 5, 9) live in their own module.
3. **Make `WellFormed` the workhorse and `Reachable` a corollary.** Prove invariants by
   preservation under `Legal` for well-formed positions. Consider storing king squares as
   fields so "one king per side" holds by construction.
4. **Phrase the material invariants correctly**: men non-increasing; pawns non-increasing;
   `excess c + pawns c ≤ 8` with bishops split by square colour. Do not state "one bishop per
   colour".
5. **Keep perft as differential testing of the spec.** Include the six standard positions as
   `native_decide` regression theorems at modest depths (and one or two `decide +kernel` at
   depth 2-3), plus `perft p.flip n = perft p n` as a proved theorem.
6. **Prove termination cheaply with μ = (men, pawnSteps, 150 − clock)** under the automatic
   75-move rule. This gives determinacy and a well-defined `value` with no repetition
   bookkeeping.
7. **Carry the prototype's `WinsIn` forward** (its three constructors are right, including the
   "defender has a legal move" guard), and add: monotonicity, a decision procedure with
   `winsIn?_iff`, the `Survives` duality, certificate completeness, and the FIDE-agreement
   theorem with clock headroom.
8. **Add draw (closed-set) certificates and interval certificates.** These are the smallest
   additions that move the library from "only winning move" to "optimal move" in positions
   where alternatives draw rather than lose.
9. **Generalize forcing to a goal predicate** (`Forces a G n p`) and define `WinsIn` as an
   instance, so material-winning and tablebase-reaching claims reuse one checker and one
   soundness proof.
10. **Treat Stockfish and tablebases strictly as untrusted oracles.** They propose
    certificates; theorems never mention their scores. Write the English for every
    engine-assisted theorem in terms of what Lean checked.
11. **Record trust in every headline theorem** (kernel only, or plus `ofReduceBool`) and keep
    an axioms-ledger file of `#print axioms` outputs.
12. **Defer** the D3 items: proving 218, deciding reachability in general, shortest-proof-game
    minimality beyond tiny cases, and optimality in general middlegame positions.

Suggested first theorem list for `docs/THEOREMS.md`, in build order: attack symmetry;
`WellFormed.play`; `mem_legalMoves` and `legalMoves_nodup`; `perft_spec`; perft regression
facts; `Checkmate`/`Stalemate` decidability; `play_measure_lt` and `game_wf`; `not_both`,
`WinsIn.mono`, `winsIn?_iff`; `check_sound`, `check_complete`, `onlyMove_sound`; draw-certificate
soundness; `Optimal` via interval certificates; FIDE agreement for `WinsIn`.

---

## Sources

- FIDE Laws of Chess (Handbook E01, 2023): https://handbook.fide.com/chapter/E012023
- J. Hurd, *Formal Verification of Chess Endgame Databases* (TPHOLs 2005): https://gilith.com/papers/chess.pdf ; poster https://www.gilith.com/talks/tphols2005-poster.pdf ; talk https://www.gilith.com/talks/oxford2005.pdf ; Galois summary https://www.galois.com/articles/formally-verified-chess-endgames
- Maric, Janicic, Malikovic, *Computer-Assisted Proving of Combinatorial Conjectures Over Finite Domains: A Case Study of a Chess Conjecture* (LMCS 2019): https://arxiv.org/pdf/1801.07528 , https://lmcs.episciences.org/5328/pdf ; CADE 2015 KRK in Isabelle/HOL and Z3: https://www.bib.irb.hr/763728
- Malikovic and Cubrilo, Coq retrograde / shortest proof games: https://www.bib.irb.hr/366507 , https://www.bib.irb.hr/493567 , https://archive.ceciis.foi.hr/index.php/ceciis/2010/paper/view/293.html
- dwrensha, Chess in Lean 4: https://reservoir.lean-lang.org/@dwrensha/Chess (repo https://github.com/dwrensha/Chess.lean)
- Lean Across the Board: https://lean-across-the-board.readthedocs.io/
- Mathlib combinatorial games (PGame): https://florisvandoorn.com/LeanCourse24/docs/Mathlib/SetTheory/Game/PGame.html ; vihdzp CombinatorialGames: https://reservoir.lean-lang.org/@vihdzp/CombinatorialGames
- M. Ambrona, *A Practical Algorithm for Chess Unwinnability* (FUN 2022): https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FUN.2022.2 ; implementation in clean-chess: https://github.com/dlbbld/clean-chess
- Chess Programming Wiki, Perft: https://www.chessprogramming.org/Perft ; Perft Results: https://www.chessprogramming.org/Perft_Results ; Fifty-move Rule: https://www.chessprogramming.org/Fifty-move_Rule
- Wismuth, *The longest possible chess game*: https://wismuth.com/chess/longest-game.html
- Wikipedia, Draw (chess): https://en.wikipedia.org/wiki/Draw_(chess) ; Proof game: https://en.wikipedia.org/wiki/Proof_game ; Zermelo's theorem (game theory): https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
- Schwalbe and Walker, *Zermelo and the Early History of Game Theory*: https://www.uni-hohenheim.de/en/organization/publication/zermelo-and-the-early-history-of-game-theory ; discussion-paper version with Zermelo translation: https://ageconsearch.umn.edu/record/263784/files/canterbury-nz-092.pdf
- Tobs40 (Lichess blog), *There is no reachable chess position with more than 218 moves*: https://lichess.org/@/Tobs40/blog/there-is-no-reachable-chess-position-with-more-than-218-moves/a5xdxeqs ; OEIS A278830: https://oeis.org/A278830
- J. Tromp, number of legal positions (~4.8 x 10^44): https://www.talkchess.com/viewtopic.php?p=975229 ; https://chessprogramming.org/John_Tromp
- python-chess Syzygy documentation (WDL, DTZ, cursed wins): https://python-chess.readthedocs.io/en/latest/syzygy.html
- Tan, Heule, Myreen, *cake_lpr: Verified Propagation Redundancy Checking in CakeML* (TACAS 2021): https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7984575/
- Lean `native_decide` / `ofReduceBool` trust: https://lean-lang.org/doc/reference/4.35.0-rc3/releases/v4.12.0/ ; Zulip thread on changes: https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Heads.20up.3A.20changes.20to.20native_decide.20(and.20bv_decide).html
- Prototype in this repository: `prototype` (README, `ChessProof/Basic.lean`, `ChessProof/Cert.lean`, `ChessProof/Line.lean`, `scratch/`)
