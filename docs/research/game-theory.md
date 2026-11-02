# Game theory for "this move is optimal"

Research note for the `Chess` library. Scope: what it means, precisely, for a chess move to be
optimal; which parts of that can be proved in Lean; what evidence each claim needs; and how an
untrusted engine (Stockfish, tablebases) can supply that evidence.

**Conventions in this note.**

- Paragraphs marked **Fact** report what a cited source says, or standard mathematics.
- Paragraphs marked **Judgment** are my own assessment or design proposal. Treat them as
  proposals to be argued with in `docs/DESIGN.md` and `docs/THEOREMS.md`.
- Lean snippets are *sketches of statements*, not code that compiles today.
- "Ply" means one move by one side. "Move" in the FIDE sense means a ply by each side.
  DTM in the literature counts winner moves; Syzygy DTZ counts plies. Every metric
  in the library must say which unit it uses.

---

## 1. The two games called "chess"

The game-theoretic value of a position depends on *which game* we mean. There are at least
three reasonable answers, and they give different values for some real positions.

### 1.1 Facts: what the FIDE Laws say (Laws of Chess, effective 1 January 2023)

Source: FIDE Handbook E.01, <https://handbook.fide.com/chapter/E012023>. Paraphrased:

- **Checkmate (5.1.1)** wins and ends the game immediately.
- **Stalemate (5.2.1)**: the side to move has no legal move and is not in check. The game is
  drawn immediately. *Stalemate is a draw, not a loss.* Any "forced win" definition must
  exclude it.
- **Dead position (5.2.2, 1.5)**: neither player can checkmate by *any* series of legal moves,
  even with the opponent's help. The game is drawn immediately.
- **Threefold repetition (9.2)** and the **50-move rule (9.3)** are *claims*: the player to
  move may claim a draw. Neither happens automatically.
- **Fivefold repetition (9.6.1)** and the **75-move rule (9.6.2)** are *automatic* draws. For
  the 75-move rule, a mate on the last move takes precedence.
- **"Same position" (9.2.3)**: same player to move, same pieces on the same squares, and *the
  same possible moves for all pieces*. So positions differ if an en passant capture was
  possible in one and not the other. They also differ if castling rights were lost. Castling
  rights are lost only when the king or rook moves. Note that the test is whether an en passant
  capture is *possible*. FEN's en passant field does not decide it, because some writers set the
  field after every double pawn push.
- **Illegal position (3.10.3)**: a position that no series of legal moves can reach.
- **Timeout (6.9)** and **resignation (5.1.2)**: these produce a draw instead of a loss when the
  opponent cannot mate "by any possible series of legal moves". This is the unwinnability
  notion. It is weaker than a dead position because it concerns only one side.

### 1.2 Three games

**Judgment.** The library should name three games explicitly and relate them by theorems.
It should not pick one silently.

| Game | State | Terminal draws | Finite plays? | Who uses it |
|---|---|---|---|---|
| **G∞** ("pure chess") | board, side, castling, en passant | stalemate only; infinite play is a draw | no, play can cycle forever | DTM tablebases (Nalimov, Lomonosov), problem composers, Zermelo |
| **G₅₀** (claim rules, claimed when allowed) | + halfmove clock | stalemate; 100 plies without a zeroing move | yes | Syzygy WDL ("cursed win" = draw) |
| **G_FIDE** (automatic rules) | + halfmove clock + repetition history | stalemate; dead position; 150 plies; fivefold | yes | the Laws as written |

A *zeroing move* is a capture or a pawn move. It resets the halfmove clock.

Three facts show why this split is useful. They are elementary, and the proofs are sketched in
§2.4.

1. In G∞, **repetition rules never change a forced win.** A winning strategy can always be
   chosen so that it never repeats a position.
2. **Dead positions never change the value.** A dead position is already a draw in every one of
   the games, because nobody can ever mate from it.
3. **Clock rules (50 or 75 moves) do change values.** These are Syzygy's cursed wins.

So the only history-dependent rule that changes W/D/L is the halfmove clock. The full
repetition history can stay out of the value semantics.

---

## 2. Zermelo, backward induction, and determinacy

### 2.1 Facts

- Zermelo addressed the Fifth ICM (Cambridge, 1912) and published the paper as "Über eine
  Anwendung der Mengenlehre auf die Theorie des Schachspiels" in 1913. In modern form the
  theorem says: in chess, either White can force a win, or Black can force a win, or both
  sides can force at least a draw.
  <https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)>
- Schwalbe and Walker ("Zermelo and the Early History of Game Theory", *Games and Economic
  Behavior* 34 (2001) 123–137) translate the paper. They argue that most modern statements of
  "Zermelo's theorem" only partly resemble what Zermelo proved. Zermelo did not use backward
  induction. The paper's actual question was whether a winning player can force a win within a
  bounded number of moves. König (1927) and Kalmár (1928) supplied later pieces of the
  argument. <https://ideas.repec.org/a/eee/gamebe/v34y2001i1p123-137.html>,
  translation reprint: <https://www.rasmusen.org/GI/reader/notes/19zermelo.1913.txt>
- **Reachability games on finite graphs are positionally (memorylessly) determined.** The
  *attractor* of a target set T is the set of nodes from which player 0 can force a visit to T.
  It is built by iteration:
  - Attr₀ = T.
  - Attrᵢ₊₁ adds the player-0 nodes that have *some* edge into Attrᵢ.
  - It also adds the player-1 nodes whose edges *all* go into Attrᵢ.

  The complement of the attractor is a *trap* for player 0: player 1 can keep play inside it
  forever. Both strategies can be taken positional. The stage at which a node enters the
  attractor is its *rank*.
  <https://www.react.uni-saarland.de/teaching/automata-games-verification-11/downloads/notes10.pdf>,
  <https://www.logic.rwth-aachen.de/files/LS/LS-chapter2.pdf>; standard reference: Grädel,
  Thomas, Wilke (eds.), *Automata, Logics, and Infinite Games*, LNCS 2500 (2002).

### 2.2 How this maps onto chess

**Fact (standard).** Under G∞, "White can force mate" is a reachability objective on the
finite graph of positions. White's winning region is the attractor of "Black to move and
checkmated". Here the opponent must have a legal move at defender nodes: a stalemated defender
node is a sink outside the target. The rank of a position is its depth to mate (DTM).
Positions outside both sides' attractors are draws, and each side has a positional strategy
that avoids losing. So G∞ is determined in the strong sense, with memoryless strategies.

**Fact (standard).** G₅₀ and G_FIDE are finite games: every play terminates. The clock rule
bounds each phase between zeroing moves. Zeroing moves are irreversible (pawn moves and
captures), so there are only finitely many phases. Zermelo/Kalmár backward induction applies
directly. The value is defined by well-founded recursion on the remaining game length.

### 2.3 Judgment: the right Lean shape

- **Win is a least fixed point; give it as an inductive predicate.** This is the prototype's
  `WinsIn` (`prototype/ChessProof/Cert.lean`). It worked well, and its three constructors
  (`mate`, `att`, `dfd`) mirror the attractor recurrence exactly.
- **"Avoid losing" is a greatest fixed point; give it by the existence of an invariant, not by
  coinduction.** The sketch:

  ```lean
  /-- `S` is a trap in which side `d` can stay forever without being mated:
      inside `S`, `d` is never checkmated; when `d` moves, some legal move stays in `S`;
      when the opponent moves, every legal move stays in `S`. -/
  def Trap (d : Side) (S : Pos → Prop) : Prop := ...
  def Holds (d : Side) (p : Pos) : Prop := ∃ S, Trap d S ∧ S p
  ```

  This is Knaster–Tarski in the style of a post-fixed point. It needs no `coinductive` keyword
  and no Mathlib. It also gives the certificate format for draws directly (§4.3).
- **Determinacy theorems, in increasing difficulty:**
  1. `not_both : WinsIn a n p → WinsIn a.other k p → False`. This is already proved in the
     prototype.
  2. `Holds d p → ¬ Wins d.other p`. A trap blocks mate, by induction on `WinsIn`.
  3. Bounded determinacy, which is decidable and constructive: for each `n`, either
     `WinsIn a n p`, or the defender has a strategy that survives `n` attacker moves. Written
     as a Boolean minimax with a soundness and completeness proof, this *is* Zermelo/Kalmár
     for depth `n`.
  4. Full determinacy for G∞: `Wins a p ∨ Holds a.other p`. This needs the finiteness of the
     reachable position set, because the attractor must stabilize. Without Mathlib's
     `Fintype`, state it relative to an explicit finite list of positions closed under moves.
     It is a nice theorem but not on the critical path. Certificates only need (1) and (2).
- **Write values relative to the side to move (negamax).** Then W/D/L for one side mirrors the
  other, which halves the definitions and the lemmas.

### 2.4 Judgment: proof sketches for the three facts in §1.2

1. *Repetition never matters for a win in G∞.* Fix a positional attractor strategy. Along any
   play consistent with it, the rank strictly decreases at every ply. Defender moves from rank
   r all land at rank below r, and the attacker's chosen move does too. So no position
   repeats, and the threefold and fivefold rules can never trigger.

   For the clocked games the argument needs one extra monotonicity lemma: a smaller halfmove
   clock is never worse for the side trying to mate. Within a phase, if a board recurs at a
   higher clock, the attacker can shortcut to the strategy for the earlier, lower-clock
   occurrence. Across phases, boards cannot recur, because zeroing moves are irreversible.

   So the claim also holds for G₅₀ and G_FIDE. This is a good, nontrivial target theorem.
2. *Dead positions.* "Dead" means no sequence of legal moves reaches mate. Every `WinsIn`
   derivation contains such a sequence, so `Dead p → ¬ Wins a p` for both sides, in every game.
3. *Clock rules matter.* Syzygy explicitly marks "cursed wins": wins in G∞ that are draws
   under the 50-move rule (§3). Formally, `WinsWithin L a p` (a win in which every phase
   between zeroing moves has at most L plies) is monotone in L. It implies `Wins a p` in G∞.
   And `Wins a p ↔ ∃ L, WinsWithin L a p`, because ranks are bounded on a finite graph.

---

## 3. Retrograde analysis and endgame tablebases

### 3.1 Facts

- Bellman (1965) proposed dynamic programming to determine optimal play in chess and checkers
  endgames. RAND P-3013, <https://www.rand.org/pubs/papers/P3013.html>.
- Thompson, "Retrograde Analysis of Certain Endgames", *ICCA Journal* 9(3) (1986) 131–139,
  introduced practical retrograde analysis. The algorithm:
  1. Seed the table with the mated positions.
  2. Generate *un-moves*. Un-moving into check and un-capturing are allowed.
  3. A position whose parent is a loss-in-i becomes a win-in-(i+1).
  4. A candidate loss is confirmed only when *all* of its successors are known wins.
  5. Whatever is left at the fixpoint is a draw (or an illegal position).

  <https://www.chessprogramming.org/Retrograde_Analysis>. This is the attractor computation of
  §2.1, run backwards.
- **Metrics** (<https://www.chessprogramming.org/Endgame_Tablebases>; Huntington and Haworth,
  "Depth to Mate and the 50-Move Rule", *ICGA J.* 2015):
  - **DTM**: winner's moves to mate.
  - **DTC**: moves to conversion.
  - **DTZ**: plies to the next zeroing move.
  - **DTZ50**: DTZ with the 50-move rule applied.
  - **DTR**: depth "by the rule".

  DTM, DTC and DTZ ignore the 50-move rule.
- **Syzygy** (Ronald de Man, 2013). Bojun Guo generated the 7-piece tables, completed in August
  2018. The 6-piece set is 149.2 GiB and the 7-piece set is 16.7 TiB. WDL files (`.rtbw`)
  account for the 50-move rule and are probed during search. DTZ files (`.rtbz`) are probed at
  the root and store only one side to move. <https://www.chessprogramming.org/Syzygy_Bases>
- Syzygy semantics, per python-chess (<https://python-chess.readthedocs.io/en/latest/syzygy.html>):
  - **WDL** ∈ {−2, −1, 0, 1, 2}. Here ±1 are the *blessed loss* and *cursed win*: mate can be
    forced, but the 50-move rule draws. WDL assumes the position was reached directly after a
    zeroing move, so the clock is 0.
  - **DTZ** is "DTZ50′′ with rounding". It may be off by one ply. Rounding never changes the
    outcome, but in positions that are nearly drawn under the 50-move rule, wasting one more ply
    can change the result.
  - **Positions with castling rights are not in the tables.**
- **Lomonosov** 7-piece DTM tables (Moscow State University, 2012). The longest 7-piece mate is
  549 moves, with the 50-move rule ignored.
  <https://en.wikipedia.org/wiki/Endgame_tablebase>. For 8 pieces, generation is partial. As of
  January 2023 the longest known forced win was 584 moves.
  <https://en.wikipedia.org/wiki/Solving_chess>
- **Formally verified tablebases already exist.** Hurd, "Formal Verification of Chess Endgame
  Databases" (TPHOLs 2005), modeled the laws of chess in HOL4 and computed with the BuDDy BDD
  engine wrapped as a HOL4 derived rule. It produced verified databases for all *pawnless
  endgames with at most four pieces*. <https://gilith.com/papers/chess.pdf>
- Other proof-assistant chess work: a Coq formalization of the KRK endgame and of conjectures
  about it (Maliković, Čubrilo, Janičić, CECIIS 2012,
  <https://poincare.matf.bg.ac.rs/~janicic/papers/2012-ceciis-chess.pdf>). An Isabelle/HOL
  partial theory of pawnless endgames ("Computer-Assisted Proving of Combinatorial Conjectures
  Over Finite Domains: A Case Study of a Chess Conjecture", <https://arxiv.org/pdf/1801.07528>).
  I found no Lean chess formalization.

### 3.2 Judgment: a tablebase is a certificate

This is the most useful idea in this note for the library.

A DTM table is a **ranking-function certificate** for the win region. A WDL table's draw region
is a **trap certificate**. Both can be checked *locally* with **forward** move generation only:

- *Win entry with rank k > 0, attacker to move:* some legal move leads to a position whose rank
  is below k.
- *Win entry, defender to move:* the defender has at least one legal move, and every legal move
  leads to a win entry of lower rank. Rank 0 means checkmate.
- *Draw entry:* never checkmate. The holding side has some move to a draw entry. Every move of
  the other side goes to a draw entry.

The checker needs no un-move generator. Un-move generators are notoriously bug-prone and
would otherwise join the trusted base. So "this table is correct" reduces to a Boolean
`checkTable` with a soundness proof. That is the same pattern as the prototype's
`check_sound`, lifted from trees to sets.

Hurd did essentially this with BDDs. In Lean the table is just data, kernel-checked or
`native_decide`-checked. 3- and 4-piece pawnless tables (KQK, KRK, KBNK…) are realistic first
targets.

For Syzygy-style DTZ, a certificate is compositional. A DTZ ranking proves progress *within* a
phase. Each zeroing move leaves the phase and lands in a *different* material or pawn
configuration, whose WDL must itself be certified. The recursion follows the material order,
so it is well-founded.

---

## 4. Proof trees, proof-number search, and certificates

### 4.1 Facts

- **Proof-number search** (Allis, van der Meulen, van den Herik, *Artificial Intelligence*
  66(1) (1994) 91–124) is a best-first AND/OR search. It finds the game-theoretic value of a
  game tree by repeatedly expanding the "most-proving node". Each node carries a *proof number*
  and a *disproof number*: the minimum number of leaves that must be proved, or disproved, to
  settle it. <https://www.chessprogramming.org/Proof-Number_Search>
- Survey: Kishimoto, Winands, Müller, Saito, "Game-Tree Search Using Proof Numbers: The First
  Twenty Years", *ICGA J.* 35(3) (2012) 131–156. It covers depth-first variants (df-pn,
  Nagai 2002), memory-limited variants, and applications in chess, shogi, Go, LOA and checkers.
  <https://webdocs.cs.ualberta.ca/~mmueller/ps/ICGA2012PNS.pdf>
- **The Graph History Interaction (GHI) problem.** A transposition table stores a result that
  depended on the path, for example on a repetition, and reuses it for the same position
  reached by a different path. The result can then be wrong. Kishimoto and Müller, AAAI 2004
  and *Information Sciences* 175 (2005), give a solution for df-pn.
  <https://webdocs.cs.ualberta.ca/~mmueller/ghi.html>
- **Checkers is solved** (Schaeffer et al., *Science* 317 (2007) 1518): it is a draw under
  perfect play, which makes it *weakly solved*. The proof combines a forward proof-tree search
  with backward endgame databases of up to 10 pieces. The result is a computational proof that
  neither side can win.
  <https://www.cs.mcgill.ca/~dprecup/courses/AI/Materials/checkers_is_solved.pdf>
- **Scale.** Tromp estimates the number of legal chess positions at about 4.8 × 10⁴⁴. Most of
  them carry many promoted pieces. Discussed at <https://chessprogramming.org/John_Tromp>.

### 4.2 Judgment: certificate shapes for a win

| Shape | What it is | Checker | Pros | Cons |
|---|---|---|---|---|
| **Strategy tree** (prototype `Cert`) | one attacker move per attacker node, all replies per defender node | structural recursion | simplest; exactly the PNS proof tree | exponential duplication on transpositions |
| **Strategy DAG** | the same, with shared subtrees | hash-consed data | much smaller | sound in G∞; **unsound under clocks unless the clock is part of the state** (GHI) |
| **Ranked set** | finite set S, a rank, and an attacker choice; local checks as in §3.2 | one pass over S | uniform with tablebases; transpositions free; no depth fuel | needs a finite-map structure in Lean |

All three should be proved sound against the same `WinsIn`. The ranked set is the most
elegant, and it generalizes the other two. A tree is a ranked set whose rank is the height.

**GHI in the library.** Values in G∞ depend only on the position, so sharing is sound. Under
G₅₀, key every shared node by (position, halfmove clock), or else certify the stronger G∞ fact
and the clock bound separately. Never key on FEN text, because FEN carries an en passant field
that may differ from the legal-move-relevant state (§1.1).

### 4.3 Judgment: why draws are harder, and the certificate for them

- A win is a *finite* object: a well-founded tree or ranked set. A draw is a claim that the
  opponent can *never* win. Its witness is a **trap**: a set S of positions closed under the
  holding side's chosen replies and under *all* of the opponent's moves, and containing no
  mate. In a middlegame that set can be astronomically large, because it must contain every
  position the opponent can steer to.
- **Small draw certificates exist when the invariant is symbolic.** Three cases:
  - **Fortresses**: for example "the black king shuttles g8–h8 and the white bishop is the
    wrong color for the h-pawn". Engines misjudge these badly. Stockfish shows large
    advantages in positions that are objectively drawn, because the horizon and the
    no-repetition search policy hide the lack of progress. Fortress detection in engines
    remains heuristic (Guid and Bratko 2012; <https://www.chessprogramming.org/Fortress>).
    *This is where Lean adds the most value over engines and tablebases.* A trap defined by a
    predicate over the board, rather than an enumerated set, can be proved by reasoning,
    for any number of pieces, including positions far beyond 7-piece tables.
  - **Perpetual check and forced repetition**: the trap is a short cycle together with the
    opponent's escapes, each of which must re-enter the cycle or another certified draw.
  - **Tablebase leaves**: in an endgame with at most N pieces, the trap is the table's draw
    region (§3.2).
- **Dead and unwinnable positions** are a special case where the check is cooperative: no
  sequence of moves at all reaches mate. Ambrona, "A Practical Algorithm for Chess
  Unwinnability" (FUN 2022), gives an algorithm claimed sound, complete and efficient in
  practice. It resolved every timeout position in the Lichess database.
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FUN.2022.2>. Its output (a
  helpmate, or a proof that none exists) is again a certificate a Lean checker could verify.
  It matters for 5.2.2 and 6.9 but, as argued in §1.2, not for W/D/L values.

---

## 5. Stockfish as an untrusted oracle

### 5.1 Facts

- **Certifying algorithms**: an algorithm returns, with each output, a witness that a simple
  independent checker can verify, so the algorithm itself need not be trusted. McConnell,
  Mehlhorn, Näher, Schweitzer, "Certifying algorithms", *Computer Science Review* 5(2) (2011)
  119–161. <https://cs.au.dk/~gerth/ae17/slides/certifying.pdf>
- **Stockfish's evaluation is a calibrated statistic, not a game value.** Since SF 16.1/17 the
  displayed evaluation is normalized so that +1.00 corresponds to a 50% *win probability* in
  Stockfish self-play at fishtest's long time control. W/D/L estimates come from a logistic
  model fitted to game outcomes. <https://github.com/official-stockfish/WDL_model>
- **How Stockfish uses tablebases.** It probes WDL tables in search and ranks root moves by
  DTZ and the halfmove clock. A UCI option (`Syzygy50MoveRule`) controls whether 50-move draws
  that Syzygy detects count as draws. Sources: CPW Syzygy page above;
  <https://github.com/official-stockfish/Stockfish/issues/5175>.
- **The prototype** (`prototype/`) used Stockfish plus python-chess to emit a `Cert` for the
  GothamChess mate in 11, and an `onlyMove` checker. Kernel-only checking of the flattened
  320-node proof took about 80 s and about 6 GB. The `native_decide` version also trusts
  Lean's compiler. In Lean 4 core, `native_decide` goes through the `Lean.ofReduceBool` axiom,
  which shows up in `#print axioms`. The prototype's README records this.

### 5.2 Judgment: what Stockfish is good for

The pipeline is: oracle → generator → certificate → Lean `check` → theorem. Lean never sees
Stockfish. The oracle is used in four places:

1. **Choosing attacker moves** in win certificates. Engines are very good at this, and the
   checker validates every choice.
2. **Ordering defender replies** so the most resistant one is tried first, which makes a bad
   certificate fail early in the generator, before Lean ever runs.
3. **Supplying candidate refutations** for "only move" claims: for each alternative, the
   opponent's best answer, which the generator expands into a win, draw, or bounded-survival
   certificate.
4. **Deciding which rung of the ladder (§6) to attempt.** If Stockfish reports a mate score,
   try a win certificate. If it reports a draw-ish score in a simple endgame, try a tablebase
   or trap certificate. Otherwise only bounded claims are realistic.

Stockfish's *numbers* never enter a theorem. A statement like "Stockfish says +2.3" is not a
mathematical claim. Even "m is best by depth-20 minimax under evaluation f" is provable only by
putting f, the NNUE network, inside Lean, and then it says nothing about chess truth. **The
library should not try to verify engine evaluations.** It should prove the strongest
*game-theoretic* statement the oracle's output lets us certify, and record the engine data as
untrusted provenance next to the theorem.

**Tablebases as oracles.** There are two honest options:

- *(a) Verified tables.* Small tables are checked in Lean by the local checker of §3.2.
- *(b) Assumed tables.* Large Syzygy tables enter as an **explicit hypothesis** on the theorem,
  for example `(htb : SyzygySound tb) → …`, never as an `axiom`. The dependence on Syzygy is
  then visible in the statement. It can be discharged later for small material by option (a).

---

## 6. A ladder of approximations to "m is optimal"

Write `v(p)` for the true value in a fixed game (default G∞) from the side to move's
viewpoint, ordered Loss < Draw < Win. The ideal statement is

> **Optimal(p, m)**: `m` is legal and `v(after m)` seen by the mover equals `v(p)`.
> Equivalently, no legal move does better.

That is *WDL-optimal* ("value-preserving"). Finer notions, such as DTM-optimal (fastest mate,
or slowest loss) and DTZ-optimal, break ties within a value class. In a drawn position every
drawing move is WDL-optimal, and "practically best" (most chances against a fallible opponent)
is not a game-theoretic notion. Only the engine can speak to it.

Each rung below is a precise, provable statement with the evidence it needs. Rungs marked
*decidable* can be settled by bounded search. The others need certificates for unbounded
facts.

| # | Statement (sketch) | Meaning | Evidence | Decidable? |
|---|---|---|---|---|
| R0 | `m ∈ legal p` | legal | none | yes |
| R1 | `WinsIn n (after m)` | m forces mate within n moves | win certificate (tree / DAG / ranked set) | yes, for fixed n |
| R2 | R1 ∧ `∀ m', ¬ WinsIn (n-1) (after m')` | m is a **fastest** mate (DTM-optimal for the winner) | one bounded **survival tree** per alternative: a defender reply against every attacker try, to depth n−1 | yes |
| R3 | R1 ∧ `∀ m' ≠ m, ¬ WinsIn N (after m')` for a stated horizon N ≥ n | m is the **only mate within N** | survival trees to depth N | yes |
| R4 | R1 ∧ `∀ m' ≠ m, ¬ Wins (after m')` | m is the **only winning move** | per alternative, one of: opponent win cert (prototype's `onlyMove`), a **trap** (draw cert), or a tablebase leaf | no; needs certificates |
| R5 | `Holds (after m)` ∧ `∀ m', Holds' (after m')` | in a drawn position, m **holds the draw** and nothing wins | trap after m, plus a trap for the opponent after every alternative | no |
| R6 | `NoLossWithin k (after m)` | m does not allow a forced mate within k (**no-blunder certificate**) | survival tree to depth k | yes |
| R7 | R6 for m ∧ `∀ m' ≠ m, opponent WinsIn k (after m')` | within horizon k, m is the **only non-losing move** | R6 tree + win certs | yes |
| R8 | a *strategy* σ on a class C (e.g. all KRK positions), proved value-preserving | **local strong solution** on C | ranking function over C (symbolic proof, or an enumerated table checked as in §3.2) | yes for finite C |
| R9 | any of the above under G₅₀ / G_FIDE | the same claims with the clock | the certificates keyed by (position, clock) | as above |

Notes on the ladder:

- **R1 → R4 is the jump that matters.** R1–R3 and R6–R7 are about bounded horizons and are
  decidable by plain minimax, so they cost only computation. R4 and R5 need *draw evidence*,
  and that is where the research problem is. The prototype reached R4 only in the special case
  where every alternative actually *loses*. Its `onlyMove` refutations are opponent wins. The
  general R4 needs traps.
- **Survival trees are the dual of win trees.** They give one defender move per defender node
  and all attacker moves at attacker nodes, to a depth bound. The same `Cert` datatype with the
  roles swapped could serve, plus a depth-exhaustion leaf. The checker and its soundness proof
  should be written once, for both.
- **R6/R7 are the honest approximation for middlegames.** They say "m is optimal *as far as
  any k-move forcing line can tell*". They are sound, decidable, and grow in strength with k.
  This is exactly the information a tactics puzzle encodes.
- **R8 links to tablebases and textbook technique.** Examples: KQK and KRK mating procedures
  (the Coq KRK work above), Philidor and Lucena positions, and wrong-bishop fortresses
  (symbolic traps).
- **Under G₅₀ the value depends on the halfmove clock.** A cursed win at clock 0 can be a
  draw at clock 60. Every R9 theorem must therefore quantify over, or fix, the clock.

---

## 7. Summary of facts versus judgments

**Established (with sources above):** the FIDE rules of §1.1; Zermelo's theorem as usually
stated, and its history; positional determinacy of finite reachability games via attractors;
the retrograde algorithm; the Syzygy, Lomonosov and DTM/DTZ semantics, including cursed wins
and the absence of castling; proof-number search and GHI; checkers weakly solved; Hurd's
HOL4/BDD verified 4-piece tables; Ambrona's unwinnability algorithm; Stockfish's eval as a
calibrated win probability.

**My judgments (to be challenged):** splitting the semantics into three games (G∞, G₅₀,
G_FIDE); the claims that repetition and dead-position rules never change W/D/L (proof
sketches in §2.4, not yet formalized); tablebases as forward-checkable certificates; traps as
the draw certificate; ranked sets as the uniform win certificate; the ladder R0–R9; and keeping
engine numbers out of theorems.

---

## 8. Recommendations for this library

1. **Separate game theory from chess.** Define a tiny abstract interface, roughly
   `Pos`, `turn`, `legal : Pos → List Move`, `play`, `inCheck`. Define `WinsIn`, `Wins`,
   `Trap`, `Holds`, certificates, checkers and every soundness theorem *once* over that
   interface. Instantiate with chess later. Test the game theory on toy games (Nim,
   tic-tac-toe, a 4×4 "mini-chess") where everything is fast and `decide` works. Determinacy
   proofs never need to know how a knight moves.
2. **Make G∞ the primary semantics.** Its state is board, side, castling, and en passant
   *as legal-move-relevant state*. Win is the inductive `WinsIn` (keep the prototype's three
   constructors and the stalemate exclusion). Holding a draw is `∃ S, Trap S ∧ S p`. G₅₀ is
   added later as `WinsWithin L`, with the theorems `WinsWithin L → Wins` and
   `Wins ↔ ∃ L, WinsWithin L`. Do not model repetition history in the value semantics. Prove
   it irrelevant instead (target theorem, §2.4).
3. **Target theorems for `docs/THEOREMS.md`**, in order:
   - `not_both` (from the prototype)
   - `holds_not_wins : Holds d p → ¬ Wins d.other p`
   - `check_sound` for win certificates
   - `checkSurvival_sound` for bounded survival trees
   - `checkTrap_sound` for draw certificates
   - `checkRanked_sound` for ranked-set and tablebase certificates
   - `minimax_correct`: bounded Zermelo, a decidable `WinsIn n`
   - `dead_not_wins`
   - `wins_iff_exists_within` (G∞ vs G₅₀)
   - stretch: `repetition_irrelevant` and full G∞ determinacy over a closed finite universe.
4. **Shape the ladder as named predicates**: `FastestMate`, `OnlyMateWithin`, `OnlyWin`,
   `HoldsDraw`, `NoLossWithin`, `OnlyNonLosingWithin`. Each gets one checker and one soundness
   theorem. "Optimal" in a theorem name must always say *which* notion.
5. **Use one certificate language, written once, generic in the role of the side.** It needs
   win nodes, survival nodes (depth-bounded), trap references, and tablebase leaves (as an
   explicit hypothesis). Prefer ranked sets or DAGs over trees once transpositions matter. Key
   shared nodes by the legal-move-relevant state (plus the clock under G₅₀), never by raw FEN.
6. **Keep Stockfish and Syzygy outside the trusted base.** They feed a generator script. Lean
   checks. Engine scores are recorded as provenance comments only. Large tables appear as named
   hypotheses (`SyzygySound`), never as `axiom`.
7. **Choose first demonstrations that exercise each rung:**
   - R1/R4: re-prove the prototype's mate in 11 on the new definitions.
   - R2: a fastest-mate puzzle.
   - R6/R7: a famous only-move tactic.
   - R5 with a *symbolic* trap: a wrong-bishop or rook-pawn fortress, where Lean beats engines.
   - R8 via §3.2: a kernel-checked KQK or KRK table.
8. **Trust tiers must be visible.** For each headline theorem, record whether it is
   kernel-only, `native_decide` (`#print axioms` shows `Lean.ofReduceBool`), or conditional on
   an oracle hypothesis. The prototype showed that kernel-only checking is possible but costly
   (about 80 s and 6 GB for 320 nodes). Definitions should stay kernel-reducible so that the
   choice remains open.

---

## Sources

- FIDE Laws of Chess (2023): <https://handbook.fide.com/chapter/E012023>
- Zermelo's theorem: <https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)>
- Schwalbe and Walker 2001: <https://ideas.repec.org/a/eee/gamebe/v34y2001i1p123-137.html>
- Zermelo translation (Rasmusen reader): <https://www.rasmusen.org/GI/reader/notes/19zermelo.1913.txt>
- Reachability games and attractors: <https://www.react.uni-saarland.de/teaching/automata-games-verification-11/downloads/notes10.pdf>, <https://www.logic.rwth-aachen.de/files/LS/LS-chapter2.pdf>
- Bellman, RAND P-3013: <https://www.rand.org/pubs/papers/P3013.html>
- Retrograde analysis: <https://www.chessprogramming.org/Retrograde_Analysis>
- Endgame tablebase metrics: <https://www.chessprogramming.org/Endgame_Tablebases>
- Syzygy bases: <https://www.chessprogramming.org/Syzygy_Bases>
- Syzygy probing semantics: <https://python-chess.readthedocs.io/en/latest/syzygy.html>
- Endgame tablebases and Lomonosov: <https://en.wikipedia.org/wiki/Endgame_tablebase>
- Solving chess: <https://en.wikipedia.org/wiki/Solving_chess>
- Hurd, verified endgame databases: <https://gilith.com/papers/chess.pdf>
- Coq KRK: <https://poincare.matf.bg.ac.rs/~janicic/papers/2012-ceciis-chess.pdf>
- Isabelle chess conjecture: <https://arxiv.org/pdf/1801.07528>
- Proof-number search: <https://www.chessprogramming.org/Proof-Number_Search>
- PNS survey: <https://webdocs.cs.ualberta.ca/~mmueller/ps/ICGA2012PNS.pdf>
- GHI problem: <https://webdocs.cs.ualberta.ca/~mmueller/ghi.html>, <https://cdn.aaai.org/AAAI/2004/AAAI04-102.pdf>
- Checkers is solved: <https://www.cs.mcgill.ca/~dprecup/courses/AI/Materials/checkers_is_solved.pdf>
- Tromp, position count: <https://chessprogramming.org/John_Tromp>
- Fortresses: <https://www.chessprogramming.org/Fortress>
- Ambrona, unwinnability: <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FUN.2022.2>
- Certifying algorithms: <https://cs.au.dk/~gerth/ae17/slides/certifying.pdf>
- Stockfish WDL model: <https://github.com/official-stockfish/WDL_model>
- Stockfish Syzygy and the 50-move counter: <https://github.com/official-stockfish/Stockfish/issues/5175>
- Prior prototype: `prototype`
  (`ChessProof/Cert.lean`, `README.md`)
