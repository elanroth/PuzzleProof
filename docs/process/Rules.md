# Process log: `Chess.Rules`

The record of the back-and-forth between the English specification (`docs/spec/Rules.md`) and the
Lean (`Chess/Rules.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written in the library: none.

**Inputs read.** `docs/DESIGN.md` (whole file; §5, §4.5–§4.6, §6.4, §7.4, §8.3 most closely),
`docs/THEOREMS.md` (§0, §1, R1–R11, §9), `Chess/Basic.lean` and `Chess/Position.lean` (whole files),
`docs/spec/Position.md` (conventions, D3.1's `promo` promise, §8–§10), `docs/process/Basic.md` and
`docs/process/Position.md` (format and open items), `docs/reviews/Basic.md` and
`docs/reviews/Position.md` (items addressed to `Rules`: Position C1, C2; Basic C2, C4, C8),
`docs/research/representation.md` (§2.4, §2.5, §5) and `docs/research/lean-engineering.md`
(§5 pitfalls, §9, §10).

**What the draft fixes.** 35 definition entries (D1.1–D6.3, with their `Decidable` instances) and
about 54 lemmas in 38 table rows (L1.1–L9.3; L4.6 is a family of pairwise exclusions), in ten file sections: Board helpers; Reaching and attacking;
Shapes of moves; Movement rules; Playing a move; Legality and terminal positions; What a move
changes (R4, R8); Sanity theorems (R5); Terminal positions (R11); Tests.

**Facts checked in Lean 4.28 before writing them down.** Every definition, instance and test, and
all lemmas but L2.8, L4.5, L4.6, L8.3 and three rows of L7.8, were translated into scratch files
importing the built `Chess.Position` (scratchpad only, nothing in the library). The final scratch
file elaborates with no errors in about 6 s. Along the way:
- Core 4.28 decides `∃ i, i < 8 ∧ P i` (`Nat.decidableExistsLT`) and `∀ j, j < i → Q j`
  (`Nat.decidableBallLT`); the slider clause needs the binders in that order.
- In a `match` arm shared by several constructors (`| .bishop | .rook | .queen => …`), `k` is the
  matched constructor: `Reaches .bishop c b s t ↔ ∃ d ∈ Direction.diagonals, Slides d b s t` is
  `Iff.rfl`.
- `by unfold X; infer_instance` gives working instances for every predicate, under `decide` and
  `decide +kernel`. `decide` proves `Legal Position.initial e2e4` in about 0.25 s.
- **Measured: the derived instance of `CastleMove` loses short-circuiting in compiled code.**
  Deciding `PseudoLegal` for all 20 480 candidate moves of the initial position took 36 s
  interpreted, nearly all of it `InCheck p` and the attack test, evaluated for every candidate. A
  minimal pair isolated it: `m.IsCastle p w ∧ InCheck p` with a derived instance, 17.5 s; the same
  with `if h : m.IsCastle p w then … else isFalse …`, 21 ms; `m.src = kingHome p.turn ∧ InCheck p`
  derived, 0.29 s. The cause inside the compiler was not pinned down. With the hand-written instance
  of D4.6, the sweep takes 0.46 s, and deciding `Checkmate` for Fool's mate 1.4 s (78 s before).
- `play` as write lists (design choice 7) does not show Position review C1's exponential cost:
  32 chained plies with a legality test each, 0.19 s; a full legality sweep four plies deep, 1.4 s.
- The legal-move counts of the scratch rules agree with chess: 20 from the initial position, 20
  after 1. f3, 19 after 1. f3 e5, 0 in Fool's mate.
- Castling (f1 attacked forbids O-O; b1 attacked does not forbid O-O-O), en passant (target after
  d7d5, capture legal, victim removed), promotion (a choice required on the last rank and forbidden
  elsewhere) and the rook-capture revocation (b7xa8=Q costs Black `q` and keeps `k`) all behave as
  FIDE says (§10 tests).
- Two traps written into the spec: after `cases k` the goals are in constructor order, not in the
  order of the `match` (use `case pawn => …`); and in `congrArg Square.rank e` with `e : m.dst =
  m.epVictim`, unification against `m.dst.rank ≠ m.src.rank` fails; `by rw [e]; rfl` works.

**Decisions taken in the English, beyond DESIGN** (each argued in spec §11):
1. `Slides d b s t` names the slider clause, in index form; "the square `j` steps away is empty" is
   `(s.shift d j).bind b = none` (settles DESIGN §10's first open item).
2. `Board.colorAt` and `Board.kindAt` helpers; "does not hold a piece of its own colour" is
   `colorAt dst ≠ some c`.
3. `StepMove` quantifies over the kind (`∃ k`); `Attacked` reads the kind off the board.
4. A third shape predicate, `Move.IsDoublePush`, shared by `DoublePushMove` and step 5.
5. `Move.PromotionRule c m := m.promo ≠ none ↔ m.dst.relRank c = 7`, and a sanity theorem L8.3 that
   keeps Position D3.1's promise about `promo` in both directions.
6. `play` as six named steps, steps 1–3 as lists of writes carried out by a new `Board.setMany`;
   every step reads the position before the move; `Move.touched` is the write list's squares.
7. **Departure from DESIGN §5.5 step 4:** rights are revoked by squares (`Move.Revokes`: the move
   leaves or lands on `kingHome c` or `rookHome c w`), not by reading whether `src` holds a king.
   Argued faithful in spec §11 item 8; flagged for the critic and the owner (spec §12 item 1).
8. `CastlingRights.ofGet`, so step 4 is "held after exactly when held before and not revoked",
   and R8 is two lines.
9. `CastleMove.decidable` hand-written (the measurement above).
10. R5 names `PseudoLegal.isLight_dst_iff_of_bishop` / `_of_knight` with `kindAt` hypotheses,
    instead of THEOREMS' `bishop_keeps_colour` / `knight_flips_colour`.

**Questions for the translator and the critic** (spec §12 lists them with context):
- Is step 4 by squares acceptable, or should it follow DESIGN's "if `src` holds a king"?
- Is `Board.setMany` with write lists clearer than a chain of named `Position → Position` steps?
- Should `StepMove` read the kind off the board (a `match`) like `AttacksFrom`, for uniformity, at
  the cost of `split` in proofs?
- Is `Move.PromotionRule` the right name (alternatives: `PromotesOnLastRank`, `PromoFits`)?
- Should `Slides` be named `SlidesTo`, or live in the `Board` namespace?

**Open items for others (not edited, outside this module's files).**
- Owner, before the translation: Basic review C2 (pawn direction as a `Direction`) changes the pawn
  arm of `Reaches` and four pawn rules; Position review C1 and C2 do not block this module.
- Basic, next revision: `rookCastleSquare_ne_kingHome`, `kingCastleSquare` injective in the wing,
  `Color.forward_ne_zero`.
- THEOREMS: R4's `play_board_dst` (`map` form) and three new R4 rows; R5's names; R3's `Attacked`
  sketch quantifies over kinds; L8.3 new. DESIGN: §5.5 step 4 (decision 7) and §5.4
  (`IsDoublePush`).

**Next.** Round 2: translation into `Chess/Rules.lean`, then a critique of the English against the
Lean.

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator, answering the Round 1 English critique (A1–A8, B1–B10,
C1–C6, D1–D3, E1–E2). Every item was taken; none was rejected. Lean written in the library: none
yet at the time of this round.

**[A] Statements that were false or overclaimed.**
- **A1 (en passant "cannot produce a capture FIDE forbids").** False, as the critic showed (a target
  left over from ten moves ago). D4.5's note now says a hand-written target can only produce a
  capture that *some* previous move would justify, and that FIDE 3.7.3.2's "immediately after" is
  enforced by `play`, which clears the target after every move that is not a double push.
- **A2 (the two revocation rules "differ only when…").** Design choice 8 adds the second case: a
  king captured on its home square (only from a position where the side not to move is in check).
- **A3 (python-chess cited as a square-only precedent).** Checked: python-chess's `push` clears
  rights by the from and to squares *and* clears all of the mover's rights on a king move, which
  reads the piece type. Stockfish's `castlingRightsMask[from] | castlingRightsMask[to]` is the
  square-only precedent; design choice 8 now cites it and says how python-chess differs.
- **A4 (L7.6 said four facts, the Lean one).** "The square a castling rook lands on is not a king's
  home square."
- **A5 (eight adjacent squares, two diagonals).** "(up to eight)", "(at most two)" in D2.2's
  docstring and L2.2.
- **A6 (L2.1 could be read as requiring `t` empty).** "…with every square strictly between `s` and
  `t` empty."
- **A7 (order of writes).** §5's intro now names squares written twice, including by step 1 itself
  when `m.src = m.dst`.
- **A8 (L2.7 vacuous).** Kept, because the terminal facts of B2 need it, retagged [core], with a
  sentence saying it checks nothing about attacks. The positive companions are tests (§10, "Attack
  geometry"): a lone rook on e8 attacks the king on e1; a pawn on e4 blocks it. A general form,
  L2.9 `not_kingAttacked_of_forall_ne`, was added.

**[B] Hidden choices made explicit.**
- **B1.** D4.6 gained a note on when the three castling attack tests are read, and why reading the
  crossed square before the move and the landing square after it agrees with FIDE's before-the-move
  reading. §0's "position before the move" rule now names `Legal` as its one exception.
- **B2.** A paragraph after D6.3 states the four facts about kingless sides; three became lemmas
  (L9.4 `not_inCheck_of_forall_ne`, L9.5 `not_checkmate_of_forall_ne`, L9.6
  `stalemate_of_board_eq_empty`), and the fourth, "every pseudo-legal move is legal", is L9.7,
  tagged [later].
- **B3.** "a king of the side to move is attacked" (D2.6), "no king of the mover's colour is
  attacked" (D6.1, L9.3), "A king of colour `c`" (D2.5 and its instance). §0 gained a rule about
  this wording.
- **B4.** D2.2's docstring opens "would reach `t` from `s` … whatever actually stands on `s`";
  "attacks" is kept for D2.3 and D2.4, and L2.2–L2.3 say "reaches". A note explains why the
  relation is hypothetical (the super-piece method).
- **B5.** D2.1 and D2.2 say "up to and including the first occupied one" and that `t` may be
  occupied.
- **B6.** D2.2 note: en passant captures are not attacks, and why that never matters for check.
- **B7.** D2.2 now cites 3.1.3, 3.2–3.4, 3.6, 3.7.3, 3.8.1, 3.9.1 and says the target need not be an
  opponent's piece, which is what 3.9 needs. §0's FIDE list says 3.1.2 is about attacks on an
  opponent's piece.
- **B8.** D5.6's docstring says why landing on the rook's home square revokes the right.
- **B9.** D5.3 gained "(If that square is empty, the crossed square becomes empty.)"; D5.1 gained
  "whatever its kind".
- **B10.** D3.3 states that among pseudo-legal moves exactly the double pushes have the shape, and
  this is a new lemma, L4.7 `PseudoLegal.isDoublePush_iff`, tagged [core] (step 5's target is then
  set exactly after double pushes).

**[C] Binding rule and wording.**
- **C1.** §0's binding rule now allows a docstring to introduce a name itself ("for some `i`", "for
  each wing `w`"). D2.1 says "for some number of steps `i`"; D5.3 "for each wing `w`, if `m` has the
  shape of castling to `w`"; D5.7 "for every colour `c` and wing `w`"; D1.3 no longer names `s` and
  `x` ("each write, a pair of a square and its new contents").
- **C2.** L7.3, L7.4, L7.5 and rows 3–5 of L7.8 speak of "a move with the shape of …"; a sentence
  after L7.8 says no pseudo-legality hypothesis is needed for them. §0 gained a "shape and rule"
  rule.
- **C3.** "one piece" (D3.1 note); "moves a pawn" (D3.1, D3.3 docstrings); D4.5's docstring names
  the victim square by its position beside the capturing pawn and says "one square further forward
  than the target, from the capturer's side".
- **C4.** L8.1, L8.2 speak of the *shade* of a square.
- **C5.** D3.5's docstring drops "and no other move may"; the note says the other four rules carry
  that half.
- **C6.** Every instance docstring names its predicate.

**[D] Places where the translator would have had to guess.**
- **D1.** `play_epTarget` uses the folded form `= m.epTargetAfter p`, like `play_castling`.
- **D2.** `StepMove` keeps its name (the task names it); its docstring opens "A step move is any
  non-pawn move other than castling", and the note says a slider's step is a slide of any length.
- **D3.** D2.1's note cites Basic's `shift_eq_none_of_eight_le`.

**[E] Tests.**
- **E1.** `castlePos` has rights `⟨true, true, false, false⟩` and expects `CastlingRights.none` after
  e1c1; `promoPos` gains a black rook on h8, has rights `⟨false, false, true, true⟩`, and expects
  `⟨false, false, true, false⟩` after b7a8=Q. §10 opens with the rule that test rights must be ones
  FIDE could grant.
- **E2.** New tests: en passant exposing the king along the rank (`epPinPos`, b5c6 pseudo-legal but
  not legal); castling out of check (`castleCheckPos`); castling through an attacked d1
  (`castleD1Pos`); a stale target one full move after the double push; adjacent kings; a knight
  move with a promotion choice.

---

## Round 3: translation feedback

Date: 2026-11-01. Author role: translator. Lean written: `Chess/Rules.lean` (129
declarations, each with its spec docstring; 1 057 lines with the tests), and `import Chess.Rules`
added to `Chess.lean`. `lake build` succeeds with no errors, no warnings, no `sorry` and no
`native_decide`; the module elaborates in about 6 s, most of it the `#guard` on Fool's mate and
the `decide` tests. Exactly the six lemmas §13 lists carry `@[simp]`. Every [core] and [sanity]
lemma is proved; of the [later] lemmas, L2.8 (`slides_symm`) and the kingless-side fact (now
L9.7–L9.8) were proved as well, and only L4.6 (M5's pairwise exclusions) is left for Stage 2.
Nothing is marked `-- TARGET:`. A script compared the two files: every English sentence of every
table row and every definition docstring of the spec occurs word for word as a Lean docstring, and
every Lean docstring occurs in the spec, except the test positions' (covered by §10's new rule).

`#print axioms`: `castling_play_le` (R8) and `stalemate_of_board_eq_empty` use only `propext` and
`Quot.sound`; the R4 lemmas, `slides_symm`, `reaches_set_dst`, L4.7 and L8.3 also use
`Classical.choice`, through `by_cases`, `omega` and `simp`. This is a fact about the proofs, not the
statements; nothing in the English depends on it.

The places where the Lean forced a decision the English had not made, or where the translation was
awkward, and what changed in the spec:

1. **`CastlingRights.get_ofGet` had no English.** The spec mentioned it only inside L7.9's proof
   note, but it is a `@[simp]` theorem on §13's list and needs a docstring. *Spec change:* a table
   after D5.7 with row L5.1 ("The rights built from `f` hold `c`'s right on `w` exactly when `f c w`
   is true.").
2. **L2.8 is two theorems.** The symmetry proof is one direction applied twice, and that direction
   is worth naming (`Slides.symm`, usable with dot notation). *Spec change:* L2.8 is a two-lemma row;
   the proof note gives the `Nat.sub_sub_self` step and the `simpa` that removes
   `d.opposite.opposite`. Tag "later (R3), proved".
3. **The kingless-side lemma (B2) turned out cheap, but needed a list fact the English lacked.**
   "Every pseudo-legal move is legal for a side with no king" needs "after the writes, a square
   holds its old contents or a written value". *Spec change:* new L1.7 `Board.setMany_eq_or_mem`;
   the old L9.7 is split into L9.7 `play_board_ne_king_of_forall_ne` (true for every move, not only
   pseudo-legal ones, which the English now says) and L9.8 `legal_iff_pseudoLegal_of_forall_ne`,
   both [core] and proved. The B2 paragraph after D6.3 cites L9.8.
4. **Instance docstrings written with an ellipsis.** Round 2 wrote "likewise '… is a push …'" for
   D4.2–D4.5, which the translator had to expand. *Spec change:* all five are written out.
5. **L7.8's src and dst share their proof.** The plan proved each separately; in Lean both are "steps
   2 and 3 do not write this square, so it holds what step 1 wrote". *Spec change:* the proof note
   records the two `private` helpers (`play_board_of_not_mem_rest`, `PseudoLegal.not_mem_rest`),
   their docstrings, and a trap: destructuring `IsCastle` with `-` drops the king-on-source fact
   that `castleWrites_of_isCastle` needs. §13 now says proof-only helpers are `private` and carry a
   docstring.
6. **L8.3's double-push case.** `relRank_of_offset_forward` must be given `dr := 2` (it is not
   found by unification against `2 * p.turn.forward`), and the leftover `((7 : Fin 8) : Int) = 3`
   is closed neither by `simp` nor by `omega`; `revert h3; decide` closes it. *Spec change:* proof
   note.
7. **Lean scopes.** The English gave each table a `variable` line but, for §3 and §8–§9, no scope.
   The translation uses `section Shapes`, `section Sanity` and `section Terminal` beside the named
   `Reaching`, `Movement`, `Play`. *Spec change:* §13 lists the scopes.
8. **Two castling test positions differing in one square.** Round 2 described `castleCheckPos` and
   `castleD1Pos`; the Lean writes one `castleRookPos (f : Fin 8)` with the black rook on the seventh
   rank of file `f` (e7 gives check; d7 attacks d1). *Spec change:* §10 describes the one
   function.
9. **Test positions are definitions, so they need docstrings.** The English gave none. *Spec
   change:* §10 says each named position has a docstring listing pieces, side to move and rights,
   with an example; the adjacent-kings position is named `kingsPos`.
10. **The stale-target test checks two plies.** The English said "after e1d1 and e8d8 the target is
    `none`"; the Lean checks the target after the first ply (where it is cleared) and the
    illegality after the second (when White is to move again). *Spec change:* §10 says exactly
    that.

Checked and needing no change: every definition, instance and the tests elaborated as Round 2
wrote them; the hand-written `CastleMove.decidable` and `by unfold X; infer_instance` instances work
under `decide` and `decide +kernel`; all Round 2 tests pass, including the new ones: en passant
along the rank (`epPinPos`: b5c6 pseudo-legal, not legal), castling out of check, castling through
an attacked d1, adjacent kings, a knight move with a promotion choice, the positive and blocked
`KingAttacked` checks, and the corrected rights in `castlePos` (`CastlingRights.none` after e1c1)
and `promoPos` (`⟨false, false, true, false⟩` after b7a8=Q). `play_epTarget` in the folded form is
`rfl`.

**Still open for others** (spec §12): the owner's decision on step 4 by squares (item 1, now citing
Stockfish rather than python-chess), Position review C1 and C2, Basic review C2, the Basic additions
(`rookCastleSquare_ne_kingHome` is still proved here as L7.6), and the THEOREMS edits (item 6), to
which L4.7, L9.4–L9.8 and the new R5 wording should be added.

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner, applying the Lean critique of Round 3 (sections 1–3 and its
six recommended edits). Files edited: `Chess/Rules.lean`, `docs/spec/Rules.md`, `docs/THEOREMS.md`
(R3, R4, R5, R8, R9, R11, M2, the Stage 1 table, decision 5), `docs/DESIGN.md` (§5.5 step 4 and the
R8 row). `lake build` succeeds (6 jobs) with no errors, no warnings, no `sorry`, no
`native_decide`; the module elaborates in about 8 s. The `@[simp]` set is unchanged. A script again
checked that every Lean docstring occurs word for word in the spec (test positions excepted, as §10
allows) and that every theorem statement in the spec's tables occurs in the Lean (L4.6 and L4.11,
not proved, excepted). Regression: the critic's scratch tests (20 legal moves initially; blocked
double push; Black O-O; Black promotion; pinned bishop) and perft (position 3: 14 and 191;
position 4: 264) give the same numbers after the refactor.

### English first: what was wrong or vague, and what changed

1. **`EnPassantMove`'s docstring omitted "the target is empty"** (critique 1.1). Now "onto the en
   passant target, which is empty and lies on its sixth rank". Lean docstring changed to match; the
   definition is unchanged.
2. **`Reaches` and `Attacked` did not say that en passant is left out** (1.3). `Reaches` now says
   "En passant aside, these are the squares the piece could capture on"; `Attacked` says "En passant
   captures are not counted; they never capture a king." The D2.2 note adds why castling is
   unaffected either (the crossed square is never an en passant target).
3. **D4.5's "some previous move would justify" overclaimed** (1.4). Now "some previous double push
   would explain", and whether that push was itself legal is `WellFormed`'s business.
4. **D4.6's castling-timing argument was imprecise** (1.2). Emptying e1 also opens the e-file and
   e1's diagonals; the note now says so and why they miss the landing square, names the rook's home
   square (a corner, so it opens no line to the landing square), and the rook's side (empty before
   and after). A first draft of this rewrite claimed something about lines through the rook's home
   square that was not needed and not quite right; it was corrected before the round closed. The
   argument is still not a theorem, so it is now **L4.11** [later, fidelity],
   `CastleMove.legal_iff`, listed in §12 item 8 as the one thing to prove before calling the module
   final.
5. **D5.4's note said `++` associates to the right. It associates to the left** (`infixl:65`).
   Found while proving `touched_nodup` (the first `nodup_append` split step 1 + step 2 from step 3).
   Corrected; proofs that split off step 1 now use `List.append_assoc` first. Round 3's
   `show … ++ (… ++ …)` had only worked because `pieceWrites` reduces to a literal.
6. **New English, then Lean, for every new name:** `Board.HasKing` (D2.5a), `Position.CanCastle`
   (D4.6a, with the new short `CastleMove` docstring "shape, permission, no promotion choice"),
   L1.6a, L2.4 (`reaches_congr` row), L2.6a, L4.8–L4.11, L7.7a, and the four `private` §4 helpers.
   Each docstring was written in the spec first.
7. **Position's `CastlingRights` convention is now false** (1.5). Not edited: it is Position's
   file. Spec §12 item 7 asks Position to restate it as "`play` changes rights only through
   `Move.castlingAfter`, which can only clear them" and to take `ofGet`; design choice 10 says the
   same.
8. **Design choice 8 (revoking by squares)** (1.7). The critic agreed it is faithful; DESIGN §5.5
   step 4 now states the square rule, with the old rule quoted and a pointer to spec §12 item 1 for
   reverting. The owner keeps the last word.

### Then the Lean

- **`reaches_congr`** (2.1): one lemma, "two boards that agree off `s` and `t` give the same
  answer", which is DESIGN §5.2's sentence. `reaches_set_src` and `reaches_set_dst` are now one
  line each. L2.4 retagged [core].
- **`Board.attacked_iff`** (2.2): R3's definition of "attacked", proved in 9 lines; the definition
  keeps reading the kind off the board.
- **`Position.CanCastle`** (2.3): the move-independent castling conditions. `CastleMove` is three
  conjuncts, and `CastleMove.decidable` is
  `decidable_of_iff (p.CanCastle w ∧ m.promo = none) (and_iff_right h).symm`: no restated
  condition and no `simp`. Two destructuring patterns changed (`colorAt_dst_ne`,
  `promo_ne_none_iff`); both are shorter.
- **The compiled-`∧` question** (end of 2.3), measured on the 20 480 candidates of the initial
  position (interpreted): "castles to some wing" with the hand-written instance under 0.1 s; with a
  derived instance for `IsCastle ∧ CanCastle ∧ promo = none`, 0.19 s; with a derived instance for
  `IsCastle ∧ InCheck p`, 35 s. `Legal`'s derived instance short-circuits: 0.47 s for the legal
  sweep against 0.46 s for `PseudoLegal`, while the post-move test alone, run for every candidate,
  takes 22 s. So the slowdown appears when an attack test is a *direct* conjunct of a derived
  instance. The compiler mechanism is still not identified (core's `instDecidableAnd` is
  `@[macro_inline]`). The guard is kept, and §13 now says never to put an attack test directly in a
  derived instance that is decided for every candidate.
- **`private Color.forward_ne_zero`, `Color.two_mul_forward_ne_zero`** (2.5) replace the four
  `cases p.turn <;> decide`.
- **`Board.HasKing`** (2.6); the kingless lemmas renamed to `not_kingAttacked_of_not_hasKing`,
  `not_inCheck_of_not_hasKing`, `not_checkmate_of_not_hasKing`, `not_hasKing_play` (was
  `play_board_ne_king_of_forall_ne`, now stated with `HasKing` on both sides) and
  `legal_iff_pseudoLegal_of_not_hasKing`.
- **Renames** (2.7): `Move.enPassantWrites_of_not_isEnPassant`,
  `Move.castleWrites_of_forall_not_isCastle`. `StepMove` kept (spec D2 and the task name it;
  `PieceMove` noted as an alternative for the owner).
- **Brittle proofs** (2.8): `promo_ne_none_iff`'s step case is `simp [hpr, hs, hk]` (was an 8-lemma
  `simp only` plus an `exact`); `not_hasKing_play` no longer splits on a four-way `rcases` of simp's
  normal form. One `simpa` names step 1's write, `Option.map_eq_some_iff` names the source's
  piece, and a `cases` on `m.promo` finishes. `Piece.kind_promote_eq_king` turned out not to be
  needed (§12 item 5 lists it as optional for Basic).
- **Bridge lemmas** (§3): `PseudoLegal.isEnPassant_iff` (L4.8), `PseudoLegal.isCastle_iff` (L4.9),
  `PseudoLegal.attacksFrom_dst` (L4.10), `Board.setMany_of_mem` (L1.6a),
  `PseudoLegal.touched_nodup` (L7.7a). With the last two, `play_board_src` and `play_board_dst` are
  one line each, and the private helper `play_board_of_not_mem_rest` is gone
  (`PseudoLegal.not_mem_rest` stays, private, inside `touched_nodup`'s proof). The isCastle proof
  needed one fact Basic lacks, `shift_kingHome_one_ne` (a king step never reaches the castling
  square), proved by `decide` as a private helper. `isEnPassant_iff` needed
  `Square.file_eq_of_offset_zero`, also private.
- **Tests** (2.10): `#guard` that the initial position has 20 legal moves; e2e4 blocked by a piece
  on e3; Rh1h2 on `castlePos` clears only `K`; `blackCastlePos` (e8g8 legal, rook to f8);
  `blackPromoPos` (a2a1=N legal, a2a1 not); `pinPos` (Be2d3 pseudo-legal, not legal).

`#print axioms`: `Board.attacked_iff`, `isCastle_iff`, `attacksFrom_dst` and
`legal_iff_pseudoLegal_of_not_hasKing` use only `propext` and `Quot.sound`; `reaches_congr`,
`isEnPassant_iff`, `touched_nodup` and `play_board_dst` also use `Classical.choice`, through
`simp`, `omega` and `by_cases`.

### Considered and not done

- **Prop-valued structures with named fields for the rules** (2.4). Deferred to the M2/M5 work
  (design choice 14). `CanCastle` already cut `CastleMove` from seven conjuncts to three, and
  positional patterns break at build time, not silently.
- **A named `Board.EmptyAt?` for `(o).bind b = none`** (2.9). Not added: spec §0 already explains the
  idiom, every use has a docstring saying "is empty", and one more definition is one more layer for
  `simp` to unfold. Revisit if a later module uses the idiom outside a docstring-ed definition.
- **R6 (`boardWrites_flip`)** and **L4.6** (exclusivity): Stage 2, unchanged.
- **Function-board read cost** (end of §3): no change in this module. It is one more reason to put
  the packed layer behind a refinement theorem rather than evaluate long games on function boards.

### Still open for others

Spec §12: the owner's final word on step 4 by squares (item 1); Position review C1 and C2 (items 2
and 4); Basic review C2 (item 3); Basic additions (item 5); DESIGN §5.4 does not yet mention
`IsDoublePush` or `CanCastle` (item 6); Position's `CastlingRights` convention and `ofGet` (item
7); L4.11 (item 8).
