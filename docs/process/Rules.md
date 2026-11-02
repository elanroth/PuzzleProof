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


---

## Note, 2026-11-02 (test library round, ROADMAP step 3): the tests moved to `ChessTest/Rules.lean`

The section "Tests" (the examples, the `#guard`s and the thirteen named test positions with their
docstrings) moved verbatim to `ChessTest/Rules.lean` in the new test library `ChessTest`
(`lake build ChessTest`, not a default target). It was about 3.3 s of this module's 3.6 s build
(measured: 3.65 s with the section, 0.39 s without, `lake env lean`), paid again by every module
that imports Rules. The module keeps four cheap `#guard`s under `/-! ## Tests -/` (no check in the
initial position, e2e4 legal, e2e5 not, the target after e2e4), with a pointer. Spec §10 now says
where the tests live and quotes the four `#guard`s; the rest of §10 specifies the test file. No
definition, docstring or proof of the library changed. Clean build of the module: 3.6 s before,
0.4 s after.

---

## Round 5: L4.11 and the review's naming and shape decisions (ROADMAP step 4)

Date: 2026-11-02. Author role: overnight agent, ROADMAP step 4. Files edited: `Chess/Rules.lean`,
`Chess/Basic.lean` (four geometry lemmas, logged in `docs/process/Basic.md`),
`ChessTest/Axioms.lean` (two entries), `docs/spec/Rules.md`, `docs/spec/Basic.md`,
`docs/spec/MoveGen.md`, `docs/spec/ChessTest.Axioms.md`, `docs/DESIGN.md`, `docs/THEOREMS.md`,
`docs/ROADMAP.md`. `lake build` green (11 jobs), no warnings from `lake env lean Chess/Rules.lean`,
no `sorry`, no `native_decide`, all lines at most 100 characters. The docstring check (Rules review
C8's script, run from a scratch directory) finds all 145 Lean docstrings of this module in the spec
(136 before the round, all found then too); Basic's count of paraphrased lemma docstrings is
unchanged (78 of 192, none of them new).

### L4.11 proved: `CastleMove.legal_iff`

English first. Spec §7a (new, so that §8–§13 keep their numbers) states six lemmas: L7a.1
`CastleMove.pseudoLegal`; L7a.2 `CastleMove.play_board_of_ne` (castling changes only `K`, `G`, `R`,
`F`); L7a.3 what those four squares hold after the move; two `private` helpers, L7a.4 (an attack
after castling on a square holding a king of the mover was an attack before) and L7a.5 (an attack
on `G` before castling is an attack after); and L4.11 itself, whose row in §4 now has the exact
statement. §2 gained L2.4a, `reaches_of_clear`, the one-way transfer of a reach between boards. The
D4.6 note, §12 item 8 and the spec's status line now say L4.11 is proved.

Then the Lean, in a new section `/-! ## The castling landing square (L4.11) -/` after `section Play`
(the lemmas need `play`'s R4 lemmas and `Legal`). About 140 lines including docstrings.

- **No one-king hypothesis.** Rules review C2 guessed none would be needed; it is not. The
  argument (spec §7a): the other colour's pieces do not move, leapers read no board, the rook's home
  square is a corner (strictly inside no line, Basic B5.16a–b), and a line through the king's home
  square (emptied) or the crossed square (filled) strictly inside it runs along the home rank
  (B5.16a), where the crossed square, resp. the king's home square, is an end of the segment or
  strictly inside it (B5.16c) and blocks.
- **Sharper than the statement.** The landing square is attacked after castling exactly when it was
  attacked before, without `¬ InCheck p`. That hypothesis only handles a second king of the mover.
- **`reaches_of_clear` instead of `reaches_congr`.** The two boards differ on squares strictly
  between attacker and target, so `reaches_congr` does not apply. The new lemma's hypothesis may
  use that the whole line is clear on the first board, which is exactly what rules out the emptied
  king's home square (its neighbour on the line is occupied).
- **Name clash.** Inside `CastleMove.play_board_rookCastleSquare` the unqualified
  `play_board_rookCastleSquare` names the lemma being defined (Lean reported a structural recursion
  failure); the proof writes `Chess.play_board_rookCastleSquare`.
- **`obtain … := h` clears `h`**, which later lines still needed (`h.pseudoLegal`,
  `h.play_board_of_ne`). Where `h` is used again the facts are taken out by projection with their
  types written (`have hR : p.board (rookHome p.turn w) = some ⟨p.turn, .rook⟩ := h.2.1.2.1`).
- `#print axioms`: `CastleMove.legal_iff` uses `propext`, `Classical.choice`, `Quot.sound`;
  `reaches_of_clear` uses `propext`, `Quot.sound`. Both are now in the axioms ledger
  (`ChessTest/Axioms.lean`, 120 entries; 128 with the perft file).
- Elaboration cost: `lake env lean Chess/Rules.lean` takes 0.41 s wall clock after the round. No
  `decide` is used in the new Rules proofs; Basic's B5.6a and B5.16a–b use it for finite case
  checks.
- Tests: two examples in `ChessTest/Rules.lean` (after the `rookAttackedPos` tests) decide e1g1
  through `CastleMove.legal_iff`, deciding only `CastleMove` and the attack on g1 before the move;
  spec §10 lists them. `lake build ChessTest` is green; `ChessTest.Rules` builds in 3.5 s.

### Rules review C5: `StepMove` renamed `PieceMove` (adopted)

The definition, its instance, `PseudoLegal`'s body and docstring ("it is a piece move, a push, …"),
L4.4 (`PseudoLegal.pieceMove_of_kindAt`) and a comment in L8.3's proof. Six occurrences in the
Lean, none outside this module (MoveGen takes the rules apart by pattern, not by name; `ChessTest`
does not name it). Current text renamed in specs Rules and MoveGen, DESIGN and THEOREMS; process
logs and reviews keep the old name, as history. Reason: "step" was wrong for a slide of any length,
and "piece move" is the chess player's word for a non-pawn move. The docstring keeps its first
sentence ("A piece move is any non-pawn move other than castling"), because FIDE's own Article 2
counts pawns among the pieces. The other parts of C5 (namespace convention in DESIGN §2, moving
helpers to Basic and Position, Position's `CastlingRights` docstring) are not done; spec §12 item 9.

### Rules review C1: structures (not adopted)

Weighed and declined; spec design choice 14 has the full reasons. In short: anonymous-constructor
and `rcases` patterns on a structure are positional too, so the brittleness the review names would
not go away without rewriting the proofs to field names; seven hand-written `decidable_of_iff`
instances would restate trusted text that the derived instances now do not; and M2, M4 and L4.11
were proved against the conjunctions without friction. To revisit if L4.6 (M5) is painful.

### Basic review C2: `Color.pawnDirection : Direction` (not adopted)

Decided here because it changes this module's trusted definitions (spec §12 item 3 has the
reasons): the predicted cost ("every pawn proof starts with `cases c`") did not appear; captures
would stay offsets, so pawn moves would mix `shift` and `offset`; six trusted definitions,
MoveGen's pawn targets and their proofs would change for a nicer double push.

---

## Round 6: review fixes for Round 5

Date: 2026-11-02. Author role: overnight agent, fixing the review of Round 5 (L4.11). Files edited:
`Chess/Rules.lean`, `Chess/Basic.lean` (one lemma, logged in `docs/process/Basic.md`),
`docs/spec/Rules.md`, `docs/spec/Basic.md`, `docs/process/Rules.md`, `docs/ROADMAP.md`.

Wording, all in spec §7a and §4–§8 proof notes unless said:
- **Where `decide` is used.** §7a said the proof uses no `decide` and that B5.16a–c are proved by
  `omega`. Wrong for the round as a whole: B5.6a is `cases d <;> cases d' <;> decide`, and B5.16a–b
  turn a `Fin 8` literal into a number with a small `decide` before `omega`. §7a now says "no
  `decide` in this section" and names both. Round 5's log above is corrected the same way.
- **Length of L4.11's proof.** "Two lines on top of them" became "a short proof (about a dozen
  lines; the extra work is the second-king case)".
- **Axioms.** The parenthetical blaming `simp` and `by_cases` for `Classical.choice` was a guess.
  `#print axioms` shows that B5.16a–c each use `propext`, `Classical.choice`, `Quot.sound`, so the
  spec now says the axioms come in through them as well.
- **"Step" after the rename.** L4.2, L4.3, L4.10 and L8.3 still called the piece-move rule "step";
  now "piece move". (`play`'s numbered steps keep the word.)
- **The sharper fact is not exported.** §7a now says so: L7a.4 and L7a.5 are `private`; promote
  them if Stage 2 needs the statement.
- **Docstring count.** Round 5's header now reads "(136 before the round, all found then too)".
- **ROADMAP step 4** no longer says this removes "the last literal-fidelity gap": it closes the
  one gap the D4.6 note flagged; the en passant readings in the fidelity assessment are separate.

Lean, the optional readability nit, taken because it was cheap:
- `Color.homeRank_eq_zero_or_seven` (Basic B6.3a, "A home rank is the first or the last rank.")
  replaces three inline `(by cases p.turn <;> simp)` in L7a.4 and L7a.5. One lemma about the home
  rank, rather than one per home square as the review suggested, because each home square's rank
  is `c.homeRank` by `rfl` (Basic B7.2), so the same term fits all three call sites.
- `Position.CanCastle.not_inCheck` (L7a.1a, "A side that may castle is not in check.") replaces
  `have hcheck : ¬ InCheck p := h.2.1.2.2.2.1` in L4.11 by `h.2.1.not_inCheck`. Design choice 14's
  last bullet now cites it. The two other projections into `CanCastle` in L7a.5 (`h.2.1.2.1`,
  `h.2.1.2.2.1`) stay, with their types ascribed; one accessor per use would add more names than
  it saves.
- The file-square fact for the rook's home square (`by cases w <;> simp [rookHome,
  Wing.rookFile]`) occurs once, so it stays inline.

Checks: `lake build` green (11 jobs); `lake env lean Chess/Rules.lean` 0.40 s and
`Chess/Basic.lean` 2.4 s, no warnings. `#print axioms`: `CastleMove.legal_iff` unchanged
(`propext`, `Classical.choice`, `Quot.sound`); `Position.CanCastle.not_inCheck` `propext`,
`Quot.sound` (through the definitions in its statement); `Color.homeRank_eq_zero_or_seven`
`propext`. Docstring check: all 146 Rules docstrings are in the spec; Basic's paraphrased count is
still 78 (of 193), the new one not among them. `lake build ChessTest` (rebuilt from Basic up):
green, 21 jobs, 525 s wall clock, 4.98 GB maximum resident set size as `/usr/bin/time -l` reports
it (ChessTest.Perft 256 s and ChessTest.PerftDeep 266 s, rebuilt because Basic changed;
ChessTest.Rules 5.2 s).

---

## Round 7 (2026-11-02, ROADMAP step 6): R3, attack symmetry

Inputs: THEOREMS R3, MoveGen spec design choice 10 (decided in MoveGen's Round 5 for a Boolean
king-safety test in `MoveGen`), Rules review C3. Spec first (§2, L2.10–L2.12 with proof notes;
R3 removed from §12's "not here"), then the Lean.

- `reaches_symm` (R3.1), `reaches_pawn_symm` (R3.2), `Board.attacked_iff_superpiece` (R3.3), in
  section `Reaching`, with the names THEOREMS R3 sketched. R3.3 is stated with `Reaches k c.other`
  for every kind, as THEOREMS has it: for kinds other than the pawn the colour is not read.
- Proofs are short because Basic already had the pieces: `neg_mem_knightJumps`,
  `Square.offset_eq_some_iff_neg`, `Square.shift_eq_some_iff_opposite`,
  `Kind.opposite_mem_slideDirections`, and this file's `Slides.symm`.
- No definition and no instance changed: the trusted text is as it was. The module docstring's
  "Main statements" gained one item.
- The ray-walk `Slides` instance (review C3.1) was measured and not adopted (MoveGen process log,
  Round 5).
- Axioms ledger: the three theorems are [kernel] (`ChessTest/Axioms.lean`).

---

## Round 8 (2026-11-02, readability round): definitions in their own file, `AttackedBy`, helpers moved

Inputs: an independent readability and fidelity audit whose findings two skeptics each reproduced
(trusted definitions interleaved with lemmas; the colour argument of `Attacked`; misplaced helpers,
Rules review C5; stale instance note; checkmate citation; 0-based ranks without a note). Spec
first, then the Lean, then `scripts/check_docstrings.py` (new, Rules review C8) on every file.

- **The split.** `Chess/Rules.lean` (1280 lines) is now an umbrella over three files, as
  `Chess.Game` was split in its step 5. `Chess/Rules/Defs.lean` (396 lines, about 50 of them the
  module docstring) holds every definition and `Decidable` instance, in the old order, and the four
  `#guard`s, and nothing else: 36 `def`s and 24 `instance`s, no theorem (37 `def`s before the
  round; `CastlingRights.ofGet` moved to Position). `Legal`, `Checkmate` and
  `Stalemate` are at lines 363–379 instead of 820–841. `Chess/Rules/Laws.lean` (739 lines) holds
  the lemma sections in their old order; `Chess/Rules/Castling.lean` (174 lines) holds §7a, L4.11.
  The split was made by a script that cut the old file at its section markers and checked that
  every non-blank line landed in exactly one file (only four section headings were added, so that
  each lemma section of `Laws` sits under the heading of its topic). Each file has a module
  docstring in the library's format; the old module docstring was divided between them (main
  definitions and the notes on definitions in `Defs`, main statements and proof notes in `Laws`).
  Downstream imports are unchanged (`import Chess.Rules`). Spec: "Files and their contents"
  replaces "Contents of the file"; design choice 15.
- **`Board.Attacked` → `Board.AttackedBy`**, `Board.attacked_iff` → `Board.attackedBy_iff`,
  `Board.attacked_iff_superpiece` → `Board.attackedBy_iff_superpiece`, and in MoveGen
  `Board.superpieceAttacked(_iff)` → `Board.superpieceAttackedBy(_iff)`. The colour argument of
  `AttackedBy` is the attacker, of `KingAttacked` the colour of the king attacked; the new name
  says which. Docstrings unchanged. Renamed in the Lean, the axioms ledger, the specs, DESIGN,
  THEOREMS, ROADMAP and README; not in the process logs and reviews, which are history.
- **Helpers moved** (rest of Rules review C5, spec §12 items 5 and 7): the four `private`
  helpers of §4 and L7.6 `rookCastleSquare_ne_kingHome` are public lemmas of `Chess.Basic` (B6.2a,
  B4.8a, B7.5a, B7.9); `CastlingRights.ofGet` and `get_ofGet` (D5.7, L5.1) are in `Chess.Position`
  (D4.6b, P4.3b). Statements, docstrings and proofs unchanged. `Board.colorAt`, `kindAt` and
  `setMany` stay here (spec §12 item 9 says why). Still not done: the namespace rule in DESIGN §2.
- **Docstrings** (spec first). `Move.PromotionRule`, `DoublePushMove` and `EnPassantMove` give the
  0-based value beside the rank's name ("(`relRank p.turn = 1`, counting from 0)"); `Checkmate`
  cites FIDE 1.4 and 1.4.1, which define checkmate, and says 5.1.1 makes it a win (it cited 5.1.1
  alone, which only states the result; the article texts were checked by two reviewers against
  the FIDE handbook, not by this round). The `EnPassantMove` docstring was rewrapped.
- **Module docstring**: the instance note said every other instance is `by unfold X;
  infer_instance`, but `Reaches.decidable` uses `cases` and `AttacksFrom.decidable` `split`; it now
  says so (`Defs`' notes, spec design choice 9).

Checks: `lake build` green (20 jobs); `lake build ChessTest` green (32 jobs, 161 s, 3.4 GB maximum
resident set size); `lake build ChessDemo` green (`GothamCert` 164 s, as before; 2.8 GB);
`lake build chess-perft` green. `#print axioms` of `CastleMove.legal_iff`, `castling_play_le`,
`Board.attackedBy_iff_superpiece` and the moved lemmas: standard axioms only. Docstring check:
every docstring of `Defs` (60), `Laws` (73) and `Castling` (9) is in the spec. No `sorry`,
`native_decide`, `axiom`, `unsafe` or `implemented_by` in `Chess/`. No line over 100 characters.
