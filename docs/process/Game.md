# Process log: `Chess.Game`

The record of the back-and-forth between the English specification (`docs/spec/Game.md`) and the
Lean (`Chess/Game.lean`). Each round says what changed, in which direction, and why.

---

## Round 1: English draft

Date: 2026-11-01. Author role: English specification writer. Lean written in the library: none.

**Inputs read.** `docs/DESIGN.md` (all, especially §1, §2, §6, §7, §8.5, §9–§12),
`docs/THEOREMS.md` (§0, §1, G1–G8, C1–C8, O2, O8, §7–§9), `docs/research/game-theory.md` (§8),
`docs/research/lean-engineering.md` (§7–§10), the specs, process logs and reviews of `Basic`,
`Position`, `Rules` and `MoveGen` (for conventions and for the review findings addressed to `Game`:
MoveGen review C2 (kernel cost per node, the `isLegal` question) and C3 (morphisms by membership),
Rules review C6), `Chess/Basic.lean` (the `Color` section), and the prototype's
`prototype/ChessProof/Cert.lean` and `GothamKernel.lean` (what to keep: the three-rule semantics
with the stalemate guard, `not_both`, per-node literal checkpoints; what to drop: fuel in the
checker, `memB`/`lookup` helpers, the budget counted after the best move, six glue lemmas).

**What the draft fixes.** 9 definition entries in the trusted section (D1.1–D1.9), 4 search
definitions and 2 instances (D3.1–D3.6), 4 certificate definitions (D4.1–D4.4), 2 toy games
(D5.1–D5.2); 18 law lemmas (L2.1–L2.18), 5 search lemmas (L3.1–L3.5), 11 certificate and per-node
lemmas (L4.1–L4.11), and 14 tests (T1–T14). Each definition has its docstring sentence, Lean name,
type and body; each lemma its English, Lean statement, tag and proof route.

**Facts checked in Lean 4.28 before writing them down** (scratch files importing the built
`Chess.Basic`; nothing in the library):

- `structure Game` with instance-implicit decidability fields, and
  `attribute [instance] Game.decMated Game.decEqMove`, elaborate; a `where` construction may omit
  the two fields.
- `G.Forces a T n x` dot notation works inside the constructors of `inductive Forces`.
- With `abbrev WinsIn`, `h.mono` for `h : G.WinsIn a n x` resolves to `Forces.mono`, and the
  `Forces` decidability instance decides `WinsIn`.
- `attackerForces`, structural on the budget with the partially applied recursive call passed to the
  non-recursive `defenderStep`, is accepted; `attackerForces_succ` holds by `rfl`.
- The search correctness proof goes through as drafted: `forces_attacker_zero_iff`,
  `forces_attacker_succ_iff`, `forces_defender_iff`, `defenderStep_iff`, `attackerForces_iff`, and
  `Forces.mono`.
- `checkForces`/`checkReplies` by mutual structural recursion through `List (M × Cert M)` are
  accepted, evaluate under `decide`, `decide +kernel` and `rfl`, and depend only on `propext`. The
  mutual soundness theorems `checkForces_sound`/`checkReplies_sound` go through by structural
  recursion with the binders after the colon.
- `checkOnlyMove` accepts T9 under `decide +kernel` and rejects T10.
- Tests T1–T10, T12–T14 elaborate (T5 and T12 against stubbed statements of L2.10 and L2.7).
- Pitfalls found: a toy game declared with `def` breaks numerals for its moves (needs `abbrev`);
  `{ takeAway with Mated := … }` copies `decMated` and fails (the variant is written out); an
  unused instance variable `[DecidablePred T]` is pulled into every theorem mentioning `T` (so it
  is declared only in the Search and Certificates sections).
- Core has `List.forall_mem_cons` and `List.forall_mem_nil` in the shapes the per-node proofs need.

**Decisions taken in the English, beyond DESIGN** (each argued in spec §6):

1. The search names the defender rule once (`defenderStep`); the attacker search takes no colour
   (choices 8, 9).
2. Three one-step characterizations (L2.1–L2.3) serve the search proof, `winsIn_zero_iff`, the
   stalemate lemma and hand unfolding.
3. Every Boolean conjunct of a checker is `decide` of its proposition (choice 10).
4. **Deviation from DESIGN §7.2/§8.5:** `checkForces` does not require each listed reply to be an
   available move; soundness does not need it (choice 11).
5. **Deviation from DESIGN §7.2:** `checkOnlyMove` takes the certificate after the best move and
   builds `.move best next` itself (choice 14).
6. DESIGN §10's open question settled: one refutation budget `k` for all alternatives (choice 15).
7. No `isLegal` field: the per-node lemmas accept a membership proof from any source (choice 13).
8. Four glue lemmas plus core list lemmas replace the prototype's six (choice 17).
9. `Forces.trans`, `mateIn_succ_iff`, `Wins.exists_mateIn`, `OnlyWinningMove.wins`/`.unique` added
   as cheap or sanity lemmas.
10. The toy games and tests stay in the library file, since they cost well under a second.

**Questions for the translator and the critic.**

- Is dropping the per-reply membership conjunct (decision 4) acceptable to the architect, given that
  DESIGN §8.5's English says "every subtree belongs to a listed move"? If DESIGN is to stay as is,
  the conjunct is one more `decide (m ∈ G.moves x)` in `checkReplies` and one more line in L4.1.
- Should `Wins.exists_mateIn` move after the decidability instance to avoid classical reasoning?
- For Stage 3: change `checkOnlyMove`'s `refs` type, or add a second checker (spec §7, item 1)?
- Kernel cost of the `replies` case naming `G.moves x` twice (spec §7, item 2): measure on chess
  before the Gotham demonstration.

**Next.** Round 1 critique of the English, then Round 2: translate into `Chess/Game.lean`, add the
import to `Chess.lean`, record every place where the English had to be made more precise or
changed for a proof to go through.

---

## Round 2: English revised

Date: 2026-11-01. Author role: translator. Input: the Round 1 critique of `docs/spec/Game.md`
(sections A–E). Every item was accepted; the changes, by critique item:

- **A1** `Forces.replies` docstring: no longer claims a defender with no move "is never forced"; it
  says the rule never applies to such a defender, which is then forced only if already in the
  target.
- **A2** `Forces` docstring: now says `T` is tested at every state (`x` included), that a defender
  with no available move outside `T` escapes, and that play never reaching `T` is not forced.
- **A3** The "least set" reading is restated as the least *family* `(F n)` with three closure
  conditions.
- **A4** L4.3's English is about an arbitrary list `ms`, order preserved; "available" removed.
- **A5** Choice 11 no longer says an extra pair is "ignored": it is checked and must pass, but
  contributes nothing. The same sentence is added to the `Cert.replies` and `checkForces`
  docstrings, and "(as the first component of some pair)" to the coverage clause.
- **A6** `checkOnlyMove` docstring: "Accepts only if …", names `checkOnlyMove_sound`, and says it
  rejects true claims whose alternatives only draw.
- **A7** §4 intro: "If a certificate checks, the claim holds. No certificate for a false claim
  checks."
- **A8** Header: §2–§4 items have a soundness theorem, and completeness only for `searchForces` and
  `checkForces`.
- **A9** After D1.8: an engine's mate report is an untrusted claim of `MateIn a 3` (with the
  Stockfish sign convention); a problem's "#3" is `WinsIn a 3`, and soundness of the problem adds
  `¬ WinsIn a 2`.
- **B1** `OnlyWinningMove` docstring: "other" means a different `G.Move` value; the instance
  obligation on `ChessGame` (no two values for the same chess move) is recorded under D1.1.
- **B2** The `Game` docstring and the module docstring say that mate is the only loss, and that
  there are no draws by rule, clock, repetition or move count.
- **B3** `Wins` docstring: "there is a number `n` such that `G.WinsIn a n x`", one bound for every
  line; a note explains the agreement with unbounded strategies under finite branching.
- **B4** New law **L2.20** `wins_iff_of_moves_eq_nil (hl : G.moves x = []) : G.Wins a x ↔
  G.DefenderMated a x`. **Consequence:** L2.7 `not_wins_of_stalemate` no longer needs a turn
  hypothesis (a not-mated side with no move is lost by nobody, whoever is to move), so its
  statement is now `(hnm : ¬ G.Mated x) (hl : G.moves x = []) : ¬ G.Wins a x`, proved in one line
  from L2.20. This is stronger than THEOREMS G2 and listed as a deviation (choice 19). T12 loses
  its `rfl` argument.
- **B5** Field docstrings of `moves_eq_nil_of_mated` and `play`, and the `takeAwayStalemate`
  docstring, rewritten as proposed.
- **B6** `MateIn.decidable` docstring: "each budget from 0 to `n`".
- **C1** §0 defines attacker/defender state (node), children, "below", available; cites THEOREMS
  §0.2 for D1 and §0.4 / DESIGN §7.3 for [kernel].
- **C2** The search argument `next : G.State → Bool` is renamed `atk` (and `hnext` → `hatk`);
  `next` now always means a certificate.
- **C3** `hm : ¬ G.Mated x` → `hnm`, `h : G.moves x = []` → `hl` (L2.7); `hne` for `m' ≠ m` →
  `hdiff` (L2.16, L2.19); both added to §0.
- **C4 / D1** Adopted the critic's cleaner form: `attackerForces_iff : G.attackerForces T n x = true
  ↔ G.Forces (G.turn x) T n x` and `defenderForced_iff : … ↔ G.Forces (G.turn x).other T n x`,
  with no turn hypothesis. The docstrings of D3.2/D3.3 say "for the side to move" / "for the
  opponent of the side to move". L3.5 rewrites with the turn. (The question of where `x` is bound
  in L3.3 disappears: `induction n generalizing x` on a statement with no hypothesis.)
- **D2** L4.11 moved to §2.5 as **L2.19** `OnlyWinningMove.of_refuted` (with `m`, `m'`, `hdiff`
  instead of `best`, `m`, `hne`); L4.7 assembles with it; the "translator's choice" note is gone.
  `section PerNode` drops the now-unused `k` and `best` variables.
- **D3** Docstring tags: the leading "(G3)" moves to a trailing "THEOREMS G3." in the Lean
  docstring (§0).
- **D4** The module docstring is given word for word.
- **D5** §0 says where `namespace Game` opens (after D1.2) and closes (before `Cert`), and that the
  sections sit inside it.
- **D6** T11's term written in full, by `decide +kernel` like T9.
- **D7** New design choice 19 lists the deviations from THEOREMS names and shapes (`searchForces_iff`,
  implicit `turn_play` arguments, `WinsIn.mono` by dot notation, the stronger
  `not_wins_of_stalemate`, C7's conclusion per DESIGN §12, the two new laws).
- **E1** L4.8's English is about forcing facts, not "literal states".
- **E2** A note after §4.1 says L4.10 needs the generator's literal list, order and repetitions
  included, so choice 16 does not cover the glue lemmas.
- **E3** Search cost: "between about 35^k and 35^(2k) leaves".
- **E4** Choice 4 now lists `winsIn_zero_iff` (and the new L2.20) among the mate-specific lemmas.

Also: "Lemma IDs are stable labels, not positions" added to §0, since L2.19 and L2.20 are placed
where they read best rather than at the end of their section.

---

## Round 3: translation feedback

Date: 2026-11-01. Author role: translator. `Chess/Game.lean` written definition by definition in
the order of the spec, with every docstring of the Round 2 English; `import Chess.Game` added to
`Chess.lean`. `lake build` succeeds with **no warnings and no `sorry`** (691 lines, of which about
110 are the module docstring and the tests). No `-- TARGET:` remains: every lemma L2.1–L2.20,
L3.1–L3.5, L4.1–L4.10 is proved, and every [cheap] lemma stayed short (`Forces.trans` 5 lines,
`Wins.exists_mateIn` 7 lines).

**`#print axioms`** (scratch file, not in the library):

| Declaration | Axioms |
|---|---|
| `checkWin_sound` | `propext`, `Quot.sound` |
| `checkOnlyMove_sound` | `propext`, `Quot.sound` |
| `searchForces_iff` | `propext`, `Quot.sound` |
| `checkForces_complete` | `propext`, `Quot.sound` |
| `Toy.takeAway_onlyWinningMove` | `propext`, `Quot.sound` |
| `WinsIn.not_both` | `propext` |
| `Wins.exists_mateIn` | `propext`, `Classical.choice`, `Quot.sound` (the classical `by_cases`, open item 3) |

All within [kernel]. `h.mono` for `h : G.WinsIn a n x` resolves to `Forces.mono` (re-checked).

**Where the Lean forced a decision the English had not made, and how the English now reads:**

1. **`rw` does not see through the `abbrev WinsIn`.** In L2.6, `rw [forces_defender_iff ht']`
   failed on a goal stated with `WinsIn` ("did not find an occurrence of `G.Forces a ?T ?n x`").
   Term-mode use, `exact`, instance search and dot notation all see through it; `rw`'s keyed
   matching does not. The proof now composes, `(forces_defender_iff ht').trans ⟨?_, .inl⟩`.
   English changed: choice 5 gains a caveat saying exactly which tools see through the `abbrev`;
   L2.6's proof sketch says `Iff.trans`, not rewriting. (Its claim "every `Forces` lemma … reach[es]
   through it" was true only for application.)
2. **Where the `variable` line of `section Search` goes.** §0 said each section "opens with" its
   `variable` line, but the Search section begins with four definitions that bind `G` and `T`
   explicitly, and the spec itself placed the variable block under "Lemmas of §3". Lean would
   accept either (explicit binders shadow), but a variable line above definitions that do not use
   it misleads the reader. English changed: §0 says each section declares its variable line
   immediately before its first lemma, and that in `section Search` the definitions come first.
3. **L2.16 constructive or classical.** The spec offered `Classical.byContradiction` "or
   `by_cases` with `G.decEqMove`". Chosen: `Decidable.byContradiction`, which uses the instance
   registered by D1.2 and keeps L2.16, L2.18 and their users free of `Classical.choice`. English
   changed: the proof sketch names only this route.
4. **Docstrings on tests.** An `example` takes no docstring, so the "a docstring on every
   definition" rule cannot apply to T1–T14. Chosen: each test is preceded by a line comment
   `-- Tn. …` stating what it tests; T11, a named theorem, has a docstring. T6 is two `example`s
   (`decide +kernel` and `rfl`). English changed: the paragraph introducing the tests says so, and
   no longer mentions the scratch-file stubs of Round 1.
5. **Subheadings inside `section Laws` and before `section PerNode`.** The spec's §2.1–§2.5 and §4.1
   headings had no stated Lean counterpart. Chosen: `/-! ### … -/` with the same titles, so the file
   reads in the spec's order. English changed: "Contents of the file" lists them.
6. **`WinsIn.not_both`: repeated turn contradictions.** Five of the nine cases end in "the turn is
   both `a` and `a.other`", and the second derivation states its turns for `a.other.other`. Chosen:
   one local fact `hturn` and `Color.other_other a ▸ _` to transport. English changed: L2.8's proof
   sketch describes this.
7. **Congruence instead of hand-written `Iff`s** in L3.2 and L3.3: after the `simp only`, the goals
   match by `or_congr`, `and_congr_right`, `forall_congr'`, `imp_congr_right`, `exists_congr` from
   core, which reads as "the sides agree child by child". English changed: L3.2's proof sketch names
   them.
8. **Trailing "THEOREMS …" sentences.** The Round 2 rule (§0) was applied to every tagged lemma.
   The three per-node lemmas L4.8–L4.10 have no tag in their table rows, but §4.1's heading is
   "(C3)"; their docstrings end "THEOREMS C3." No English change needed beyond the §0 rule.

**Confirmed without change** (the English was precise enough to translate mechanically): the
`Game` structure with instance-implicit decidability fields and the `attribute [instance]` line;
`Forces` and its constructors; `defenderStep`/`attackerForces` structural on the budget, with
`attackerForces_succ` by `rfl`; the C4 form of L3.3/L3.4 (no turn hypothesis; `induction n
generalizing x` went through first time, with `hatk` at `a := G.turn x` by `rw [ih, hy]`); the
mutual structural recursion of `checkForces`/`checkReplies` and of their soundness theorems through
the nested `List (M × Cert M)`; `checkForces_complete` by `induction w` with L4.3; L4.7 assembled by
L2.19; the toy games as `abbrev`s, and T12 with `rfl` for `hl`.

**Open items carried forward** (unchanged from spec §7): Stage 3 refutation type for
`checkOnlyMove`; kernel cost of the `replies` conjuncts naming `G.moves x` twice (measure on chess);
`Wins.exists_mateIn` remaining classical.

---

## Round 4: refinement

Date: 2026-11-01. Author role: refiner. Input: the critique of Round 3 (`docs/spec/Game.md` checked
against `Chess/Game.lean`; verdict "ready", no semantic bug). Every item below was applied to the
English first and then to the Lean, or declined with a reason. `lake build` succeeds (8 jobs) with
**no warnings and no `sorry`**; `Chess/Game.lean` is 748 lines (691 in Round 3; the growth is the
five new lemmas). Tests T1–T14 unchanged and passing.

**`#print axioms`** (scratch file, not in the library):

| Declaration | Axioms |
|---|---|
| `checkOnlyMove_sound` | `propext`, `Quot.sound` |
| `searchForces_iff` | `propext`, `Quot.sound` |
| `WinsIn.not_both` | `propext` |
| `wins_attacker_iff` (new) | none |
| `wins_defender_iff` (new) | `propext`, `Quot.sound` |
| `forces_common_budget` (new) | `propext`, `Quot.sound` |
| `OnlyWinningMove.winsIn_play` (new) | `propext` |
| `Toy.takeAway_onlyWinningMove` | `propext`, `Quot.sound` |

### Fidelity (English and Lean disagreed or the English was vague)

- **F1, binding rule.** The critique offered two fixes: exempt pattern-matched definitions in the
  English, or name the Pi binders after the colon in the Lean (`(n : Nat) → (x : G.State) → Bool`),
  claimed to show up in hovers. Tried the second: it builds, but `#check @attackerForces` and
  `#check @checkForces` still print `Nat → G.State → Bool`; the equation compiler drops the names.
  So it buys nothing a reader sees and is unusual style. Reverted. **English changed:** §0's
  binding rule now exempts definitions by pattern matching (D3.2, D4.2), whose docstrings name
  those arguments themselves in phrases that say what each is ("checks certificate `c`", "a
  `move m next` node", "a budget of the form `k + 1`", "every pair `(m, c)` of `rs`"), and records
  why naming the binders was rejected. Lean unchanged.
- **F2, `OnlyWinningMove` docstring.** "…or a slower win, mean there is no only winning move" could
  be read as about the speed of `m`. **English and Lean changed** to: "'Other' means a different
  value of `G.Move`, so if another available move also wins, however slowly, there is no only
  winning move; in particular there is none when two promotions both win."
- **F3, "Stage 1" in the `checkOnlyMove` docstring.** Roadmap jargon in a permanent docstring.
  **English and Lean changed** to: "…only draws: this checker cannot certify those, and refutations
  by traps are future work."
- **F4, instance obligation missing from the Lean.** **English and Lean changed:** the `moves` field
  docstring now ends "An instance must not list two different values for the same move (for chess,
  two encodings of one castling), since `OnlyWinningMove` tells moves apart by their values." The
  D1.1 translator note points to it and adds why it is not a field (breaking it can only make
  `OnlyWinningMove` false, never wrongly true).
- **F5, sibling lemmas stated differently.** `wins_iff_of_moves_eq_nil` now concludes
  `G.turn x = a.other ∧ G.Mated x`, like `winsIn_zero_iff` and THEOREMS G2. **Both sides changed**;
  the proof is untouched (`DefenderMated` unfolds by definition under `exact`).
- **F6, `rw` and the `abbrev`.** The Round 3 caveat ("`rw` cannot see through it") was too
  pessimistic. Re-checked: `rw [forces_defender_iff ht]` on a `WinsIn` goal fails, but
  `rw [WinsIn, forces_defender_iff ht]` and `simp only [forces_defender_iff ht]` both work.
  **English changed:** choice 5's caveat lists the three ways round it and says why bare `rw` fails
  (it matches the head symbol syntactically); L2.6's proof sketch refers to it. Lean unchanged
  (L2.6 keeps `Iff.trans`).
- **F7, proof-route drift.** L2.11: **Lean changed** to the spec's `rcases … with hlt | rfl | hlt`
  and `· rfl`. L2.17: **English changed** to the Lean's term-mode `let`.
- **F8, THEOREMS.md out of sync.** Not edited here: THEOREMS.md is the theorem architect's file and
  was being edited by another role this session. **English changed** instead: spec choice 19, the
  list of deviations from THEOREMS addressed to the theorem architect, now covers every item the
  critique found: `turn_play` (G1), `searchWin` (G5), `Cert.mate` → `Cert.goal` (C1; new bullet),
  `not_wins_of_stalemate` without a turn hypothesis (G2), C7's conclusion counted at `x` (the
  `Refutation` type is in §7 as Stage 3), toy games in the library file rather than `test/` (G1;
  new bullet), and the five new lemmas of this round. **Handoff:** the theorem architect should
  apply choice 19 to THEOREMS G1, G2, G5, C1, C7.

### Readability and elegance

- **R1, the turn contradiction spelled out seven times.** Basic is not this module, so the lemma
  lives here: **L2.21** `theorem turn_ne_both (ht : G.turn x = a) (ht' : G.turn x = a.other) :
  False`, docstring "The side to move is never both the attacker and the defender.", placed first in
  §2.1. Used in L2.1–L2.3, L2.6, L2.8, and the new L2.23 and L2.25. `WinsIn.not_both` lost its local
  `hturn`; the `Color.other_other a ▸ h'.1` transport elaborates directly as its first argument
  (no `(a := a)` needed). **English changed:** §2.1 intro, L2.1–L2.3 and L2.8 proof sketches.
- **R2, why `checkReplies` exists.** **English and Lean changed:** a line comment above `mutual`
  says structural recursion cannot pass through `List.all` over the nested list, and the
  hand-written recursion keeps the checker kernel-reducible. Text in D4.2.
- **R3, instance style.** `MateIn.decidable` now uses the section variables, like `Forces.decidable`
  (`#check` shows `{G a n x}` implicit; `[DecidablePred T]` is not pulled in). **Both sides
  changed** (D3.6 heading and body).
- **R4, toy duplication.** Declined. A parametrized `takeAwayWith (loses : Color → Bool)` would make
  `takeAway`'s `Mated` read `x.2 = 0 ∧ (fun _ => true) x.1 = true` instead of `x.2 = 0`: the
  duplication is eight plain lines, and each toy's definition reads exactly as its docstring. The
  critique marked it optional.
- **R5, `OnlyWinningMove.unique` argument order.** Now concludes `m = m'`, in hypothesis order like
  `MateIn.unique`; the proof became `(h'.wins_iff h.1).1 h.2.1`, with no `symm`. **Both sides
  changed.**
- **R6, `defenderStep` reads `G.moves x` twice.** Deferred with spec open item 2, which now says the
  same fix applies to `defenderStep` in the same change, if the chess measurement calls for it.
- **R7, `Forces.mono`.** Kept the `obtain ⟨n', rfl⟩ : ∃ k, n' = k + 1` line: `cases n'` with an
  `omega` for the zero case is three lines instead of one. The critique called it fine.

### Provability (lemmas added now)

- **P2, `checkOnlyMove_sound` forgets that `best` itself wins within `n − 1`.** Added **L2.25**
  `OnlyWinningMove.winsIn_play (h : G.OnlyWinningMove x m) (w : G.WinsIn (G.turn x) (n + 1) x) :
  G.WinsIn (G.turn x) n (G.play x m)` in §2.5, docstring "…then it wins within `n` after `m`: a
  fastest win starts with `m`." A lemma about every only winning move, not a third conjunct of
  `checkOnlyMove_sound`, since it holds without a certificate. The critique's 4-line proof went in
  as given, with `turn_ne_both` for the impossible `goal` disjunct.
- **P3, one-step characterizations of `Wins`** (for G9, G10). Added three [cheap] lemmas:
  - **L2.22** `forces_common_budget (h : ∀ m ∈ ms, ∃ n, G.Forces a T n (G.play x m)) :
    ∃ n, ∀ m ∈ ms, G.Forces a T n (G.play x m)` in §2.2: list induction, `max`, and `Forces.mono`
    (9 lines). Stated for moves at `x`, its only use, rather than for an arbitrary function. The
    `section Laws` variable line gains `{ms : List G.Move}`.
  - **L2.23** `wins_attacker_iff (ht : G.turn x = a) : G.Wins a x ↔ ∃ m ∈ G.moves x,
    G.Wins a (G.play x m)`. Uses no axiom at all.
  - **L2.24** `wins_defender_iff (ht : G.turn x = a.other) : G.Wins a x ↔ G.Mated x ∨
    (G.moves x ≠ [] ∧ ∀ m ∈ G.moves x, G.Wins a (G.play x m))`. With the turn fixed by `ht`, the
    mate disjunct is just `G.Mated x`, not `DefenderMated`.
  The module docstring's "Main statements" gains a line for L2.23 and L2.24 (both sides).
- **P4, `DecidableEq G.State` for the trap checker (C5).** Recorded as spec choice 21: an instance
  argument of `checkTrap`, not a `Game` field.
- **P5, survival certificates (C4).** Recorded as spec choice 20: `checkForces` hardcodes the
  attacker's role, so C4 will be a second checker with its own soundness proof.
- **P1, P6, P7.** No change: P1 confirms Stage 1 targets; P6 agrees to keep `Wins.exists_mateIn`
  classical (open item 3); P7 confirms morphisms can be stated by membership (choice 16).

**Lemma count.** `section Laws` now has L2.1–L2.25. Every new lemma stayed under the [cheap] bound
of 15 lines. Lemma IDs follow the §0 rule: new numbers, placed where they read best (L2.21 first in
§2.1, L2.22 after `Forces.trans`, L2.23–L2.24 after the stalemate lemma, L2.25 after
`OnlyWinningMove.unique`).

---

## Round 5: split, only-move certificate, frozen interface, diagnostics (ROADMAP step 5)

Date: 2026-11-02. Author role: overnight implementer. Inputs: `docs/ROADMAP.md` §5 step 5,
`docs/reviews/Game.md` (C2, C3, C9), `docs/DESIGN.md` §7.2, §7.4, §11, the spec and this log, and
the prototype (`prototype/ChessProof/Cert.lean`, `GothamKernel.lean`, `Flatten.lean`,
`scripts/gen_cert.py`) for what generated files look like. Starting state: `lake build` green
(11 jobs).

**Split (review C2), as the review proposed.** `Chess/Game.lean` became six files: `Defs` (the
section "Games", 130 lines with the module docstring), `Laws` (281), `Search` (127), `Cert` (421,
of which 170 are the new diagnostics), `Examples` (159) and the umbrella `Chess/Game.lean` (40,
imports and module docstring). Every declaration moved verbatim, with its docstring; the slices
were cut by line number from a copy of the old file, so nothing was retyped. `Search` and `Cert`
both import `Laws` and not each other (the checkers need `OnlyWinningMove.of_refuted`, not the
search). The toy games and tests stayed in the library, in `Examples`, as before; moving them to
`ChessTest` would have saved under a second and lost the documentation. The heavier alternative of
one spec per file was not taken: one spec covers the six files (spec choice 22). **English
changed:** header, §0 namespaces, "Files and their contents" (replacing "Contents of the file"),
six module docstrings, a file line under each section heading, §8.

**Module docstrings.** Five are new (`Defs`, `Laws`, `Search`, `Cert`, `Examples`), and the
umbrella's was rewritten to point to them. Review C9's first point is done in the new `Laws`
docstring, whose "Main statements" now name `Forces.trans`, `OnlyWinningMove.of_refuted` and
`OnlyWinningMove.winsIn_play`. These were written in the Lean first and copied into the spec by
script, the one place this round went Lean → English; every other docstring of the round was
written in the spec first.

**`OnlyMoveCert` (review C3.3): adopted.** `checkOnlyMove n k x best next refs` became
`checkOnlyMove n x best oc` with `oc : OnlyMoveCert G.Move` holding `next`, `refBudget` and
`refs`. The rule that decides what goes where: the arguments are the claim (they occur in the
conclusion of `checkOnlyMove_sound`), the structure is the evidence. So `best` stays an argument
(it is in `OnlyWinningMove x best`), and the refutation budget, which the review listed among the
structure's fields, goes into the structure (it is not in the conclusion). The review's field name
`win` became `next`, matching `Cert.move`'s field and the old argument. **English changed:** D4.4
(signature, body, docstring, a paragraph on the claim/evidence rule), D4.5 (new), the §4 variable
line (`k`, `next`, `refs` out, `oc` in), L4.7, choices 12, 14, 15, new choices 23 and 24, open
item 1 (a third way: a new field with a default), T9–T11. Lean: the proof of
`checkOnlyMove_sound` changed only in names (`oc.next`, `oc.refBudget`).

**Owner decision taken: one refutation budget** (ROADMAP §5's open decision "one refutation budget
`k` or one per alternative"). Kept one, now the field `refBudget` (choice 24): monotonicity makes
the largest budget serve every alternative, and the structure can grow a per-alternative field
later without breaking old files. The owner can reverse this.

**Frozen interface (review C3.1, C3.2).** Spec §4.3 lists what a generated file may use and says
it never applies a constructor of `Forces`. To make that possible for mate leaves, **L4.12**
`WinsIn.of_mated (ht : G.turn x = a.other) (h : G.Mated x) : G.WinsIn a n x` was added to
`section PerNode` (spec first; the prototype's `WinsIn.mate`; L4.11 is not reused, since it was
Round 1's label of L2.19). The interface is recorded by `ChessTest/Interface.lean` (22
`#guard_msgs` entries of `#check`/`#print` output; `docs/spec/ChessTest.Interface.md`). The name
`Cert` is kept, explicitly (C3.2). Not done: review C3.1's "one sentence in the `scripts/` README";
there is no such README yet (the perft scripts are documented in `docs/process/ChessTest.md`), so
the rule is in spec §4.3, in `Cert`'s module docstring and in ROADMAP step 7, where the generator
is written.

**Diagnostics (review C3.4).** Spec first: D4.6 `Cert.Rejection` (one constructor per checker
condition), D4.7 `firstFailure`/`firstFailureReplies` (mutual structural recursion mirroring
`checkForces`/`checkReplies`), D4.8 `firstFailureWin`, D4.9 `firstFailureOnlyMove`, and the
agreement lemmas L4.13, L4.14, L4.16, with the helper L4.15 `checkReplies_eq_true_iff`. The review
asked for no proof; the agreement was cheap enough to prove (choice 25), and it guarantees that a
diagnostic reports a failure exactly when the checker rejects (amended in Round 6).
`firstFailureWin` was not in the review; it is to `firstFailure` what `checkWin` is to
`checkForces`, and every test and the generator use it. `firstFailureOnlyMove` walks the refutations
with `firstFailureReplies` rather than a third recursion, since checking the refutations is
`checkReplies` for the opponent (L4.15).

**Lean → English (proofs).**
- The `replies` case of L4.13 first failed: after `simp only [decide_not, …]` the `find?` predicate
  in the goal had become `!decide (…)`, so `cases hf : (G.moves x).find? (fun m => m ∉ …)` no
  longer matched it. Fix: rewrite with the equation lemmas `firstFailure.eq_4` and
  `checkForces.eq_4` and split on the `find?` before any `simp`. The spec's proof note says this.
- `Iff.not` does not exist in core; the `some` case of L4.14 proves `checkForces … ≠ true` from
  L4.13 directly.
- The coverage conjunct after `simp` is `∀ m ∈ G.moves x, m ∈ rs.map Prod.fst` only under
  `simp only [Bool.and_eq_true, decide_eq_true_eq]`; full `simp` rewrites it to
  `∃ c, (m, c) ∈ rs`. The proofs use `simp only` there.
- `#print axioms`: L4.12 none; L4.13 and L4.16 `propext`, `Classical.choice`, `Quot.sound`. All
  three are in the axioms ledger (now 131 entries).

**Tests.** T9–T11 use structure-instance notation for the certificate. New T15–T19 run the
diagnostics on the toy games, and together produce every constructor of `Cert.Rejection` (including
a path inside a refutation, `[2]`). T11's docstring is now given in the spec (review C9's second
point). Three `#guard`s in `ChessTest/ChessGame.lean` run `firstFailureWin` on chess (an accepted
mate in one, a legal non-mating move, an illegal move).

**Not changed.** Spec open item 2 (the `replies` case reads `G.moves x` twice; review C6 measured
that the kernel shares it) is left for the owner to close. No declaration was renamed.

**Checked.** All 106 docstrings of the six files (declarations, fields, constructors and the six
module docstrings) occur word for word in the spec (script, whitespace-normalised, trailing
"THEOREMS …" tags stripped; before this round one docstring, T11's, did not). No line over 100
characters. `lake build` green (17 jobs); `lake build ChessTest` green (28 jobs), see
`docs/process/ChessTest.md` Round 3. Elaboration time per file (`lake env lean`, this machine):
`Defs`, `Laws`, `Search` 0.18 s each, `Cert` 0.59 s, `Examples` 0.23 s, the umbrella 0.14 s
(an empty file importing `Chess.Basic` takes 0.14 s); the old single `Game.lean` took 0.40 s. The
new cost is mostly the diagnostics and their proofs.

---

## Round 6 (2026-11-02, review fixes of Round 5)

Author role: overnight implementer, fixing the review of Round 5 (ROADMAP step 5, "Freeze the
certificate interface"). Spec first for every changed declaration.

**The interface was not self-sufficient at defender nodes (medium).** Round 5 said the only gap
in the frozen interface was mate leaves. It was not: `Forces.replies_of_moves_eq` takes
`h : ∀ m' ∈ m :: ms, G.Forces a T n (G.play x m')`, and a per-node file discharges it one move at a
time, which Round 5 left to core's `List.forall_mem_cons` and `List.forall_mem_nil`. Neither was in
§4.3 or in the interface ledger. Of the review's two fixes (own glue lemmas, or allow core lemmas
and record their names), I took the first: the interface is then closed under this library's own
names, and a toolchain change to a core lemma is absorbed by two proofs here instead of by every
generated file. This reverses Round 5's sentence "this module needs no `all_cons`/`all_nil` of its
own"; the prototype had them for the same reason. **English first:** L4.17
`Forces.forall_mem_nil` and L4.18 `Forces.forall_mem_cons` in §4.1 with their docstrings, the
paragraph on walking the move list and the generated shape rewritten to use them, §4.3, choice 26,
the `Cert` module docstring (Main statements), the file contents list and the checklist. **Lean:**
both lemmas in `section PerNode` after `WinsIn.of_mated`, word for word; proofs
`fun _ h => nomatch h` and `List.forall_mem_cons.2 ⟨h, t⟩`; no axioms. **Test T20** (new, in the
spec first): T1's claim proved node by node with the glue alone (one `have` per node, every
checkpoint by `decide` or `rfl`), so the claim "no generated proof needs a constructor of `Forces`
or a lemma of core" is now checked on every build, not only argued. The interface ledger gained
both lemmas, and the axioms ledger both (no axioms).

**Choice 25 overclaimed (medium).** It said the agreement theorems guarantee that "a reported
failure is always the reason for a rejection". L4.13, L4.14 and L4.16 prove only that a diagnostic
returns `none` exactly when its checker accepts; nothing proves that the path of a `some` leads to
a failing node or that the reason is the one that fails there. That is tested (T16–T19 and the
three chess `#guard`s). Choice 25 now says exactly this, and Round 5's "it is what makes a
diagnostic's answer reliable" above is amended to "it guarantees that a diagnostic reports a
failure exactly when the checker rejects". Spec §4.1's "L4.12 closes the last gap in the glue"
became "the gap at mate leaves", with a pointer to L4.17–L4.18.

**`Game.chess` in the interface ledger (low).** Generated files call `Game.chess.checkOnlyMove`
and `Game.chess.firstFailureWin`, so the name is part of the interface. Recorded in
`ChessTest/Interface.lean` (25 entries in all); `docs/spec/ChessTest.Interface.md` now says why.
`Game.chess_mated` was not added: a mate leaf proves `Game.chess.Mated p` by `decide`, which
needs no lemma name.

**Cosmetic (low).** The `move` case of `firstFailure` now prefixes the path with
`match … | some (ms, r) => some (m :: ms, r) | none => none`, as `firstFailureReplies` does, where
it used `Option.map`. D4.7's Lean body changed in the spec first. **Lean → English:** the `move`
case of L4.13 no longer closes by one `simp` with the recursive call reversed (`simp` leaves the
`match` and reports the reversed lemma unused); the proof now runs `simp` with the definitions,
rewrites with `← firstFailure_eq_none_iff next`, and splits on the child's diagnostic. The spec's
proof note says this.

**Long lines (low).** Choices 22 and 25, the file contents list and the L4.13 proof note are
reflowed to 100 columns. (The spec has other long lines from earlier rounds, mostly table rows and
section headings; they were not touched.)

**Checked.** All 108 docstrings of the six files (106 in Round 5, plus the two new lemmas) occur
word for word in the spec (script, whitespace-normalised, trailing "THEOREMS …" tags stripped). No
new line over 100 characters in the Lean or in the edited prose. `lake build` green (17 jobs; a
clean build of a fresh copy takes 7.7 s); every `ChessTest` target rebuilt one at a time and green
(`docs/process/ChessTest.md` Round 4). `Cert` now elaborates in 0.70 s and `Examples` in 0.26 s
(`lake env lean`), against 0.59 s and 0.23 s in Round 5.

**Not changed.** Open item 2 (the `replies` case names the move list twice) is still for the
owner. No `scripts/README.md` exists yet; ROADMAP step 7 says it should repeat §4.3.

---

## Round 7 (2026-11-02, ROADMAP step 7): the only-move root of a per-node proof

Inputs: ROADMAP §5 step 7, the first generated file (`ChessDemo/GothamCert.lean`). Spec first
(§4.1, L4.19–L4.22 and the paragraph after them; §4.3), then the Lean, in `section PerNode` of
`Chess/Game/Cert.lean`.

**The gap.** Round 6 made the interface self-sufficient for win certificates. An only-move claim
proved node by node also needs, at the root, L2.19's hypothesis "after every other available move
the opponent wins", gathered over the explicit list of root moves from one theorem per alternative.
That needed core's list lemmas again. New: `OnlyWinningMove.of_moves_eq` (L4.19: the root, from
`G.moves x = ms`), `refuted_nil`, `refuted_cons_self`, `refuted_cons` (L4.20–L4.22: the walk over
the list, with the best move skipped by `refuted_cons_self`). L4.19 takes `ht : G.turn x = a` and
states everything with `a`, so a generated file's types say `.black`/`.white` and the elaborator
never has to evaluate the turn of a position written `fen "…"`.

**Two elaboration facts found while generating**, now in §4.1 and in `scripts/README.md`:
- The shape `(by decide +kernel : legalMoves p = […])` from the Round 6 example, and
  `mem_legalMoves.2 …` at attacker nodes, made the elaborator unfold `legalMoves p` during
  unification and start evaluating it; on positions with many moves it ran out of heartbeats
  (`whnf`). Written `Game.chess.moves p = […]` and `mem_chess_moves.2 …` (`Chess.ChessGame.Fide`),
  the types match L4.9 and L4.10 syntactically and elaboration is immediate. The interface now
  lists `mem_chess_moves` for chess (§4.3).
- One theorem holding all 34 root checkpoints of Gotham ran out of heartbeats; the generator now
  writes one `refutes_<uci>` theorem per alternative.

Interface ledger (`ChessTest/Interface.lean`): the four new lemmas and `mem_chess_moves` added.
Axioms ledger: the four lemmas added.

---

## Round 7, review fixes (2026-11-02, spec only; no Lean change)

From the review of ROADMAP step 7 (`docs/process/ChessDemo.md`, Round 2).
- §4.3, first bullet: a generated file may name its moves by literal `Move` definitions named by
  their UCI writing, as `ChessDemo.GothamCert` does, with `uci "…" = lit` proved by
  `decide +kernel` in the file that restates the claim (`ChessDemo.uci_b7b2`). Third bullet: the
  literal `Game.chess.moves` equations may be used by `rw` and `▸`, as at the only-move root.
- §4.1: the example of the only-move root is now the generated shape: `moves_root`, the theorem
  `refutations` (stated over `Game.chess.moves`, since it says more than `OnlyWinningMove`: a
  forced mate after each alternative), and `onlyWinningMove` from the two. Its numbers were wrong
  (`WinsIn .white 2`, `w318`); they are now the file's (`WinsIn .white 1`, `w60`).
- §4.1 table: L4.8–L4.10, L4.12, L4.17, L4.18 had no THEOREMS tag and L4.19–L4.22 had it trailing;
  all ten now carry the leading "(C3)" that §0 turns into the docstring's trailing "THEOREMS C3.".
  The docstrings did not change; with §0's rule every docstring of the `Game` files now matches
  its row (26 through the tag rule, the rest verbatim).
- The interface's names did not change, so `ChessTest/Interface.lean` did not either.

---

## Round 7, docstring fixes (2026-11-02, documentation only; no change to any Lean statement or proof)

Two low-severity findings of the overnight review, each reproduced by two independent skeptics.
- game-1. The `Forces` docstring (Defs.lean, spec §1) said "A defender to move with no available
  move outside `T` escapes". Its natural parse, "no move that leads outside `T`", is the opposite of
  the rule: a defender whose every move leads into `T` is forced by `replies`. Reworded, matching
  `SpecForces` in `Chess.Spec.Winning`: "A defender to move with no available move escapes unless
  the state is in `T`". The same ambiguity in DESIGN §6.6 ("A defender with no moves outside `T` is
  safe") was reworded the same way. The rules did not change; this file's Round 1 entry keeps the
  old wording as history.
- game-3. The interface paragraph of the `Cert` module docstring (and its copy in this spec) said
  a generated file proves its claims "only through" the checkers' soundness theorems, the glue
  lemmas and `OnlyWinningMove.of_refuted`. §4.3, `ChessTest/Interface.lean` and
  `ChessDemo/GothamCert.lean` also use literal `Position.play`/`Game.chess.moves` checkpoint
  equations proved by `decide +kernel` and, for chess, `mem_chess_moves`. Round 7 updated §4.3
  but not this paragraph. The paragraph now lists both and points to §4.3, in Cert.lean and in the
  spec copy together.

Checks: `scripts/check_docstrings.py` on `Chess/Game/*.lean` reports 0 definitions missing (the
theorem rows it reports are the existing tag-rule paraphrases); the module docstring of Cert.lean
appears in this spec after whitespace normalisation; `lake build` green (see below).

---

## Note, 2026-11-02 (finding trust-3, documentation only)

A whole-library docstring check found 26 `Game` lemma docstrings not in the spec word for word.
24 match once §0's tag rule is applied ("(G3) …" becomes "… THEOREMS G3."). The other two, L4.1
`checkForces_sound` and L4.4 `checkForces_complete`, are tagged "(C1, general)" and "(C2,
general)" in the spec and end "THEOREMS C1." and "THEOREMS C2." in the Lean; §0 now says that a
qualifier inside the tag is dropped. No Lean change.
