# Process log: the demo library `ChessDemo` and `scripts/gen_cert.py`

The record of the round that closed Stage 1 (ROADMAP steps 6 and 7): the kernel cost of a
certificate node, measured and cut; the certificate generator; the Gotham demonstration; small
mates by search. Specifications: `docs/spec/ChessDemo.Gotham.md`, `ChessDemo.GothamCert.md`,
`ChessDemo.Mates.md`, `ChessDemo.Axioms.md`; the library changes are logged in
`docs/process/MoveGen.md` (Round 5), `Rules.md` (Round 7), `Position.md` (Round 5) and `Game.md`
(Round 7).

---

## Round 1 (2026-11-02, overnight implementer)

Inputs: ROADMAP §5 steps 6–7, MoveGen review C2, Rules review C3, the prototype
(`chess-lean/ChessProof/Gotham.lean`, `Cert.lean`, `GothamKernel.lean`, `Flatten.lean`,
`scripts/gen_cert.py`).

**Order of work, and one departure from the convention.** For the library changes (R3,
`kingSafeAfter`, `Piece.ofCode`, the four glue lemmas) the spec text was written before or with the
Lean and compared word for word afterwards. For the four `ChessDemo` files the docstrings were
drafted in the Lean, while the proofs were being made to work, and then copied into the specs; the
specs were written after. They were compared word for word at the end (see "Checks").

### 1. The generator (`scripts/gen_cert.py`)

Ported from the prototype's script, with these changes:
- **Move order from this library.** Per-node defender proofs state `Game.chess.moves p = […]` in
  the generator's exact order. The script gets every move list from the compiled `chess-perft`
  (depth 1 prints the divide in `legalMoves` order), checks it against python-chess's move set, and
  checks that `chess-perft` writes the script's FEN back unchanged.
- **Checkpoints in this library's conventions,** computed by the script: `Board.pack`'s digits
  (codes 1–12 in python-chess's piece-type order, Position spec D2.1), the en passant target after
  every double push, castling rights revoked by squares.
- **Output: data and proofs.** One `Cert` value per node and the `OnlyMoveCert` (as the task
  asked), and one theorem per node through the glue lemmas only (the prototype flattened in a
  separate Lean program, `Flatten.lean`; here the script writes the per-node file directly).
- **Robustness.** Stockfish runs with one thread and fixed depths (deterministic). If the proposed
  move does not lead to a mate within the budget, the script asks again with more depth and three
  lines and tries the others. `--check` runs `firstFailureOnlyMove`/`firstFailureWin`, interpreted.
- Generating the Gotham file takes about 25 s (68 engine calls, 192 calls of `chess-perft`).

### 2. Kernel cost (ROADMAP step 6)

First full check of the generated file, before any library change: about 430 s wall, 4.3 GB (and
the only-move root failed, see §3). Fifteen nodes of each kind, decided alone (sequential,
`decide +kernel`): mate leaf 2.0 s, defender move list 2.0 s, `m ∈ legalMoves p` 1.5 s, `Legal p m`
0.12 s, checkpoint 0.11 s. The analysis and the changes are in MoveGen's Round 5. After them: 0.68,
0.72, 0.47, 0.09 and 0.04 s, and the whole file **165 s, 1.13 GB** (`lake build
ChessDemo.GothamCert`, sequential elaboration). The prototype: about 80 s and 6 GB.

Parallel elaboration (Lean's default) gave 179 s and 3.1 GB for the same file, so the lakefile sets
`Elab.async = false` for `ChessDemo`.

**The certificate checked in one piece.** `decide +kernel` on
`Game.chess.checkOnlyMove 11 p0 b7b2 cert = true` (the generated `OnlyMoveCert`, from the literal
root) did not finish in 30 minutes and was stopped by its timeout; the process stayed near 1.3–2.1
GB. Without checkpoints, every board read after the first move goes down the chain of `play`s from
the root, so the cost per node grows with the depth. The per-node file is the affordable route, as
in the prototype, whose single `check` also exhausted memory. The interpreted check
(`firstFailureOnlyMove`, the script's `--check`) takes a few seconds.

### 3. Elaboration problems met, and their fixes

1. **Heartbeats at the only-move root.** The prototype's shape put all 34 root checkpoints into one
   theorem; it ran out of heartbeats (`maxHeartbeats` 200000) after about 15 of them. Now each
   alternative has its own theorem `refutes_<uci>`.
2. **The elaborator evaluating `legalMoves`.** With `(by decide +kernel : legalMoves p = […])` at
   defender nodes and `mem_legalMoves.2 (by decide +kernel)` at attacker nodes, elaboration ran out
   of heartbeats at `whnf` on positions with many moves (all White mates in 1 of the refutations,
   38 errors): unifying `legalMoves p` with the glue lemmas' `Game.chess.moves p` unfolded
   `legalMoves p` and began to evaluate it. Oddly, the same file elaborated in parallel (Lean's
   default) reported no error, but peaked at 6.6 GB and took 438 s; why the errors were not
   reported there was not investigated. Fix: `Game.chess.moves p = […]` and `mem_chess_moves`
   (from `Chess.ChessGame.Fide`), which match syntactically. Game spec §4.1 and §4.3 now say so.
3. **A missing glue lemma.** L2.19's hypothesis at the root needed core's list lemmas; four glue
   lemmas were added (Game Round 7).

### 4. The demonstration

- `ChessDemo.GothamCert` (generated): 159 attacker nodes, 36 defender nodes, 124 mate leaves, 314
  checkpoints, 81 moves; 33 refutations (30 mates in 1, two in 2, one in 5).
- `ChessDemo.Gotham`: `gotham_winsIn`, `gotham_onlyWinningMove` (with `uci_b7b2` to pass from the
  generated literal to `uci "b7b2"`), `gotham_specWinsIn`, `gotham_specOnlyWinningMove` (G8), and
  `gotham_not_wins_white`.
- `ChessDemo.Mates`: exact `MateIn` 1 (Fool's mate), 2 and 3 (rook endings). Search in the kernel
  turned out to be memory-hungry: a first mate in 2 (`7k/8/5K2/8/8/8/8/6R1 w`) took 408 s and 7.2
  GB (its search, in `legalMoves` order, tries all 14 rook moves before the winning king move and
  visits 294 defender nodes); a mate in 3 by search alone, 48 s and 5.9 GB. A Python model of the
  search in `legalMoves` order (from `chess-perft`) was used to pick positions it visits cheaply:
  the chosen mate in 2 visits 21 defender nodes (3.3 s). For the mate in 3 the win is a certificate
  and only the minimality is a search (`mateIn_succ_iff`).
- No `native_decide`, so no `_native` theorem: the kernel version was affordable.
- `ChessDemo.Axioms`: `#print axioms` of every theorem of `Gotham` and `Mates`, and of the
  generated `winsIn` and `onlyWinningMove`, under `#guard_msgs`.

### 5. Checks

All on 2026-11-02, after the last change, one heavy job at a time:

- **Clean rebuild** (`rm -rf .lake/build`, then each target): `lake build` 8.7 s (0.84 GB peak);
  `lake build ChessTest` 160 s (3.7 GB; `ChessTest.Perft` 39 s and `ChessTest.PerftDeep` 119 s,
  against 276 s and 265 s before step 6); `lake build ChessDemo` 162 s (2.8 GB, `GothamCert` 160 s
  and `Mates` 19 s in parallel); `lake build chess-perft`. All green, no warnings in the changed
  files.
- **Forbidden constructs:** no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or
  `implemented_by` in `Chess/`, `ChessTest/` or `ChessDemo/` (the word `native_decide` occurs
  only in comments and docstrings that say it is not used).
- **Axioms:** `ChessDemo/Axioms.lean` (13 entries) and `ChessTest/Axioms.lean` +
  `AxiomsPerft.lean` (142 entries) pass; every entry is among `propext`, `Classical.choice`,
  `Quot.sound`. Mutation checks: weakening the expected axiom lists of the demo ledger fails its
  build (9 errors); changing two expected signatures of the interface ledger fails its build.
- **Docstrings:** every docstring of `Rules`, `MoveGen`, `Position`, the `Game` files,
  `ChessGame`, `Spec/Winning`, `ChessGame/Fide`, `Puzzles`, `ChessDemo.Gotham` and
  `ChessDemo.Mates` occurs word for word in its spec (script, whitespace-insensitive), and the two
  demo module docstrings too, apart from the trailing "THEOREMS Cn." tags of the `Game/Cert`
  docstrings, which the script stripped (and `**`) before comparing. [Corrected by Round 2, after
  review: Round 1 stated the check without that exception. Round 2 found, under the Game spec's §0
  rule (a leading "(Cn)" in the spec is the docstring's trailing "THEOREMS Cn."), that 6 rows had
  no tag at all, L4.8–L4.10, L4.12, L4.17, L4.18, and 4 had the trailing form, L4.19–L4.22; the
  rest, such as `checkWin_sound`'s "(C1)", already followed the rule.] `Basic` has 78 docstrings that its spec paraphrases instead of
  quoting: the known, pre-existing gap recorded by the G8 round; not changed here.
- **The generator:** regenerating after the last script change gave a byte-identical file; over
  the night's runs (about ten) the tree never changed (the same 319 nodes and moves), only the
  docstrings and layout as the script changed. `--check` reports `none`; a win-only run on
  `rookMate3` (with `--import ChessDemo.Mates`) writes a five-node file (not compiled).
- **Differential perft** of the rebuilt `chess-perft` against python-chess 1.11.2: 307 jobs (the
  standard positions to depth 3, the 16 named positions to depth 3, 150 random positions to depth
  2, 60 just after a double push and 60 with promotion or castling to depth 3): all agree.
  (`legalMoves` returns the same list as before by `legalMoves_eq_filter`, whose statement did not
  change; this is a check of the compiled program, not of the theorem.)

---

## Round 2 (2026-11-02, review fixes of Round 1)

Inputs: the review of Round 1 (two medium issues, six low). Spec first, then the generator and the
Lean, then the word-for-word check.

**Medium: DG3 said more than its statement.** The docstring of `gotham_onlyWinningMove` said that
after each of Black's other 33 moves White has a forced mate; `OnlyWinningMove` says only that
Black does not win after them. Both fixes the review offered were made. (a) DG3's docstring now
says only what the statement says ("…Black wins after it, and after none of its other 33 legal
moves."). (b) The forced mates are now a theorem: `gen_cert.py` emits, for an only-move claim,
`moves_root` (the root's moves as an explicit list, `decide +kernel`), `refutations : ∀ m ∈
Game.chess.moves R, m ≠ B → ∃ k, WinsIn .white k (R.play m)` (by `rw [moves_root]` and the
`refuted_cons` walk) and `onlyWinningMove`, now proved from them by
`of_moves_eq … moves_root … (moves_root ▸ refutations)`. `ChessDemo.Gotham` restates it as
`gotham_refuted` (DG7) and, through G8, `gotham_specRefuted` (DG8: over `Legal`, with
`SpecWinsIn`). The demo ledger gained three entries (16). The generated tree is unchanged
(regenerated: only the root's claims differ); `--check` still reports `none`. A scratch file
checked both root shapes against the old generated file first (about 3 s each).

**Medium: Game spec §4.3 said generated files name moves with `uci "…"`.** They use literal `Move`
definitions; §4.3's first bullet now allows both and names the bridge (`uci "…" = lit` by
`decide +kernel` in the restating file, as `uci_b7b2`). `scripts/README.md` says the same, and
says that the root's move-list equation is used by `rw` and `▸` (no lemma of core is named).

**Low.** The §4.1 example of the only-move root now shows the generated shape (`WinsIn .white 1`,
`w60`, and the new `moves_root`/`refutations`). ROADMAP's counts: 142 axioms-ledger entries, 30
interface entries, 16 demo-ledger entries. Mates spec §3: DM4 alone was re-measured (4.4 s
including imports, 1.6 GB peak, in a file holding only DM4; DM5 likewise 3.5 s, 1.5 GB), and the
whole file sequentially has its own row (18 s, 2.7 GB; the review measured 17.9 s and 2.75 GB).
The kernel-cache passages in DESIGN (Outcome of §7), ROADMAP step 6 and the MoveGen spec (D3.4's
note) now say what was measured and that the mechanism (reuse of a closed term's evaluation within
a declaration) is inferred from timings, not checked against the kernel's code. The process logs of
earlier rounds (MoveGen Round 5) keep their wording as the record of that round. The 'THEOREMS C3.'
tags: rather than keep an ad hoc normalisation in the check, the Game spec now writes every
per-node lemma row (L4.8–L4.10, L4.12, L4.17–L4.22) with the leading tag "(C3)" that its §0 rule
turns into the docstring's trailing "THEOREMS C3."; L4.19–L4.22 had the trailing form, the other
six none. The review counted 11 untagged rows; under the §0 rule the other tagged `Game/Cert`
rows (for example `checkWin_sound`, "(C1) …") were already consistent, so 6 were missing and 4
were in the other form. The Lean docstrings did not change.

**Low, no code change: the review of `Spec/Winning` is not independent.** Agreed. ROADMAP step 7's
"Not done" now says that a separate reviewer session must write it, and that until then no summary
for the owner should call Stage 1 closed without saying the trusted file under the G8 headlines
has had only a self-review.

**Checks** (2026-11-02, one heavy job at a time): `lake build ChessDemo` green (`GothamCert` 159 s,
`Gotham` 0.4 s, `Axioms` 1.0 s); the docstring check, with only the Game spec §0 tag rule and
whitespace normalised: the `Game` files 0 mismatches (26 through the tag rule), `ChessDemo.Gotham`
and `ChessDemo.Mates` 0, the module docstrings of `Gotham` and `Axioms` found verbatim. The full
build list is in the round's return value and ROADMAP.

## Round 3 (2026-11-02, documentation finding docs-16)

The module docstring of `ChessDemo/Mates.lean` was titled "Small mates, proved by search" and said
the claims were "decided by the bounded search", while its own implementation notes say the mate
in 3 proves its win by a certificate (`Game.checkWin_sound`) and only its minimality by search.
Spec first, then Lean: the docstring quoted in `docs/spec/ChessDemo.Mates.md` §0 and the Lean
module docstring now read "Small exact mates", and say that the absence of a shorter mate is
decided by search, as is the mate itself in 1 and in 2, while the mate in 3 is proved by a checked
certificate. The root docstring of `ChessDemo.lean` (no spec) now says "small exact mates (their
minimality proved by search)". No statement or proof changed. Checked: the module docstring and
the eight declaration docstrings of `Mates` appear word for word (whitespace normalised) in the
spec; `lake build ChessDemo` green (19 s, 2.77 GB maximum resident set size).

## Round 4 (2026-11-02, documentation finding gotham-1, low)

The trust note of `ChessDemo/Gotham.lean` (module docstring, implementation notes) and the
paragraph under the header of `docs/spec/ChessDemo.Gotham.md` said that a reader of the three
`spec` theorems trusts the notation "through `fen_eq_iff` and `uci_eq_iff`" but "not the game
layer". The right-hand side of `fen_eq_iff` is `p.Sane ∧ IsFEN s p`, and `Position.Sane`, `IsFEN`,
`ClockFields`, `IsNumeral` and the writer `Position.fenFields` are defined in `Chess/ChessGame.lean`,
whose own docstring lists them as trusted. Nothing was hidden (the clause about `fen_eq_iff` took
them in), but the sentence contradicted that list. Spec first, then Lean: both places now name
these definitions (and the "Writing" helpers `Position.fenFields` uses), say that `Move.toUCI` is
in `Chess.Position`, and narrow the untrusted part to the generator `legalMoves`, the game instance
`Game.chess`, the parsers, the generated file and the engine. No statement or proof changed.
Checked: the module docstring of `Gotham.lean` is verbatim the spec's §0 block, and the eight
declaration docstrings appear word for word (whitespace normalised); `lake build ChessDemo` and
`lake build` green.
