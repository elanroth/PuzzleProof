# Board representation and move generation

Research note for the `Chess` library (Lean 4.28.0, core + Std, no Mathlib).
Question: which board representations and move-generation techniques give an elegant
*specification*, which belong in an *optimized implementation*, and how a refinement proof
between the two layers can look.

Each section keeps **Facts** (what the sources say, with the source tag in brackets, see
[Sources](#sources)) apart from **Judgment** (my assessment for this project). Section 3 records
small Lean experiments I ran on this machine with the project's toolchain. They are measurements,
not library code.

Related notes: `docs/research/theorem-landscape.md` §3.3 (the move-generation soundness,
completeness and refinement theorems) and `docs/research/game-theory.md`.

---

## 0. Summary

- A **bitboard** is a 64-bit word read as a set of squares. Union, intersection, complement and
  difference are single machine instructions [CPW-SET]. That *is* a finite-set representation,
  so it can serve as the library's `SquareSet`. Membership is `getLsbD`, and the set-algebra
  lemmas come from Lean core's `BitVec` theory.
- **Leapers** (pawn attacks, knights, kings) are computed by shifting a whole set at once with a
  file mask that stops wrap-around [CPW-SET, CPW-KNIGHT]. Mathematically each one is the *image
  of a set under a partial translation of the board*. These maps distribute over union, so a
  refinement proof splits into (a) a compositional "additive" lemma and (b) a finite check on the
  64 singletons. Section 3 shows both parts kernel-checked in about 1.5 s for the knight.
- **Sliders** have one clear specification: "squares along a ray up to and including the first
  occupied square." The *classical ray* method [CPW-CLASSIC] and the `o^(o-2r)` subtraction trick
  [CPW-SUB] implement that sentence almost word for word. Hyperbola quintessence [CPW-HQ],
  kindergarten [CPW-KG], rotated [CPW-ROT], magic [CPW-MAGIC] and PEXT [CPW-BMI2] bitboards are
  progressively more table-driven speed tricks. They belong in an optional implementation layer, if
  anywhere.
- **Specification board**: a total map `Square → Option Piece`, which is the mailbox in its purest
  form [CPW-BR]. **Implementation board**: two colour bitboards plus six piece-type bitboards (the
  "by colour / by type" layout), related to the specification by an abstraction function.
- **Zobrist hashing** [CPW-ZOB] and **perft** [CPW-PERFT] are tools, not definitions. A hash only
  speeds up a map whose keys are still compared by equality, so it never touches soundness. Perft
  counts become regression theorems and differential tests.

---

## 1. Square numbering

**Facts.** The Chess Programming Wiki's examples mostly use *Little-Endian Rank-File* (LERF)
numbering: `square = 8*rank + file`, with a1 = 0, b1 = 1, ..., h8 = 63 [CPW-MAP]. Compass
offsets: N +8, S −8, E +1, W −1, NE +9, NW +7, SE −7, SW −9 [CPW-MAP, CPW-SET]. Mirrors are XORs
on the index: `sq ^ 7` flips files, `sq ^ 56` flips ranks, `sq ^ 63` does both [CPW-MAP]. The
prototype also uses `s = rank*8 + file` with a1 = 0 (`prototype/ChessProof/Basic.lean`).
Sebastian Lague's engine uses the same indexing [YT-LAGUE1].

**Judgment.** Use LERF, because it is the convention every source, FEN tool and perft reference
assumes. In the spec, though, a square should be a pair `⟨file : Fin 8, rank : Fin 8⟩` and not a
bare index. The rules of chess are stated in file and rank differences, and `Fin 8` arithmetic
says "off the board" honestly. The index `8*rank + file : Fin 64` should be one named bijection
(`Square.toFin` / `Square.ofFin`) with its round-trip lemmas proved once. Colour symmetry
("Black's moves are White's moves mirrored") then becomes the involution `sq ↦ sq ^ 56`, which is
convenient for halving case analyses later.

---

## 2. Facts from the sources

### 2.1 Taxonomy of board representations

- **Square-centric**: each square stores what is on it. The variants are the 8×8 array
  ("mailbox"), the 10×12 board, 0x88 and vector attacks [CPW-BR].
  - *10×12*: the 8×8 board sits inside a 120-entry array with sentinel border squares. Two border
    ranks are needed because of the knight's reach. TSCP's offsets are knight ±8, ±12, ±19, ±21;
    bishop ±9, ±11; rook ±1, ±10. Index translation goes through `mailbox[120]` and
    `mailbox64[64]` [CPW-10x12].
  - *0x88*: 128 entries indexed `16*rank + file`. A square is off the board iff
    `sq & 0x88 ≠ 0`. The difference `0x77 + a − b` is unique for every pair of squares, so a
    240-entry table can answer "can a piece of type X on a ever attack b?" [CPW-0x88].
- **Piece-centric**: for each piece, store where it is. The variants are piece lists, piece sets
  and bitboards [CPW-BR].
- **Hybrid**: bitboard engines usually also keep an 8×8 array to answer "what is on this square?",
  and array engines add piece lists so they need not scan the board [CPW-BR].
- **Full position**: piece placement, side to move, castling rights, en-passant target and the
  reversible-move (50-move) counter. Repetition needs the game history [CPW-BR]. The prototype
  leaves out the 50-move and repetition rules (`prototype/README.md`).

### 2.2 Bitboards as sets

| English (sets) | Bitboard | Source |
|---|---|---|
| A ∩ B | `a & b` | [CPW-SET] |
| A ∪ B | `a \| b` | [CPW-SET] |
| complement of A | `~a` | [CPW-SET] |
| B \ A | `~a & b` | [CPW-SET] |
| symmetric difference | `a ^ b` | [CPW-SET] |
| A ⊆ B | `(a & b) == a` | [CPW-SET] |
| disjoint | `(a & b) == 0` | [CPW-SET] |
| {sq} | `1 << sq` | [CPW-SET] |
| smallest element of A (LS1B), isolated | `x & -x` | [CPW-SET] |
| A minus its smallest element | `x & (x - 1)` | [CPW-SET] |
| squares below sq | `(1 << sq) - 1` | [CPW-SET] |

To make or unmake a move, XOR the from- and to-square bits into the moving piece's board, and
toggle the captured piece's board on the to-square [CPW-SET]. Lague builds this up step by step in
his second video, and points out that castling, en passant and promotion each touch an extra
bitboard [YT-LAGUE2]. He also shows that a bitboard alone cannot say *which* piece is on a square,
which is why an engine keeps several of them [YT-LAGUE2]. Bartek Spitza's overview makes the same
basic point. Testing "is this square occupied by a white pawn?" is one AND with a nonzero test, and
twelve bitboards (one per coloured piece type) represent a whole board [YT-SPITZA].

### 2.3 Leapers by shifting whole sets

- **One step** (post-shift masks), with `notAFile = 0xfefefefefefefefe` and
  `notHFile = 0x7f7f7f7f7f7f7f7f` [CPW-SET]:
  `north = b << 8`, `south = b >> 8`, `east = (b << 1) & notAFile`,
  `west = (b >> 1) & notHFile`, `ne = (b << 9) & notAFile`, `nw = (b << 7) & notHFile`,
  `se = (b >> 7) & notAFile`, `sw = (b >> 9) & notHFile`.
  Equivalently, mask the source with the mirrored file mask first and then shift [CPW-SET].
- **Knight**: eight shifts (±6, ±10, ±15, ±17), each with a one- or two-file mask. A two-stage
  version first computes one-file and two-file horizontal neighbours (`h1`, `h2`) and then shifts
  them vertically: `(h1<<16) | (h1>>16) | (h2<<8) | (h2>>8)` [CPW-KNIGHT].
- **Pawn pushes** (White): `single = north(wpawns) & empty`,
  `double = north(single) & empty & rank4` with `rank4 = 0x00000000FF000000` [CPW-PAWN].
- **Wrap-around bug in practice.** When Lague switched pawn captures to bit shifts, the pawns gained
  "a new sneak attack where they can warp around the edge of the board" [YT-LAGUE2]. This is
  exactly the failure the file masks exist to prevent, and exactly what a refinement theorem rules
  out.
- **Patterns as masks.** Lague detects passed and isolated pawns with precomputed masks ("forward
  mask ∧ triple-file mask ∧ enemy pawns = 0") [YT-LAGUE2]. This is the "moves and patterns become
  vectors in 64-bit words" idea: a chess concept becomes a set, and testing it becomes set algebra.

### 2.4 Sliding pieces

| Technique | Idea | Tables / constants | Source |
|---|---|---|---|
| Loop over rays (mailbox) | step square by square until edge or piece | precomputed squares-to-edge | [YT-LAGUE1], prototype `rayHit`/`slide` |
| Classical ray | `blk = ray[d][sq] & occ`; first blocker `b` = bitscan forward (positive rays) or reverse (negative); `attacks = ray[d][sq] ^ ray[d][b]` | `ray[8][64]`, 4 KB | [CPW-CLASSIC] |
| `o^(o-2r)` | on a line-masked occupancy `o`, a slider bit `r`: `o ^ (o - 2r)` gives the positive-direction ray up to and including the first blocker. The borrow ripples through empty squares | line masks only | [CPW-SUB] |
| Hyperbola quintessence | positive half by `o-2r`, negative half by the same trick on the reversed board: `(o-2r) ^ reverse(o'-2r')`. Files and diagonals use a byte swap. Ranks need a different method, because there is no cheap bit reversal | per-square line masks | [CPW-HQ] |
| Rotated bitboards | keep the occupancy in 4 orientations so every line's bits are contiguous, then look up attacks. Hyatt / Crafty (1995 posts, ICCA J. 1999) | about 0.5 MB early on, later shrunk 4× | [CPW-ROT] |
| Kindergarten | mask the line, multiply by `0x0202020202020202`, `>> 58` gives a 6-bit index, look up `fillUpAttacks[file][idx]`, mask again. Files use a separate multiplier and table | 2 × 4 KB | [CPW-KG] |
| Magic | `idx = ((occ & mask[sq]) * magic[sq]) >> (64 - n)`. Magics are found by trial and error. Constructive collisions allowed. Hansen / Kannan ("fancy") / Purves (names) | plain about 2.3 MB, fancy about 800 KB | [CPW-MAGIC], [YT-LAGUE2], [YT-CMK] |
| PEXT | `idx = pext(occ, mask[sq])`, needs BMI2. Slow on AMD before Zen 3 | about 840 KB (PDEP variant about 210 KB) | [CPW-BMI2] |

Points from the videos:
- Lague's first magic attempt (a general-purpose dictionary from occupancy to moves) made move
  generation *slower*. A custom table indexed by magic multiplication then cut his lookup
  micro-benchmark from about 762 ms to about 53 ms [YT-LAGUE2]. His magics come from a brute-force
  random search that is saved to a file and pasted into the source [YT-LAGUE2]. The Code Monkey King
  series ("Bitboard CHESS ENGINE in C") has separate episodes on masking relevant occupancy, on
  generating magic candidates and on brute-forcing magics [YT-CMK].
- Magic numbers are *found, not derived*. The table is correct because the search verified it,
  not because of any reason a reader can follow [CPW-MAGIC, YT-LAGUE2].

### 2.5 Legality, move encoding and bug classes

- **Pseudo-legal then filter**: play each move and reject it if the mover's king can then be
  captured. Lague calls this "a little gross" but it is the simplest correct method [YT-LAGUE1].
  The prototype does the same (`legal = pseudo.filter (kingSafe ∘ play)`).
- **Faster legality**: keep the opponent's attack set, a check mask (squares that block or
  capture the checker) and pin rays, and generate only legal moves [YT-LAGUE1].
- **Bug classes perft found for Lague** [YT-LAGUE1]:
  - Capturing a rook on its home square must remove that side's castling right.
  - A pinned pawn becomes free once the pin is broken.
  - An en-passant capture can uncover a rank attack on the king (both pawns leave the rank).
- **Move encoding**: 16 bits per move, made of a 6-bit from-square, a 6-bit to-square and a 4-bit
  flag (promotion and so on). Move 0 (a1→a1) doubles as the null move, which once caused a bug
  [YT-LAGUE2].

### 2.6 Zobrist hashing

**Facts** [CPW-ZOB]. Introduced in Zobrist's 1970 technical report. One random key per (piece,
square) (12 × 64), one for Black to move, 4 (or 16) for castling rights and 8 for the en-passant
file: 781 keys in all. The hash is the XOR of the keys of the features present. A move updates it
incrementally by XORing out the old features and XORing in the new ones, and XOR being its own
inverse makes unmake free. 64-bit keys are standard, and collisions become likely after about
2^32 positions (birthday bound). Lague uses Zobrist keys for his transposition table and says he
does nothing about collisions: "if we want the speed we have to live in fear" [YT-LAGUE1].

### 2.7 Perft

**Facts** [CPW-PERFT]. Perft counts the leaf nodes of the legal-move tree at a fixed depth. Mated
or stalemated positions before the last ply add nothing, and the 50-move rule, repetition and
insufficient material are ignored. *Divide* prints the count for each root move. That localizes a
bug, and Stockfish's `go perft` prints a divide, which Lague used in exactly this way [YT-LAGUE1].
Bulk counting returns the number of legal moves at depth 1 instead of making each one.

Reference counts [CPW-PERFT-R]:

| Position | FEN | d1 | d2 | d3 | d4 | d5 |
|---|---|---|---|---|---|---|
| Initial | `rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1` | 20 | 400 | 8,902 | 197,281 | 4,865,609 |
| Kiwipete | `r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -` | 48 | 2,039 | 97,862 | 4,085,603 | 193,690,690 |
| Pos. 3 | `8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1` | 14 | 191 | 2,812 | 43,238 | 674,624 |
| Pos. 4 | `r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1` | 6 | 264 | 9,467 | 422,333 | 15,833,292 |
| Pos. 5 | `rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8` | 44 | 1,486 | 62,379 | 2,103,487 | 89,941,194 |
| Pos. 6 | `r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10` | 46 | 2,079 | 89,890 | 3,894,594 | 164,075,551 |

### 2.8 Prior formalizations

- **lean-across-the-board** (Lean 3 + mathlib) [LATB]: a board is an indexed family of pieces
  plus a `playfield` (a matrix of optional indices), with fields requiring that every piece is on
  the board and that no two pieces share a square. Its own notes say this rules out captures.
  Lesson: putting invariants into the type is elegant, but it can make the moves themselves
  impossible to state.
- **Lean-Hackathon** (Lean 4) [HACK], read locally from `~/chess-lean-research/Lean-Hackathon`: the
  board is `Vector (Vector (Option ColourPiece) 8) 8`. Moves are checked *relationally*
  (`isStraight`, `isDiagonal`, `isPathClear from to`, `isValidKnightMove from to`), and
  `LegalProofs.lean` has 23 theorems. This is the declarative "is this move geometrically
  allowed?" style a specification layer wants.
- **dwrensha/Chess** is listed on Reservoir as "an (incomplete) implementation of chess in Lean 4"
  that depends on mathlib [RES-DW]. The GitHub URL returned 404 when I tried it, so I could not
  check its representation.
- **Isabelle/HOL KRK**: Janičić, Marić and Maliković (LMCS 2019) proved a KRK winning strategy
  correct on n×n boards, and argue that different automated and interactive methods "work best
  together and in synergy" [ARX-KRK].
- I found no machine-checked refinement proof of a *bitboard* move generator. A 2025 paper on
  rotated bitboards validates its generator with perft only [ARX-ROT].

### 2.9 Lean 4.28 core: what is available without Mathlib

Checked in the installed toolchain sources
(`~/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean`) and by running small files:
- `BitVec w` has `&&&`, `|||`, `^^^`, `~~~`, `<<<`, `>>>`, `-`, `*`, plus `reverse`, `clz`,
  `ctz` and `cpop` (popcount) (`Init/Data/BitVec/Basic.lean`). It has a large lemma library
  (`getLsbD_*`, `shiftLeft_or_distrib`, `ushiftRight_or_distrib`, `and_or_distrib_right`, ...).
- `UInt64` wraps `BitVec 64` (`UInt64.toBitVec`) and compiles to a native machine word.
  **Gotcha**: `UInt64` shift amounts are taken mod 64, so `(1 : UInt64) <<< 64 = 1`, while
  `(1#64) <<< 64 = 0` (checked with `#eval`). Any refinement from `BitVec` to `UInt64` must keep
  shift amounts below 64.
- `bv_decide` (Std, from LeanSAT) bit-blasts `BitVec`/`Bool` goals to SAT, runs the bundled
  CaDiCaL, and checks the LRAT certificate. Its proofs rely on compiled code: in 4.28,
  `#print axioms` shows a `..._native.bv_decide.ax_*` axiom [LEAN-BVD, LEAN-412]. It also handles
  `UInt64` goals (checked).
- `decide +kernel` on `BitVec 64` arithmetic is fast, because the kernel's `Nat` operations
  (`land`, `lor`, `xor`, shifts, `mod`) are GMP-accelerated. The prototype's nibble-packed `Nat`
  relied on the same fact.
- Finite sets without Mathlib: no `Finset`, but `Std` provides `HashSet`, `TreeSet` and the
  extensional `ExtHashSet` / `ExtTreeSet` (directory listing of `Std/Data`).

---

## 3. Experiments (Lean 4.28.0, `lean` CLI, this Mac)

Throwaway files, not library code, kept outside the repo in the session scratchpad.

1. **Knight shift formula vs. geometric spec, kernel only.** With `BB := BitVec 64` and the
   two-stage knight formula from [CPW-KNIGHT], and the spec "|Δfile|, |Δrank| = {1, 2}":
   ```lean
   theorem knightBB_spec : ∀ s t : Fin 64,
       (knightBB (1#64 <<< s.val)).getLsbD t.val = knightJump s t := by decide +kernel
   ```
   This checks all 4,096 (from, to) pairs in about 1.3 s of CPU. Axioms: `propext`,
   `Quot.sound` only.
2. **Union law, kernel only, compositionally.** Define
   `Additive f := ∀ a b, f (a ||| b) = f a ||| f b`. Prove it once each for `(· <<< k)`,
   `(· >>> k)` and `(· &&& m)`, then show it is closed under composition and pointwise `|||`. With
   the knight written as `side1`/`side2` helpers, without `let`, `knightBB_additive` is a one-line
   term built from those combinators. It checks in about 0.2 s, kernel only.
   *Negative result*: the same goal proved with `simp only [distrib lemmas]` + `ac_rfl` on a
   `let`-based definition with inline 64-bit literal masks **timed out** (whnf, 200k heartbeats).
   The `let`s become `have`s that rewriting cannot reach, and the defeq fallback unfolds the
   literals.
3. **The subtraction trick is "LS1B" in disguise** (`bv_decide`, about 0.3 s): with the slider on
   bit 0 of `o`, if `x := o &&& ~~~1 ≠ 0` then
   `o ^^^ (o - 2) = ((x &&& -x) <<< 1) - 2`, the interval (0, first blocker]. So
   [CPW-SUB]'s trick and [CPW-CLASSIC]'s "first blocker" are provably the same function. This
   relies on the `bv_decide` native axiom.
4. `bv_decide` proved `(a ||| b) <<< 8 = (a <<< 8) ||| (b <<< 8)` for `UInt64` and the knight
   union law on raw literals instantly. It is a good fallback where the native axiom is acceptable.

**Proof pattern that came out of this (judgment).** For any leaper:
`t ∈ attacks B ↔ ∃ s ∈ B, Step s t` follows from
(i) `attacks` is additive and `attacks ∅ = ∅` (compositional, kernel),
(ii) `B = ⋃_{s ∈ B} {s}` (one generic lemma about bitboards), and
(iii) the 64 singleton cases (`decide +kernel`, seconds).
No SAT solver and no compiler need to be trusted.

---

## 4. Judgments: each idea for this project

Scale: **Spec** (belongs in the definition of chess), **Impl** (optimized layer behind a
refinement theorem), **Tool** (testing or search infrastructure, outside the trusted core),
**Skip**.

| Idea | Verdict | Why |
|---|---|---|
| `Square = ⟨file, rank⟩ : Fin 8 × Fin 8` | Spec | Rules are stated in file and rank differences; "off board" is `Option` from a checked offset. |
| `Square.offset (df dr : Int) : Square → Option Square` | Spec | One partial translation explains every leaper, ray and pawn move. |
| Mailbox board `Square → Option Piece` | Spec | Total by construction: no "two pieces on one square" invariant to maintain. "What is on e4?" is function application. Extensional equality via `funext`. |
| Bitboard as `SquareSet` (`BitVec 64` + `Membership`) | Spec *and* Impl | It is a faithful finite set. Using it in the spec for "attacked squares", "empty squares" and so on costs nothing and makes refinement trivial for those parts. |
| 12 per-piece bitboards | Impl (prefer by-colour + by-type) | 12 boards need 66 pairwise-disjointness facts. 2 colour + 6 type boards need "colours disjoint, types pairwise disjoint, ⋃colours = ⋃types": fewer and more readable invariants. |
| Mailbox 10×12, 0x88 | Skip | Sentinel tricks for off-board tests in C. `Option` from `Square.offset` does that job with types. The 0x88 difference uniqueness is a neat fact but not needed. |
| Piece lists | Skip (maybe Impl later) | They duplicate information, which adds a consistency invariant. Bitboard serialization (`ctz` + clear LS1B) already lists pieces. |
| One-step shifts with file masks | Impl, with a per-direction theorem `mem_shift : t ∈ shift d B ↔ ∃ s ∈ B, s.offset d = some t` | Exactly "image under a partial translation". The mask is the proof obligation "no wrap-around", and Lague's warping pawns [YT-LAGUE2] are the bug it prevents. |
| Knight/king/pawn shift formulas | Impl | Proved by the additive + singleton pattern (§3). |
| Ray walk ("slide until blocked") | Spec | The English rule itself. Write it as a relation (`SlideReach o s t d`: t is on ray d from s and every square strictly between is empty), as the Lean-Hackathon `isPathClear` does, and/or as a structurally recursive function over at most 7 steps. |
| Classical ray (ray table + first blocker) | Impl, first choice | One lemma per direction ("first blocker = LS1B / MS1B of the ray ∩ occupancy"). The 4 KB table is defined by the spec (`ray d s` = spec ray on an empty board), so the table needs no separate trust. |
| `o^(o-2r)` / hyperbola quintessence | Impl, optional | §3 shows the trick equals the classical LS1B form. HQ needs `reverse` (in core) and leaves ranks to another method [CPW-HQ]. Elegant for a talk, harder to read than "first blocker". |
| Kindergarten | Impl, optional | Fixed constants and small tables, so verification is a bounded finite check. A reasonable fast path if ever needed. |
| Rotated bitboards | Skip | Four occupancy copies to keep consistent on every move [CPW-ROT]. Superseded in practice. |
| Magic / PEXT | Skip in Lean (or Tool) | Constants found by search [CPW-MAGIC, YT-LAGUE2], with no reason a reader can follow. Checking the tables is a large finite computation. PEXT has no Lean primitive. The speed belongs in the untrusted engine (Stockfish), not in the checker. |
| Pseudo-legal + king-safety filter | Spec | It is literally the FIDE definition ("a move is illegal if it leaves one's own king attacked"), so it is the right `legal` definition. |
| Check / pin masks | Impl (later) | A pure speed optimisation. Its correctness theorem is "equals the filtered list", which [YT-LAGUE1] shows is the bug-prone part (pins broken by en passant). |
| 16-bit move encoding | Impl / I/O | The spec move should be a structure (`from`, `to`, `promo : Option PromoPiece`) or an inductive with castling and en passant as explicit constructors. Use the packed form only for UCI and certificate I/O, with a round-trip lemma. Avoid "a1→a1 = null move" sentinels [YT-LAGUE2]. |
| Zobrist | Tool | Use it only as the `Hashable` instance of a `HashMap` keyed by positions compared with `DecidableEq`, so collisions can cost time but never soundness. The incremental update `hash (play p m) = hash p ^^^ δ p m` is provable if ever needed. |
| Perft | Tool + regression theorems | `theorem perft_start_3 : perft 3 start = 8902` style facts (kernel or `native_decide`, labelled). Use divide against python-chess or Stockfish for differential testing (the prototype's `scripts/` and `lake exe perft` already do this). |

### 4.1 What the refinement theorems should look like

Write `abs : Impl.Position → Spec.Position`, with the mailbox spec board
`abs.board sq = the piece whose colour bitboard and type bitboard both contain sq`. Then:

1. **Representation**: `WF bb → (abs bb).board` is well defined (colours disjoint, types disjoint,
   unions agree), and `bb.pieceAt sq = (abs bb).board sq`.
2. **Set layer** (per technique):
   `t ∈ Impl.knightAttacks B ↔ ∃ s ∈ B, Spec.KnightStep s t`;
   `t ∈ Impl.rookAttacks s occ ↔ ∃ d ∈ rookDirs, Spec.SlideReach occ s t d`.
3. **Move generation**:
   `m ∈ Impl.legalMoves bb ↔ m ∈ Spec.legalMoves (abs bb)`, stated up to permutation, or as
   list equality if the implementation emits moves in the spec's canonical order. Membership is
   easier to prove. Equality is what certificate checking wants, because then `Spec`-level
   theorems transfer to fast `Impl` evaluation by rewriting.
4. **Make move**: `WF bb → abs (Impl.play bb m) = Spec.play (abs bb) m` for legal `m`.

With 3 and 4, a game-tree theorem proved by evaluating the fast implementation
(`decide`/`native_decide` on `Impl`) transfers to the spec by `simp [← refine]`. That is the
"Stockfish proposes, Lean disposes" pipeline with a readable trusted base.

---

## 5. Lessons from the prototype (`prototype/`)

- **What worked**: one `Nat` of 64 nibbles makes kernel reduction fast, because GMP shifts and
  masks are cheap. It was fast enough for a kernel-only mate in 11 (320 per-node theorems, about
  80 s, about 6 GB, `prototype/README.md`). Perft agreement with python-chess on the standard
  suite was the correctness evidence.
- **What should change**:
  - Everything is a `Nat`: piece codes `0..14` with `kind = c &&& 7`, square `64` for "none",
    castling bits `0..3`, `promo = 0` for none, and direction offsets biased by +2 so that `0..4`
    means −2..2 (`shift s df dr`). Each of these is a translation hazard with no type to catch
    mistakes.
  - `play` hard-codes castling as `(4,6)`, `(4,2)`, `(60,62)`, `(60,58)`, and `rightsMask` lists
    magic numbers (`12`, `13`, `14`, ...).
  - The generator was *tested*, not proved, against any declarative rule set.
- **Carry forward**: the *kernel performance insight* (bitwise `Nat`/`BitVec` operations are fast
  in the kernel) and the perft harness. Rebuild everything else as typed spec + `BitVec`
  implementation + refinement. The §3 timings suggest a `BitVec 64` implementation keeps most of
  the prototype's kernel speed while being far easier to state and prove things about.

---

## Recommendations for this library

1. **Two layers, one abstraction function.**
   - `Chess.Spec.*`: `Square := ⟨file : Fin 8, rank : Fin 8⟩`, `Board := Square → Option Piece`,
     a structured `Move`, and relational move rules (`KnightStep`, `KingStep`,
     `SlideReach occ s t d`, pawn rules), with `legal` = pseudo-legal + "own king not attacked
     afterwards".
   - `Chess.Bitboard.*`: by-colour + by-type `BitVec 64` boards, shift/mask leapers,
     classical-ray sliders.
   - The refinement theorems of §4.1 connect them.
2. **Make `SquareSet` a thin structure over `BitVec 64`** with `Membership Square SquareSet`,
   `ext`, and `mem_inter` / `mem_union` / `mem_compl` / `mem_sdiff` / `mem_singleton` simp lemmas.
   Use it in the spec as well (attacked squares, empty squares). Then "bitboard = finite set" is a
   definition, not a theorem.
3. **One primitive for geometry**: `Square.offset (df dr : Int) : Square → Option Square`. Prove
   the bitboard `shift d` is its image (`mem_shift`). Derive the knight, king and pawn-attack
   tables and the classical ray table from this one primitive, so no table carries independent
   trust.
4. **Sliders**: implement the classical ray method first. Write a single lemma "first blocker on a
   positive ray = LS1B of `ray ∩ occ`" (MS1B / `clz` for negative rays) and prove it against
   `SlideReach`. Treat `o^(o-2r)` / hyperbola quintessence as an optional later optimisation,
   which §3 shows is provably equal. **Do not** implement magic or PEXT bitboards in Lean.
5. **Proof style for bitboard lemmas**:
   - Write bitboard functions as compositions of small named maps (no `let`, named masks).
   - Prove algebraic laws compositionally (the `Additive` combinators of §3).
   - Discharge finite residues with `decide +kernel`.
   - Use `bv_decide` only where the native axiom is acceptable, and label it.
   - Keep a trust ledger per theorem: kernel / `bv_decide` / `native_decide`.
6. **Machine words last.** Develop on `BitVec 64`. If compiled speed matters later, add a `UInt64`
   instance via `UInt64.toBitVec` and prove the shift-amount < 64 side conditions, because
   `UInt64` shifts are mod 64.
7. **Moves are data, not codes.** Use `Move` as a structure (or an inductive with explicit castling
   and en-passant constructors, decided in `docs/spec`). Keep the 16-bit packing and UCI strings
   to an I/O module with round-trip lemmas.
8. **Position** = board + side to move + castling rights (a 4-field `Bool` structure) +
   en-passant square (`Option Square`) + halfmove clock. Treat the repetition history explicitly
   or not at all, and say which in the spec. The prototype's "no 50-move, no repetition"
   simplification should be visible in the type, not implied.
9. **Perft as regression theorems**:
   - The six reference positions of §2.7 at small depths as named theorems, with their trust
     level stated.
   - Divide-based differential testing against python-chess or Stockfish kept as an untrusted
     `lake exe` tool.
   - Encode Lague's three bug classes (castling right lost when the rook is captured, pin broken,
     en passant uncovering a rank check) as small named example positions.
10. **Zobrist only as a `Hashable` instance** for search and certificate deduplication, never as a
    position identity inside a soundness argument.

---

## Sources

Web pages (fetched 2026-11-01):
- [CPW-SET] Chess Programming Wiki, *General Setwise Operations*: https://www.chessprogramming.org/General_Setwise_Operations
- [CPW-MAP] CPW, *Square Mapping Considerations*: https://www.chessprogramming.org/Square_Mapping_Considerations
- [CPW-BR] CPW, *Board Representation*: https://www.chessprogramming.org/Board_Representation
- [CPW-10x12] CPW, *10x12 Board*: https://www.chessprogramming.org/10x12_Board
- [CPW-0x88] CPW, *0x88*: https://www.chessprogramming.org/0x88
- [CPW-KNIGHT] CPW, *Knight Pattern*: https://www.chessprogramming.org/Knight_Pattern
- [CPW-PAWN] CPW, *Pawn Pushes (Bitboards)*: https://www.chessprogramming.org/Pawn_Pushes_(Bitboards)
- [CPW-CLASSIC] CPW, *Classical Approach*: https://www.chessprogramming.org/Classical_Approach
- [CPW-SUB] CPW, *Subtracting a Rook from a Blocking Piece*: https://www.chessprogramming.org/Subtracting_a_Rook_from_a_Blocking_Piece
- [CPW-HQ] CPW, *Hyperbola Quintessence*: https://www.chessprogramming.org/Hyperbola_Quintessence
- [CPW-ROT] CPW, *Rotated Bitboards*: https://www.chessprogramming.org/Rotated_Bitboards
- [CPW-KG] CPW, *Kindergarten Bitboards*: https://www.chessprogramming.org/Kindergarten_Bitboards
- [CPW-MAGIC] CPW, *Magic Bitboards*: https://www.chessprogramming.org/Magic_Bitboards
- [CPW-BMI2] CPW, *BMI2* (PEXT bitboards): https://www.chessprogramming.org/BMI2
- [CPW-ZOB] CPW, *Zobrist Hashing*: https://www.chessprogramming.org/Zobrist_Hashing
- [CPW-PERFT] CPW, *Perft*: https://www.chessprogramming.org/Perft
- [CPW-PERFT-R] CPW, *Perft Results*: https://www.chessprogramming.org/Perft_Results
- [LEAN-BVD] Lean API docs, `Lean.Elab.Tactic.BVDecide`: https://lean-lang.org/doc/api/Lean/Elab/Tactic/BVDecide.html
- [LEAN-412] Lean 4.12.0 release notes (bv_decide): https://lean-lang.org/blog/2024-10-3-lean-4120
- [LATB] lean-across-the-board docs: https://lean-across-the-board.readthedocs.io/ and source https://github.com/Julian/lean-across-the-board/blob/main/src/chess/board.lean
- [HACK] Lean-Hackathon chess model: https://github.com/aastha-guptaa/Lean-Hackathon (read from the local clone `~/chess-lean-research/Lean-Hackathon`)
- [RES-DW] Reservoir, dwrensha/Chess: https://reservoir.lean-lang.org/@dwrensha/Chess
- [ARX-KRK] Janičić, Marić, Maliković, *Computer-Assisted Proving of Combinatorial Conjectures Over Finite Domains: A Case Study of a Chess Conjecture*, LMCS 15(1), 2019: https://arxiv.org/abs/1801.07528
- [ARX-ROT] Buchner, *Rotated Bitboards and Reinforcement Learning in Computer Chess and Beyond*, 2025: https://arxiv.org/abs/2503.10822v1

Videos (auto-captions fetched with yt-dlp and read in full or searched):
- [YT-LAGUE1] Sebastian Lague, *Coding Adventure: Chess*: https://www.youtube.com/watch?v=U4ogK0MIzqk
- [YT-LAGUE2] Sebastian Lague, *Coding Adventure: Making a Better Chess Bot*: https://www.youtube.com/watch?v=_vqlIPDR2TU
- [YT-SPITZA] Bartek Spitza, *The Fascinating Programming of a Chess Engine*: https://www.youtube.com/watch?v=w4FFX_otR-4
- [YT-CMK] Chess Programming (Code Monkey King), *Bitboard CHESS ENGINE in C* series, e.g. masking rook attacks https://www.youtube.com/watch?v=F6zdC0W0kGg, magic candidates https://www.youtube.com/watch?v=KqWeOVyOoyU, brute-force magics https://www.youtube.com/watch?v=UnEu5GOiSEs (titles only; the series is listed at https://www.chessprogramming.org/BBC)

Local:
- Prototype: `prototype/README.md`, `prototype/ChessProof/Basic.lean`
- Lean core sources: `~/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Init/Data/BitVec/`, `.../Std/Data/`
