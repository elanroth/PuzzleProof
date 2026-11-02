# Lean engineering notes for `Chess` (Lean 4.28.0, core + Std, no Mathlib)

Researcher: lean-engineering. Date: 2026-11-01.

This note answers one question: which Lean 4.28 engineering choices make a chess library that
is faithful, readable, provable, and fast enough to check certificates? It covers evaluation
tactics, kernel arithmetic, machine words, square and board representations, deriving,
recursion, the Std toolbox, and conventions. The last section gives recommendations.

Every section keeps two kinds of statement apart:

- **Fact**: from Lean sources or documentation (cited), or measured here (numbers given).
- **Judgment**: my reading of what the facts mean for this library.

---

## 0. Method and environment

- Lean `4.28.0` (commit `7e01a1bf`, arm64-apple-darwin), Apple M4, 16 GB RAM.
- Each experiment is a standalone `.lean` file, run with `lean FILE` under `/usr/bin/time -l`
  with a 60 s alarm. Files lived in the session scratchpad, outside the library.
- **Baseline:** an empty file takes **0.30 s** wall time (0.26–0.36 s) and about 345 MB RSS
  (resident memory). `import Std.Tactic.BVDecide` adds about 0.15 s. The numbers below are
  wall times; subtract roughly 0.3 s to get the cost of the work itself.
- Each figure comes from one run, so treat differences under about 0.1 s as noise.
- `decide +kernel` builds a separate auxiliary theorem for each use. The kernel's reduction
  cache does not carry over between declarations, so one theorem per measured operation
  gives a fair per-operation cost.
- **Fixed cost:** 400 trivial `decide +kernel` theorems took 0.95 s in total, about
  **1.6 ms per theorem**.

---

## 1. Evaluation tactics: `decide`, `decide +kernel`, `native_decide`, `rfl`, `bv_decide`

### Facts from the 4.28 sources

These come from the docstrings in `src/Init/Tactics.lean` and from `src/Init/Core.lean`.

- `decide` evaluates the `Decidable` instance with the **elaborator's** reduction, which
  respects transparency, and then the kernel checks the result again.
- `decide +kernel` "uses kernel for reduction instead of the elaborator". As the docstring
  puts it, "(1) since it uses the kernel, it ignores transparency and can unfold everything,
  and (2) it reduces the `Decidable` instance only once instead of twice."
- `decide +native` (`native_decide` is a synonym) compiles the instance and evaluates it,
  "admitting the result via the `Lean.ofReduceBool` axiom". The trusted base then includes
  the compiler and every `@[implemented_by]`.
- Stated limitation: instances defined by well-founded recursion, or containing `Eq.rec`
  (for example, instances built with `rw` or `simp`), may get stuck. The docstring advises
  using `decidable_of_iff`.
- `bv_decide` bit-blasts the goal and runs CaDiCaL. It then checks the LRAT certificate by
  applying `Lean.ofReduceBool` to `verifyBVExpr` (`src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean`).
  That means native evaluation, not kernel reduction.

### Facts: `#print axioms`, measured in 4.28

| proof | axioms |
|---|---|
| `by decide`, `by decide +kernel` | none |
| `by native_decide` | `Lean.ofReduceBool`, `Lean.trustCompiler` |
| `by bv_decide` (bitboard lemma) | `propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Quot.sound` |

### Facts: how they scale

Benchmark: `(List.range n).foldl (· + ·) 0 = n*(n-1)/2`, wall time in seconds.

| n | `decide` | `rfl` / `by rfl` | `decide +kernel` | `native_decide` | `simp` / `grind` |
|---|---|---|---|---|---|
| 100 | 0.27 | 0.25 | 0.24 | 0.23 | fail (no progress) |
| 200 | **fails** (maxRecDepth) | **fails** (maxRecDepth) | — | — | — |
| 1 000 | fails; 0.42 with `maxRecDepth 100000` | fails | 0.30 | 0.24 | fail |
| 10 000 | fails | fails | 0.90 | 0.25 | fail |
| 30 000 | — | — | 3.16 (862 MB) | — | — |
| 100 000 | — | — | **fails** after 7.7 s (deep recursion, 1.9 GB) | — | — |

Finite quantifier benchmark: the 4096-instance statement
`∀ a b : Square, knightAdj a b = knightAdj b a`.

| `Square` | `decide` | `decide +kernel` | `native_decide` |
|---|---|---|---|
| `Fin 64` | 4.16 s | 2.28 s | 0.34 s |
| `structure {file rank : Fin 8}`, `∀` decided via `Fin` quantifiers | 4.95 s | 2.19 s | — |
| same structure, `∀` decided via an enumeration *list* | **fails** (maxRecDepth) | 1.98 s | 0.33 s |

### Judgment

- `decide +kernel` is the right default for closed computations. It is about 2× faster than
  `decide`, it avoids the elaborator's `maxRecDepth` limit of 512 (hit at n = 200), and it
  adds no axioms.
- Plain `decide` is fine for small facts such as 64-square lemmas. It breaks on anything
  list-recursive beyond a few hundred steps.
- `native_decide` and `bv_decide` both add `Lean.ofReduceBool` and `Lean.trustCompiler`. Keep
  them out of any theorem that claims to be kernel-checked (see Recommendations).

---

## 2. Kernel arithmetic: which `Nat` operations are accelerated

### Facts from the kernel source

Source: `src/kernel/type_checker.cpp` at tag `v4.28.0`, functions `reduce_nat`,
`reduce_bin_nat_op`, `reduce_bin_nat_pred` and `reduce_pow`.

- The kernel reduces these operations on literals natively, with arbitrary precision:
  - `Nat.succ`
  - `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.gcd`
  - `Nat.land`, `Nat.lor`, `Nat.xor`
  - `Nat.shiftLeft`, `Nat.shiftRight`
  - `Nat.beq`, `Nat.ble`
  - `Nat.pow`, only up to exponent `2^24`
- Arguments are reduced to whnf first.
- `Nat.log2` is not on the list.
- There is no built-in reduction for `String`, `BitVec`, `UInt64` or `Fin`. These reduce
  through their definitions down to the `Nat` primitives.
- The reference manual's `Nat` chapter says the kernel and compiled code both use "a fast
  arbitrary-precision arithmetic library (usually GMP)".

### Facts: measured

Operands are a = 3^300000 (about 475 000 bits) and b = 7^100000 + 12345. The test is
`Nat.ble 0 (op) = true` by `decide +kernel`.

- `+ - * / % gcd &&& ||| ^^^ <<< >>> == ≤ testBit` and `2^100000`: each took 0.26–0.32 s,
  the same as the baseline, so the cost is effectively nothing.
- A false variant (`Nat.ble (a*b) 0`) was correctly rejected in 0.27 s, so the value really is
  computed.
- `Nat.log2 a` **failed** after 4.7 s and 3.3 GB with a deep-recursion error. `Nat.log2 (2^2000)`
  is fine. `log2` uses structural recursion with fuel, so its cost grows with the bit length
  of the argument.
- The elaborator's `decide` refuses `3^300000`: "exponent 300000 exceeds the threshold 256"
  (`exponentiation.threshold`). The kernel does not have this limit.

### Judgment

- Packed-`Nat` encodings, such as the prototype's 64 nibbles or bitboards held as `Nat`,
  benefit fully from kernel acceleration.
- Any "find the lowest set bit" helper must avoid `Nat.log2` on large values. Iterating over
  64 squares is both clearer and safe.

---

## 3. `UInt64` and `BitVec 64` in the kernel

### Facts

- `#print` gives `structure UInt64 where toBitVec : BitVec 64` and
  `structure BitVec (w) where toFin : Fin (2^w)`. Kernel reduction therefore unwraps two
  structures and works on `Nat` modulo 2^64.
- Benchmark: xorshift64 (6 word operations per iteration) run N times by structural recursion
  on N, proved by `decide +kernel`. Times are wall seconds.

  | N | `Nat` with `&&& (2^64-1)` | `BitVec 64` | `UInt64` |
  |---|---|---|---|
  | 1 000 | 0.46 | 0.57 | 0.62 |
  | 3 000 | 0.67 | 1.09 | 1.54 |
  | 6 000 | 1.07 | 2.19 | 3.04 |
  | 10 000 | **stack overflow** (lazy accumulator, see §5) | 3.45 | 4.87 |

- Marginal cost per iteration, from the slope between 3k and 6k: `Nat` **0.13 ms**,
  `BitVec` **0.37 ms**, `UInt64` **0.50 ms**. Word types cost about 3–4× more than raw
  `Nat` in the kernel.
- `bv_decide` proved a universally quantified bitboard lemma, knight-attack symmetry
  `knight x &&& y = 0 ↔ knight y &&& x = 0` for all `x y : BitVec 64` (eight shift-and-mask
  terms), together with a shift lemma. Both took about 0.8 s of work in total.
- `bv_decide` pitfall (measured): with `abbrev BB := BitVec 64`, the same goals **failed**
  with "potentially spurious counterexample". The tactic abstracted `x <<< 8` as an opaque
  atom. Writing `BitVec 64` directly fixed it. The `Bool` form (`== 0`) also worked, but took
  3.3 s against 1.2 s for the `Prop` form.

### Judgment

- In the kernel, `UInt64` buys nothing over `Nat`; it only adds wrapper overhead.
- The real value of `BitVec 64` is reasoning: `bv_decide` and the `BitVec` lemma library
  (about 970 theorems in `Init/Data/BitVec/Lemmas.lean`).
- `UInt64` matters only for compiled speed (`#eval`, perft). If the library has a bitboard
  layer, that layer should be stated over `BitVec 64` or `Nat`, not `UInt64`.

---

## 4. Squares: `Fin 64`, `Nat`, or a structure

### Facts

- Core provides `Decidable (∀ i : Fin n, p i)`, `List.finRange`, `Array.finRange`,
  `Fin.foldl` and `Fin.cases`. There is no `Fin.all` and no `Fintype`.
- The `decide` cost of the 4096-instance quantifier is in §1. `Fin 64` and a
  `{file rank : Fin 8}` structure cost about the same under `decide +kernel` (2.0 s vs 1.9 s
  of work).
- With the structure, elaborator `decide` works only if `∀` is decided through the core `Fin`
  quantifiers:

  ```lean
  instance (p : Square → Prop) [DecidablePred p] : Decidable (∀ s, p s) :=
    decidable_of_iff (∀ f r : Fin 8, p ⟨f, r⟩) ⟨fun h s => h s.file s.rank, fun h f r => h ⟨f, r⟩⟩
  ```

  Going through a `List` enumeration hits `maxRecDepth` under plain `decide`.
- The round trip between `structure Square {file rank : Fin 8}` and `Fin 64`
  (`toFin s = rank*8 + file`) was proved in both directions:
  - by `grind [Square.ofFin, Square.toFin]`;
  - by `simp [.., Fin.ext_iff]; omega`.

  `simp …; omega` without `Fin.ext_iff` failed, because `omega` does not see through
  `Fin.mk` equalities.

### Judgment

- A raw `Nat` square needs a `< 64` side condition everywhere. Avoid it in the spec layer.
- A `structure Square where file : Fin 8; rank : Fin 8` reads like the English ("a square is
  a file and a rank"). It makes geometry (file and rank deltas) direct, and it costs nothing
  in decision procedures once the `Fin`-based `Decidable ∀` instance above is in place.
- Keep `Square.toFin : Square → Fin 64` (bit index a1 = 0 … h8 = 63) as the bridge to packed
  boards and bitboards, with the `grind`-proved bijection lemmas.

---

## 5. Boards: `List`, `Array`, `Vector`, functions, packed `Nat`

### Facts: literal-board benchmark

This is the workload of a certificate checker: each position is a closed literal. Cost is
per operation, `(t₄₀ − t₀) / 40`. "Scan" reads all 64 squares and counts the occupied ones.
"Update" plays one move (two writes), then checks equality against the literal result board.
"Eq" decides `B = B` for a literal `B`.

| representation | scan 64 squares | update + eq | eq |
|---|---|---|---|
| `List (Option Piece)` (`getD`, `set`) | 129 ms | 14 ms | 10 ms |
| `Array (Option Piece)` | 243 ms | **467 ms** | **481 ms** |
| `Array`, compared via `.toList` | — | 20 ms | 7.8 ms |
| `Vector (Option Piece) 64` | 220 ms | **485 ms** | **472 ms** |
| `Nat`, 64 nibbles (prototype style) | **10.5 ms** | **1.8 ms** | ≈ 0 |

### Facts: why `List` and `Array` reads are slow

- **Indexed access is O(index).** One scan of 64 squares costs:

  | access pattern | time |
  |---|---|
  | `List.finRange` + `getD` | 133 ms |
  | `List.finRange` + hand-written structural `nth` | 84 ms |
  | `List.range` + `nth` | 81 ms |
  | walking the list once (`countList`) | **4.8 ms** |
  | `finRange` iteration with no board reads | 11.5 ms |

  That is about 35–75 µs per recursive step in the kernel.
- **`Array` and `Vector` equality is about 40× slower than `List` equality.** The cause is
  `Array.instDecidableEq` → `instDecidableEqImpl`. That code is indexed and carries proofs, and
  in the kernel every `a[i]` is a walk along the list (`Array` is `structure { toList : List α }`).

### Facts: chained-move benchmark

This applies K moves without normalizing to a literal, counting occupied squares after each
move. Times are wall seconds.

| K | List | Array | Vector | function `Fin 64 → Option Piece` | Nat nibbles |
|---|---|---|---|---|---|
| 0 | 0.60 | 1.14 | 0.74 | 0.48 | 0.64 |
| 5 | 1.00 | 2.16 | 1.90 | 0.50 | 0.51 |
| 20 | 3.30 | 6.95 | 6.15 | 1.38 | 0.75 |
| 50 | 6.67 | 18.6 | — | — | — |
| 200 | > 60 s (5.3 GB) | > 60 s | — | — | — |

### Facts: kernel evaluation pitfalls

- **Lazy accumulators overflow the stack.** The kernel reduces lazily, so a tail-recursive
  accumulator builds a nested term that is forced only at the end. `Nat` xorshift with
  N = 10 000 hit "Stack overflow detected. Aborting".
  - Forcing the accumulator each step (`if x == 0 then 0 else iter n (step x)`) fixed it:
    6 000 iterations in 1.65 s, 20 000 in 5.6 s, 100 000 in 26.6 s.
  - Memory grows linearly, about 35 KB per iteration (3.6 GB at 100k), because of the kernel
    cache.
- **Memory grows within one declaration.** The prototype's kernel-only mate-in-11
  (`prototype/scratch/kernel.log`) needed 80 s and 5.75 GB for 320 generated theorems.
- **Per-theorem cost:**

  | proof style | List board (40 updates) | Nat board |
  |---|---|---|
  | `by rfl` | 0.62 s | ≈ 0.4 s |
  | `decide +kernel` | 1.00 s | ≈ 0.4 s |
  | `decide` | 1.08 s | ≈ 0.4 s |
  | `native_decide` | 0.49 s | ≈ 0.4 s |

  `rfl` is a reasonable alternative to `decide +kernel` for literal equalities.
- **Proof ergonomics of function boards:**
  - `update b s a := fun t => if t = s then a else b t` gives one-line `@[simp]` lemmas
    (`update_same`, `update_ne`).
  - `update_comm` is proved by `funext u; simp only [update]; grind`.
  - Core has **no** `Function.update`. Mathlib's lives in Mathlib, so the library must define
    its own.

### Judgment

- **Spec layer:** `Board := Square → Option Piece`, with a library-local `Board.set` and its
  simp lemmas. This is the most faithful ("each square holds at most one piece") and the
  easiest to prove things about. It has no canonical normal form, but `DecidableEq` follows
  from the `Square` quantifier, which costs 64 comparisons.
- **Executable layer:** packed `Nat`, either nibbles or one `Nat` bitboard per piece type,
  linked to the spec by `get (encode b) s = b s` refinement lemmas. It is 12× faster to scan
  and 8× faster to update than `List`, and about 250× faster than `Array` or `Vector` for
  update + eq.
- Never kernel-evaluate `Array` or `Vector` equality. Compare via `.toList`, or better, avoid
  them in kernel-checked code entirely.
- Certificates should state every intermediate position as a literal checkpoint, the way the
  prototype's `play p m = p'` does. Avoid long unnormalized chains, which are superlinear (see
  the chained-move table).

---

## 6. Deriving and enumeration without Mathlib

### Facts

- Core deriving handlers that compile here: `DecidableEq`, `Repr`, `BEq`, `Hashable`, `Ord`,
  `Inhabited`, plus `ReflBEq` and `LawfulBEq` on a type that derives `BEq`.
- Every enum inductive gets `T.ctorIdx : T → Nat` (`toCtorIdx` is deprecated) and
  `T.ofNat : Nat → T`.
- A derived enum `DecidableEq` is `if h : x.ctorIdx = y.ctorIdx then isTrue … else isFalse …`.
  It reduces cheaply in the kernel.
- **Pitfall (measured):** `deriving DecidableEq, BEq` produces a `BEq` instance that is *not*
  `LawfulBEq` (synthesis fails). Deriving only `DecidableEq` gives a lawful `BEq` through
  `instBEqOfDecidableEq`.
- There is no `Fintype`, `Finset` or `deriving Fintype`. The working pattern is:

  ```lean
  /-- All piece kinds, in a fixed order. -/
  def Kind.all : List Kind := [.pawn, .knight, .bishop, .rook, .queen, .king]
  theorem Kind.mem_all (k : Kind) : k ∈ Kind.all := by cases k <;> simp [Kind.all]
  theorem Kind.all_nodup : Kind.all.Nodup := by decide
  ```

  `Decidable (∀ k, p k)` then comes from `decidable_of_iff` over `Kind.all`. Both were tested.

### Judgment

- Derive `DecidableEq, Repr, Inhabited` everywhere, and `Hashable` and `Ord` only where a map
  or sort needs them.
- Do not derive `BEq` separately.
- Every finite type gets `all`, `mem_all`, `all_nodup`, and a `Decidable ∀` instance.
  Together these stand in for `Fintype`.

---

## 7. Recursion: structural, well-founded, fuel

### Facts

- Since Lean 4.9.0 (PR #4061), definitions by well-founded recursion are `@[irreducible]` by
  default. The `seal` and `unseal` commands also arrived in that release.
- Measured on `rayWF` (`termination_by 64 - s`):
  - `decide` and `rfl` **fail**. The `decide` error reads "reduction got stuck at … `(rayWF 3).beq 7`".
  - `decide +kernel` **succeeds**, because the kernel ignores transparency.
  - `simp [rayWF]` succeeds, through the equation lemmas.
  - `@[semireducible]` makes `decide` work again.
- Kernel cost of well-founded recursion (on a `Nat` measure) compared with structural fuel
  recursion, counting to N:

  | N | well-founded | structural fuel |
  |---|---|---|
  | 200 | 0.39 s | 0.33 s |
  | 1 000 | 0.43 s | 0.41 s |
  | 3 000 | 0.58 s | 0.60 s |

  They are indistinguishable here.
- Both styles produce functional induction principles (`rayWF.induct`, `rayFuel.induct`).
- Encoding cost for summing a 3000-element list, per theorem, including building the list:

  | encoding | time |
  |---|---|
  | `match` structural | 223 ms |
  | `foldl` | 237 ms |
  | `foldr` | 224 ms |
  | tail-accumulator | 234 ms |
  | `List.sum` | 213 ms |
  | raw `List.rec` | **134 ms** |

  The raw `List.rec` version must be `noncomputable`: "code generator does not support
  recursor `List.rec`".

### Judgment

- Prefer structural recursion: on the data, on `Fin`, or on explicit fuel with a stated bound,
  such as `rayFuel 7` for sliding pieces.
- Well-founded recursion is acceptable for spec-level functions that are only reasoned about.
  It adds friction in the elaborator, though: `decide` fails, and `rfl` needs `unseal`.
- Raw recursors save about 40% of kernel time but cost readability and executability. They
  are not worth it.

---

## 8. What core and Std provide (no Mathlib)

### Facts

- **Tactics in core:**
  - `omega`: linear arithmetic over `Nat` and `Int`.
  - `simp` and `simp +arith`.
  - `decide` with `+kernel` and `+native`.
  - `grind`, released in v4.22.0: SMT-style congruence closure, E-matching, and linear
    integer arithmetic.
  - `funext`, `rfl`, `exact?`, functional induction (`f.induct`).
- **In Std:**
  - `bv_decide` (`Std.Tactic.BVDecide`).
  - `Std.Sat`: CNF and LRAT.
  - `Std.Do`: Hoare-style reasoning about monadic code (`mvcgen`).
  - `HashMap`/`HashSet`, `TreeMap`/`TreeSet` and their `Ext*` variants with lemmas.
  - `Std.Time`, `Std.Net`, `Std.Sync`.
- **Lemma libraries in Init** (theorem counts in the main `Lemmas.lean` files alone):

  | file | theorems |
  |---|---|
  | `List/Lemmas.lean` | 682 |
  | `Array/Lemmas.lean` | 796 |
  | `Vector/Lemmas.lean` | 602 |
  | `BitVec/Lemmas.lean` | 973 |

  More lemmas sit in sibling files.
- `Vector α n` is in core (`#v[...]` literals, `Vector.ofFn`, `Vector.get`).
- **Missing from core:** `Function.update`, `Fintype`, `Finset`, `Set` lemmas, the `lemma`
  keyword (it is a parse error), and `Nat.sqrt`.
- **Measured automation:**
  - `grind` proved `Square.ofFin (toFin s) = s`, its converse, and `update_comm` with no hints
    beyond unfolding.
  - `simp` proved `List.getElem?_set`-style facts with a bounds hypothesis.

### Judgment

`grind` plus `omega` cover most of the square arithmetic and board-update reasoning in a
chess model. Use `grind [defs]` as the first tool for small lemmas, and keep `simp` lemma sets
small and explicit.

---

## 9. Naming and docstring conventions to follow

These are facts, summarized from the Lean core naming guide, the Mathlib naming guide, and
the Mathlib doc and style guides.

### Case

- Types, structures, inductives and `Prop`-valued predicates use `UpperCamelCase`:
  `Square`, `Board`, `Position`, `IsLegal`, `WinsIn`.
- Functions and data use `lowerCamelCase`: `legalMoves`, `Square.toFin`, `Board.set`.
- Theorems use `snake_case`: `set_same`, `toFin_ofFin`, `legalMoves_sound`.
- Upper-case pieces inside a theorem name become `lowerCamelCase`: `isLegal_iff`.

### Theorem names

- Read the conclusion; hypotheses go after `_of_`: `C_of_A_of_B`.
- Use `_iff` for biconditionals (the core guide insists on it), plus `ne`, `not`, `le`/`lt`,
  `left`/`right`, `inj`/`injective`, `comm`, `ext`, `induct`, `def`.
- Avoid primed names; prefer descriptive pairs.
- Put the main hypothesis's namespace on the name so dot notation works:
  `WinsIn.mono` lets you write `h.mono`.

### Suffixes and predicates

- `?` marks a function returning `Option`; `!` marks a function that may panic.
- In Std style a predicate takes `Is…`, unless that is ungrammatical, as with `Pairwise`.

### Variable names

- `h` for hypotheses, `w` for witnesses.
- `l` for lists; `xs` and `ys` for arrays and vectors.
- `i`, `j`, `k` for indices; `n`, `m` for sizes.
- Locally: `s`, `t` for squares; `b` for boards; `p`, `q` for positions; `m` for moves.

### Docstrings

- Each file opens with a module docstring `/-! … -/`. It starts with a `# Title` and a
  summary, then the optional sections `## Main definitions`, `## Main statements`,
  `## Implementation notes` and `## References`.
- Every `def`, and every major theorem, gets a `/-- … -/` docstring:
  - in complete sentences ending in periods;
  - with Lean names in backticks;
  - saying the meaning, not the implementation.
- `/-! ### … -/` sectioning comments organize long files.

### Layout

- Lines are at most 100 characters.
- `:= by` ends the line.
- Proofs are indented 2 spaces; continuation lines of statements are indented 4.
- Write `fun x ↦` (or `=>`), never `λ`; use `<|`, never `$`.
- Use `where` for structure and instance values.
- One tactic per line, and `·` for subgoals.
- Arguments go left of the colon. Split conjunctions into separate lemmas.
- Give the return types of definitions explicitly.

---

## 10. Recommendations for this library

These are judgments, each tied to the measurements above.

1. **Two layers, one refinement seam.**
   - The **spec layer** has these types:
     - `Square` as `structure { file : Fin 8, rank : Fin 8 }`;
     - `Piece` as a structure of `Color` and `Kind` enums;
     - `Board := Square → Option Piece`, with a library-local `Board.set` and the `@[simp]`
       lemmas `set_same`, `set_ne` and `set_comm`;
     - the rules as `Prop`-valued inductive or definitional predicates.
   - The **executable layer** packs positions into `Nat`: nibbles or `Nat` bitboards.
   - Link them with `decode (encode b) = b` and `get (encode b) s = b s` lemmas (§4, §5).
   - Do not use `Array` or `Vector` anywhere the kernel evaluates. Their equality is about 40×
     slower than `List` and about 250× slower than packed `Nat` (§5).
2. **Kernel-first checking.**
   - Certified results use `decide +kernel`, or `rfl` for literal equalities.
   - `native_decide` and `bv_decide` live only in modules named for that, for example
     `Chess/Native/…`, and every headline theorem's `#print axioms` gets recorded in the
     docs. Both tactics add `Lean.ofReduceBool` and `Lean.trustCompiler` (§1).
3. **Certificates are many small theorems over literal checkpoints.**
   - Each node states `play p m = p'` with `p'` a literal, as in the prototype.
   - Never chain moves without normalizing. That pattern is superlinear: 20 chained `List`
     moves took 3.3 s against 14 ms for each literal step.
   - Keep each declaration small so the per-declaration kernel cache stays bounded (§5).
4. **Recursion discipline.**
   - Use structural recursion on data or on explicit, documented fuel, such as the 7-step
     sliding ray.
   - Write accumulators so each step forces the value (§5 stack overflow).
   - Avoid well-founded recursion in anything plain `decide` or `rfl` must evaluate (§7).
   - Avoid `Nat.log2` on large values (§2).
5. **Finite types.** Each enum or finite structure gets:
   - `deriving DecidableEq, Repr, Inhabited`, and not `BEq`;
   - `all`, `mem_all` and `all_nodup`;
   - a `Decidable ∀` instance built from core's `Fin` quantifiers via `decidable_of_iff`, so
     that both `decide` and `decide +kernel` work (§4, §6).
6. **Bitboards as an optional third layer.**
   - State them over `BitVec 64` or `Nat`, not `UInt64`. `UInt64` is about 3.8× slower than
     `Nat` in the kernel and has no reasoning advantage (§3).
   - Prove per-square refinement lemmas by `decide +kernel` over the 64 squares. That costs
     about 2 s for 4096 cases (§1) and keeps them kernel-only.
   - Use `bv_decide` only as an exploratory oracle or in `Native` modules. Never put an
     `abbrev` around `BitVec 64` in goals meant for `bv_decide` (§3).
7. **Automation budget.** For square and board lemmas, try `grind [defs]` first, then
   `simp [defs, Fin.ext_iff]; omega`. Use `decide` only for closed finite statements under
   about 10⁴ instances (§1, §4).
8. **Style.**
   - Follow §9.
   - Every `def` gets a one-sentence English docstring that matches `docs/spec/<Module>.md`,
     so the English and the Lean can be diffed by eye.
   - Use `theorem` throughout, since `lemma` does not exist without Mathlib.
   - Keep `autoImplicit = false`; `lakefile.toml` already sets it.

---

## Sources

- Lean 4 kernel type checker, v4.28.0 (`reduce_nat`, `reduce_bin_nat_op`, `reduce_pow`, `ReducePowMaxExp = 1<<24`):
  <https://github.com/leanprover/lean4/blob/v4.28.0/src/kernel/type_checker.cpp>
- `decide` / `native_decide` docstrings, v4.28.0: <https://github.com/leanprover/lean4/blob/v4.28.0/src/Init/Tactics.lean>
- `Lean.ofReduceBool`, `Lean.trustCompiler` axioms: <https://github.com/leanprover/lean4/blob/v4.28.0/src/Init/Core.lean>
- `bv_decide` proof construction via `ofReduceBool`:
  <https://github.com/leanprover/lean4/blob/v4.28.0/src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean>
- Lean reference manual, Natural Numbers (GMP-backed kernel and runtime support):
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/>
- Lean reference manual, tactic reference (`rfl`, `grind`, `bv_decide`):
  <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- Lean 4.9.0 release (well-founded definitions irreducible, PR #4061; `seal` and `unseal`):
  <https://lean-lang.org/blog/2024-7-1-lean-490>, <https://lean-lang.org/doc/reference/latest/releases/v4.9.0/>
- Lean 4.22.0 release (`grind` released): <https://lean-lang.org/doc/reference/latest/releases/v4.22.0/>
- Lean core / Std naming conventions: <https://github.com/leanprover/lean4/blob/master/doc/std/naming.md>
- Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>
- Mathlib documentation requirements: <https://leanprover-community.github.io/contribute/doc.html>
- Mathlib style guide: <https://leanprover-community.github.io/contribute/style.html>
- Prior prototype (local): `prototype/`,
  in particular `ChessProof/Basic.lean`, `ChessProof/GothamKernel.lean` and `scratch/kernel.log`.
- All measurements were taken by me in this session on Lean 4.28.0 (§0).
