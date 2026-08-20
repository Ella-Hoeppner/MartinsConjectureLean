# Final report: Martin's conjecture in Lean 4 / Mathlib

**Date:** 2026-08-14, extended through 2026-08-20 (multiple work sessions).
**Toolchain:** Lean 4 `v4.34.0-rc1`, Mathlib master (pinned in `lakefile.toml` /
`lake-manifest.json`). Full `lake build`: green, 56 files, ~13.8k lines.
**Sorry count: 0. Custom axioms: 0** (every headline theorem audited via `#print axioms`;
each uses only `propext`, `Classical.choice`, `Quot.sound`).

**Research into the OPEN cores (2026-08-19).**  After a literature review of the frontier
(Lutz–Siskind's measure-preserving approach; Lutz's regressive result on the *hyperarithmetic*
degrees — the regressive case on the Turing degrees is *explicitly open*, blocked by an ordinal
jump-hierarchy barrier), the modern **measure-preserving** framework was formalized
(`MeasurePreserving.lean`, building on the existing order-preserving skeleton): the general-function
theory (Prop 1.8, increasing modulus via choice, the two-ended dichotomy, structural theory —
upward-closed in the Martin order, closed under composition, `measurePreserving_escapes`), the exact
equivalence `partI_iff_measurePreserving` (Part 1 ⟺ Thm 3.4 ∧ (non-constant⟹measure-preserving),
pinning its two halves), the tree-free fragment `aboveId_of_bounded_modulus`, and — connecting my
Slaman–Steel formalization to the frontier — `measurePreservingAboveId_uniform`: **Lutz–Siskind's
central Theorem 3.4 (measure-preserving ⟹ above the identity), proved for the uniform class without any
pointed perfect tree**, via the encoding technique.  The remaining general theorem needs the
Groszek–Slaman pointed-perfect-tree coding (a genuine multi-session build).

The two open cores (regressive / incomparable, on the Turing degrees) were then **reduced to a single
clean hypothesis** (`RegressiveReduction.lean`, following Lutz's strategy).  The class properties
"constant / regressive / incomparable on a cone" are shown to be Martin-equivalence invariants, so if a
regressive (resp. incomparable) invariant function is Martin-equivalent to *any* uniformly-invariant
one, that core follows from the formalized uniform theorems.  Capstone
**`partI_of_uniformization`: Part 1 of Martin's conjecture holds provided every Turing-invariant function
is, on a cone, Martin-equivalent to a uniformly-invariant one** — pinning the entire remaining content
into "uniformization on a cone" (exactly Lutz's hyperarithmetic step, open on the Turing degrees).  A
companion sharpening (`escaping_iff_not_constant`, `nonconstant_mp_iff_escaping_mp`) shows escaping ⟺
non-constant, so the class-specific half of the measure-preserving decomposition reads simply
"escaping ⟹ measure-preserving".

Finally, the **general Theorem 3.4** was attacked directly (`PointedTree.lean`).  The recursion-theoretic
output of the Groszek–Slaman pointed-perfect-tree construction is bundled into an interface
`InvertingTree` (per increasing `F`): pointedness, realizing-a-cone, right-inversion of `F` on the
branches (Cor 2.6), and branch-recovery (Lemma 2.1 — **now a proved theorem, see below**).  From the single existence hypothesis
`GroszekSlaman` (one such tree for every increasing function) the **entire Lutz–Siskind §3 argument is
machine-checked**: `measurePreservingAboveId_of_groszekSlaman` proves Theorem 3.4 (Turing-invariant
measure-preserving ⟹ above the identity on a cone) for *arbitrary* invariant functions, and
`partI_of_groszekSlaman` derives Part 1 from `GroszekSlaman` + the class half.  The interface is checked
non-vacuous (`inverting_tree_id`), and a **concrete proper pointed perfect tree** (the even-bits tree) is
built with its `pointed`/`realizes` fields proved (`evenTree_pointed`, `evenTree_realizes`).

`GroszekSlaman` was then **reduced further, and the reduction proved in full** (`MartinTree.lean`,
following Lutz–Siskind §2).  `groszekSlaman_of_martinPPT : MartinPPT → GroszekSlaman` derives it from
`MartinPPT` — **Martin's cited determinacy theorem** (their Lemma 2.3: every set cofinal in the Turing
degrees contains a pointed perfect tree).  Machine-checked along the way: the σ-pigeonhole
`exists_cofinal_of_iUnion` (Cor 2.4, via `bigJoin`); the code-extraction machinery
(`outReal`/`outReal_eq`/`exists_code`); and the Lemma 2.5 / Cor 2.6 assembly — for increasing `F` the
sets `A n = {x : Φₙ computes y with F y = x}` have cofinal union (because `F z ≥ᵀ z`), so Cor 2.4 yields a
pointed perfect tree inside one `A n` and `Φₙ = outReal n` is the inverting functional (injective on
branches for free, since `F ∘ (outReal n) = id` there).  Net: **`measurePreservingAboveId_of_martinPPT`
and `partI_of_martinPPT` derive Theorem 3.4 and Part 1 from `MartinPPT` alone** — the general
measure-preserving direction of Part 1 now rests on one named, standard determinacy theorem, everything
else verified.

**Lutz–Siskind's Lemma 2.1 was then proved in full** (`Konig.lean`, `EffectiveTree.lean`,
`EffectiveTreeReduction.lean`).  `Martin.lemma21` states: for a downward-closed tree `Tr` and a
*computable* (code `e`) functional `g` that is *injective on the branches*, every branch `x` satisfies
`x ≤ᵀ g x ⊕ Tr`.  The proof is the genuine effective-injectivity argument — König's lemma
(`Konig.exists_branch`), the use principle, a compactness *separation* lemma (wrong nodes stop being
consistent with `g x`), and a `Nat.rfind` over levels of an oracle-computable "good level" predicate,
reading `x↾(n+1)` off the first good node — carried all the way down to a `RecursiveIn` reduction (node
enumeration, tree-membership and consistency checks all shown primitive recursive).

Because Lemma 2.1 needs *nothing* but tree-closure, the `recover` field of a pointed perfect tree is
**not an assumption but a theorem** (`RawPPT.lean`).  A `RawPPT` bundles only a genuine downward-closed
tree that is `pointed` and `realizes` a cone — Martin's Lemma 2.3 with no recursion-theoretic content
smuggled in — and `RawPPT.toPPT` supplies `recover` for free via `lemma21`.  Hence
**`martinPPT_of_martinPPT' : MartinPPT' → MartinPPT`** and `partI_of_martinPPT'_escaping`: Part 1 now
rests on the *recover-free* `MartinPPT'`, exactly Martin's cited Lemma 2.3 in a concrete tree
representation.  Prop 1.10 (`realizes`) was then *also* discharged (`PerfectEmbedding.lean`): from a
degree-preserving perfect embedding `emb : 2^ω → [T]` (`emb z ≤ᵀ z ⊕ code`, invertible), `realizes` is a
three-line `≤ᵀ` calculation.  A `PerfectTree` (`RawPPT.lean`) therefore carries **only structural tree
data** — closure, pointedness, embedding — and derives both `realizes` and `recover`; so
`partI_of_perfect_escaping` rests Part 1 on the promise-free `MartinPPT_perfect`.

**The determinacy game builds these trees (invariant case)** (`ConeTree.lean`).  Martin's Lemma 2.3 is
proved here for the **Turing-invariant** case, straight from the game machinery: `cone_theorem` +
cofinality give a cone `cone Y ⊆ A` (`cone_of_invariant_cofinal`), and a cone *is* a pointed perfect
tree — the reals whose even bits spell `Y` (`{join Y Z}`) are pointed, realize every degree above `Y`
(Prop 1.10, via `coneEmbedding` + `realizes_of_perfectEmbedding`), perfect (the embedding
`z ↦ join Y z` is injective — continuum-many branches), and lie in `cone Y ⊆ A`.  Headline
`invariant_cofinal_contains_pointedPerfect` (and its `TuringDeterminacy`-threaded form).  What remains is
only the **non-invariant** cofinal case of `MartinPPT'` — the sets `A n` in Groszek–Slaman are not
Turing-invariant, so the cone theorem does not apply and Martin's genuine fusion/uniformization argument
is needed — a well-scoped separate project needing AD, threaded as a hypothesis, never axiomatized.

**Headline (latest session, 2026-08-20):**
1. **Lutz–Siskind's Lemma 2.1 proved in full** (`Martin.lemma21`): a computable functional injective on
   the branches of a downward-closed tree lets each branch be recovered — `x ≤ᵀ g x ⊕ Tr` — via König's
   lemma, a compactness separation lemma, and an oracle `rfind`, carried down to a `RecursiveIn`
   reduction. `[propext, Classical.choice, Quot.sound]`.
2. **`recover` and `realizes` are theorems, not axioms** (`RawPPT.lean`, `PerfectEmbedding.lean`): the
   promise-free `MartinPPT_perfect` (a purely structural perfect pointed tree) implies `MartinPPT` —
   `recover` via `lemma21`, `realizes` (Prop 1.10) via `realizes_of_perfectEmbedding`. So
   `partI_of_perfect_escaping` rests Part 1 on the minimal, faithful form of Martin's theorem.
3. **The determinacy game builds pointed perfect trees (invariant case)** (`ConeTree.lean`): Martin's
   Lemma 2.3 proved for Turing-invariant cofinal sets straight from `cone_theorem` — a cone is the
   `Y`-coding tree `{join Y Z}`, pointed + realizing + (injective embedding ⟹) perfect, inside the set.
   Only the non-invariant case of `MartinPPT'` now remains.

**Headline (prior session):**
1. **Lachlan's theorem for r.e. operators, globalized to a cone** — for *bare* uniform invariance
   (`Martin.lachlan_dichotomy_cone_uniform`, `Martin.lachlan_no_post_solution_cone_uniform`).
2. **Part I of Martin's conjecture for uniformly-invariant functions** (`Martin.partI_uniform`
   = `PartI_Uniform_Borel`, Slaman–Steel 1988) — **both Part I open cores proved for the uniform
   class** (`Martin.regressive_uniform`, `Martin.incomparable_uniform`).
3. **Bard's Lemma 3.4** (`Martin.uti_computable`): `UniformlyTuringInvariant F →
   ComputablyUniformlyTuringInvariant F` — the linchpin that discharges computable uniformity for
   both results above.  Built from the symmetric universal `d`-machine (`eval_dCode`: read the unary
   index via `rfind`, run the tail via `univCode ∘ shiftIdx`, region-select) and the composition
   monoid (`iterTrE`, `trE₂`), assembled into `v(i,j)` with `forward_correct`/`backward_correct`.

## Headline results (all sorry-free, standard axioms; believed new to Lean)

Recursion-theory foundation (`OracleCode.*`, `Cantor.*`):
- **Enumeration theorem** for oracle computability (`exists_code`); **jump strictness**
  `X <ᵀ X′` (`jumpFn_gt`, `Cantor.lt_jump`, `TuringDegree.lt_jump`); jump is
  degree-invariant and order-preserving (`jumpFn_congr`), descends to `TuringDegree`.
- **Kleene–Post**: incomparable Turing degrees exist (`kleene_post`,
  `TuringDegree.not_isTotal_le`); and the **effective** version
  (`KleenePostJump.effective_kleene_post`): two reals `A, B` with
  `A ≤ᵀ 0′ ∧ B ≤ᵀ 0′ ∧ ¬(A ≤ᵀ B) ∧ ¬(B ≤ᵀ A)` — the finite-extension
  construction made fully `0′`-computable by encoding the whole stage recursion
  (`condN`) and running each stage's Σ₁ decision through the jump.
- **The universal machine**: step-indexed `evaln` with soundness/completeness, and
  **`evaln_prim`** (it is primitive recursive).
- **Relativized recursion theorem** (`exists_fixedPoint`), **s-m-n** (`smn`), **padding
  lemma** (`infinite_indices`), quine (`exists_quine`).
- **Σ₁-completeness of the jump** (`dom_iff_jumpP`); **the full Shoenfield limit lemma**
  `f ≤ᵀ X′ ↔ f is X-limit-computable` (`limit_lemma`, `Cantor.le_jump_iff_limitApprox`);
  the jump is Δ⁰₂-in-X (`jump_limitApprox`).
- **Lachlan's theorem for r.e. operators, GLOBALIZED to a cone** (`Martin.lachlan_dichotomy_cone`,
  `Martin.lachlan_no_post_solution_cone`; Lachlan 1975 / Lutz Cor. 3.11).  For a
  *computably-uniformly-invariant* r.e. operator `W` (index `e`) that is above the identity on a
  cone, with Turing determinacy: **on a cone `Wˣ ≡ᵀ X` or `Wˣ ≡ᵀ X′`**, and `W` is never strictly
  between `X` and `X′`.  Both branches are fully proved and assembled (`local_dichotomy_complete`):
  * **continuous case** (`continuous_case`, determinacy-free): `Wˣ ≤ᵀ X ⊕ 0′`, via the `0′`-decidable
    `0/1`-extension-halting test and the decisive-prefix reduction;
  * **discontinuous case** (`discontinuous_case_complete`): `Wˣ ≡ᵀ X′`, via the **coding-real family**
    — `Y_c ≡ᵀ X` splicing `Φ_c^X(c)↓` at the marker (`yc_equiv`), fully built including the explicit
    uniform backward-recovery `OracleCode` that discharges `HasCodingFamily` (`hasCodingFamily`,
    `CodingFamilyCode.lean`);
  * **globalization**: `Martin.cone_theorem_onCone` on the invariant pivot `{X | Wˣ ≤ᵀ X}` — cone ⟹
    `Wˣ ≡ᵀ X` (with above-id), complementary cone ⟹ `W` discontinuous ⟹ `Wˣ ≡ᵀ X′`.

  Determinacy is threaded explicitly (`TuringDeterminacy`); nothing is axiomatized.  The **single
  external classical input** is Bard's Lemma 3.8 (bare uniform invariance ⟹ *computable* uniformity),
  which is why the hypothesis is `ComputablyUniformlyTuringInvariant` — the standard *effective* form
  of Lachlan's theorem.  Supporting infrastructure: operator use principle, computable composition of
  functionals (`eval_trE_comp`, Bard's `∗`), Bard's Fact 3.1 (`joinFam_le`), `Wˣ ≤ᵀ X′`
  (`reReal_le_jump`), the explicit universal machine (`eval_univCode`).
- **The Friedberg Jump Inversion Theorem** (`jump_inversion`): *every Turing degree above the
  halting problem is a jump* — for every `C ≥ᵀ 0′` there is an `A ≤ᵀ C` with `A′ ≡ᵀ C`.  The
  full finite-extension construction relative to `C`: each stage consults the extension-halting
  oracle (`0′`-decidable, hence `C`-decidable) and appends the least forcing extension then a
  bit of `C`.  `A ≤ᵀ C` (the construction is `C`-computable), `A′ ≤ᵀ C` (the jump is read off
  the `C`-computable stage decisions via the use principle), and `C ≤ᵀ A′` (decode by
  reconstructing the coding positions from `A′` through an `A′`-computable length recursion,
  using `A ≤ᵀ A′`).  ~830 lines, all standard axioms — believed the first Lean proof.
- Upper-semilattice join on Cantor points; infinitely many degrees; no maximal degree.

Martin's-conjecture layer (`Martin.*`):
- **Formal statements** of Part I and Part II (Borel version), the uniform and
  order-preserving variants, and Lachlan's statement — with sanity lemmas.
- **Martin's cone theorem** (`cone_theorem`), determinacy as an explicit hypothesis;
  proved unconditionally for open/closed sets (`cone_dichotomy_of_isOpen/isClosed`).
- **Martin measure** as a countably complete ultrafilter (`exists_onCone_of_cover`);
  comparability trichotomy; the jump is a `Regular` function (`regular_jump`).
- **Reduction of the whole conjecture to five isolated open cores**, proved to be an
  *exact equivalence* under Turing determinacy (`martinConjectureAD_iff_cores`,
  `partI_iff_cores`, `partII_iff_cores`); boundedness lemma and counterexample profile.
- **The canonical Steel chain** (`uniform_jump_chain`): the iterates `X ↦ X^(n)` are
  simultaneously uniformly invariant (via the universal machine), `Regular`, and strictly
  Martin-increasing-and-comparable — a machine-checked witness that the conjecture's
  predicted `id <ₘ (·′) <ₘ (·″) <ₘ ⋯` is realized as far as provable without full Part II.

**Bottom line:** Martin's conjecture itself remains open (no honest run settles a
50-year-open problem). What this project delivers is (a) a substantial, first-of-its-kind
Lean formalization of the recursion-theory and Martin-measure machinery the subject rests
on, several pieces genuinely new to Lean, and (b) the conjecture's open content *formally
isolated* to five precisely stated cores, with everything around them machine-checked.

## TL;DR (session 1)

Tiers T0–T3 are complete, sorry-free, and pass the anti-fooling checklist. The headline
results, believed to be **new to Lean** (based on the prior-art search below):

1. **Jump strictness** `O <ᵀ O′` for Mathlib's oracle-computability framework
   (`jumpFn_gt : O ≤ᵀ jumpFn O ∧ ¬ jumpFn O ≤ᵀ O`), including a Gödel numbering and
   enumeration theorem for `Nat.RecursiveIn`.
2. **Martin's cone theorem** (`Martin.cone_theorem`): every Turing-invariant determined
   subset of Cantor space contains a cone or is disjoint from a cone — with determinacy of
   the game as an explicit hypothesis (nothing else was mathematically possible: no
   determinacy exists in Mathlib, and axiomatizing AD would be inconsistent).
3. **The jump is degree invariant and descends to `TuringDegree`**
   (`JumpInvariance.lean`): `jumpFn_mono`/`jumpFn_congr` (order preservation / invariance,
   via a primitively-recursive code translation proved by course-of-values recursion), the
   jump is an `OrderPreserving`/`TuringInvariant` function in the Martin framework, and
   `TuringDegree.jump` with **`TuringDegree.lt_jump : d < d.jump`** on Mathlib's own degree
   structure. This completes every T1 item in the brief.

Plus formal statements (T2) of Martin's conjecture Parts I and II (Borel version), the
uniformly-invariant and order-preserving variants, and Lachlan's theorem — with sanity
lemmas exercising every definition.

## What compiles, file by file

All `#print axioms` outputs show only `[propext, Classical.choice, Quot.sound]`
(the enumeration theorem needs only `[propext]`); transcript in `axiom_audit.lean`.

### `MartinsConjecture/OracleCode.lean` — Gödel numbering for `Nat.RecursiveIn`
- `OracleCode`: codes for oracle machines = `Nat.Partrec.Code` + an `oracle` constructor,
  with plain `rfind` instead of `rfind'` (design decision, below).
- `eval O c : ℕ →. ℕ`, clause-for-clause aligned with the constructors of `Nat.RecursiveIn`.
- **`exists_code : Nat.RecursiveIn {O} f ↔ ∃ c, eval O c = f`** — the enumeration theorem
  for oracle computability. Structural induction in both directions (this is what the
  `rfind`-not-`rfind'` choice buys).
- Numbering `encodeCode`/`ofNatCode`, round-trip lemmas both ways, `Denumerable OracleCode`.
- Primitive recursiveness of the numbering arithmetic (`constEnc`, `pairEnc`, `compEnc`) —
  the ingredients for *primitive recursive families of codes*.
- Membership characterizations `mem_eval_comp`, `mem_eval_pair`, `mem_eval_rfind`,
  `dom_eval_rfind` (engineering layer that tames `PFun` irreducibility; see LEDGER).

### `MartinsConjecture/Jump.lean` — the Turing jump, T1 keystone
- `jumpP O e`: the diagonal halting problem relative to `O`; `jumpFn O`: its characteristic
  function (total, 0/1-valued — a point of Cantor space, as it should be).
- **`jumpFn_not_turingReducible : ¬ jumpFn O ≤ᵀ O`** — diagonalization. Notable: the proof
  needs *only* `exists_code` plus the `RecursiveIn` constructors (the diagonal function is
  `μ n [jumpFn O a = 0]`, built from `comp`/`left`/`rfind` — no universal machine, no code
  arithmetic).
- **`turingReducible_jumpFn : O ≤ᵀ jumpFn O`** — unbounded search: `O(a)` is the unique `n`
  such that the jump answers "halts" at the code "compute `O(a)`, halt iff it equals `n`";
  the code family `k a n` is a primitive recursive function of `(a, n)` built from the
  numbering arithmetic, and the equality-test code is obtained *for free* from `exists_code`
  applied to a `Partrec` function (a noncomputable choice of a fixed code is harmless since
  `Primrec.const` does not care).
- `jumpFn_gt` (strictness), `jumpFn_not_partrec` (no jump is computable),
  `halting_problem_not_partrec` (sanity anchor: `∅′ ≰ᵀ ∅`).
- `trOracle`/`eval_trOracle`/`jumpP_trOracle`: code translation splicing an oracle
  implementation into codes — everything for jump order-preservation *except* one
  primrec-ness fact (LEDGER gap 1).

### `MartinsConjecture/CantorPoints.lean` — degree theory on `2^ω`
- Points `X : ℕ → Bool`, embedding `toPFun`, reducibility `≤ₜ` / equivalence `≡ₜ` /
  strict `<ₜ` (scoped notation), pre-order lemmas.
- Jump on points; **`lt_jump : X <ₜ Cantor.jump X`**.
- **Join / upper semilattice**: `join X Y` by bit-interleaving, with `left_le_join`,
  `right_le_join`, and the least-upper-bound property `join_le`.
- Bottom degree sanity anchors: `le_bot_iff` (bottom degree = the partial recursive
  characteristic functions), `le_of_computable`, `not_computable_jump`.

### `MartinsConjecture/Martin.lean` — T2: the conjecture, formally stated
Definitions follow Lutz's thesis (*Results on Martin's Conjecture*, Berkeley 2021)
definition-for-definition: `TuringInvariant` (Def 1.11), `OrderPreserving` (Def 1.34),
`cone`/`OnCone`, Martin order `MartinLE`/`MartinEquiv`/`MartinLT` (Defs 1.14–1.15),
`EquivVia`/`UniformlyTuringInvariant` (Defs 1.27–1.28, including the exact index-pair
convention `Φ_i(x) = y ∧ Φ_j(y) = x`).

Stated `Prop`s (none asserted): **`PartI_Borel`**, **`PartII_Borel`**
(= totality ∧ well-foundedness ∧ jump-is-successor), `MartinConjecture_Borel`,
`PartI_Uniform_Borel` (Slaman–Steel), `PartI_OrderPreserving_Borel` (Lutz–Siskind),
`LachlanStatement`. "Borel" = `Measurable` for the product σ-algebra on `ℕ → Bool`.

Proved sanity lemmas exercising the definitions (anti-fooling checklist item 2):
- `EquivVia.equiv` and `equiv_iff_exists_equivVia` — index witnesses exist iff genuinely
  Turing equivalent (this is exactly the enumeration theorem at work);
- `OrderPreserving.turingInvariant`, `UniformlyTuringInvariant.turingInvariant`;
- `partI_Borel_implies_orderPreserving`, `partI_Borel_implies_uniform`;
- **`martinLT_jump : MartinLT F (jump ∘ F)`** — the provable-outright half of the Part II
  successor claim, from pointwise jump strictness.

### `MartinsConjecture/ConeTheorem.lean` — T3: Martin's cone theorem
- Games on `2^ω` with histories encoded as `Nat.pair`-chains; strategies are `ℕ → Bool`
  (Cantor points — so *the winning strategy is literally a cone base*, no coding detour);
  `WinsI`/`WinsII`/`GameDetermined`.
- **`gamePlay_le`** — the computational heart: if one player's moves are the bits of `Y` and
  the other's come from a strategy recursive in `Y`, the whole play is recursive in `Y`.
  Proved by primitive recursion on histories via the `prec` constructor, with a
  parity-mixing arithmetic trick to avoid case-split (cond) closure lemmas that Mathlib's
  `RecursiveIn` API lacks.
- **`cone_theorem`**: Turing-invariant + determined ⟹ contains a cone or misses a cone;
  `cone_theorem_onCone` in "on a cone" form. Determinacy is an explicit hypothesis
  (`GameDetermined A`), never an axiom.

### `MartinsConjecture/JumpInvariance.lean` — T1 completed: the jump is invariant
- `trE_primrec`: the `trOracle` translation is primitive recursive on encodings, by
  course-of-values recursion (`Primrec.nat_strong_rec`) with a total step function reading
  the history list (`trStep`, `trStep_spec`).
- `jumpFn_mono` (order preservation), `jumpFn_congr` (degree invariance);
  `Cantor.jump_mono`/`jump_congr`; `Martin.orderPreserving_jump` /
  `Martin.turingInvariant_jump` — the jump belongs to the function class Martin's
  conjecture quantifies over.
- `TuringDegree.jump : TuringDegree → TuringDegree` (well-defined via `Quot.map`) and
  **`TuringDegree.lt_jump : ∀ d, d < TuringDegree.jump d`** — jump strictness stated on
  Mathlib's own `TuringDegree` partial order.

## The oracle-computation design decision (and why)

Adopted **Mathlib's `Nat.RecursiveIn {g}` as the definition of `≤ᵀ`** (rather than forking a
new machine model) and added the missing Gödel numbering on top. Rationale: theorems land in
Mathlib's own language (upstreamable; `TuringDegree` etc. come for free), and the inductive
characterization makes both directions of `exists_code` structural.

Two deliberate deviations from `Nat.Partrec.Code`, both documented in `blueprint.md`:
`oracle` constructor (the point), and plain `rfind` in place of `rfind'` — the eval clause
then matches `Nat.RecursiveIn.rfind` *syntactically*, making `exists_code` cheap; `rfind'`
is only needed for a step-indexed universal machine (`evaln`), which jump strictness does
not need. That observation — diagonalization needs only `exists_code`; the search direction
needs only primrec *code families* — is what made T1 fit in this budget (the port of the
full `evaln` development, ~1000 lines, was avoided entirely).

Judgment call to flag: skipping `evaln` is a *debt*, not a free lunch — Lachlan/T4 and
anything about c.e. sets will need it (LEDGER, scope cuts).

## Prior art (searched 2026-08-13: Mathlib, Zulip, GitHub, arXiv)

- Mathlib has `Nat.RecursiveIn`/`TuringDegree` (Duve–Roth 2025) but **no jump, no oracle
  codes, no cones, no determinacy**. Open PRs #37062 (join on `ℕ →. ℕ`), #37111
  (`PrimrecIn`) — no overlap with the jump work; our Cantor-point join is complementary.
- Tanner Duve's personal repo (github.com/tannerduve/computability, Lean v4.24) defines a
  jump and oracle codes but its enumeration lemmas and **jump strictness are `sorry`ed**.
  To our knowledge the strictness proof here is the first in Lean.
- Sven Manthe's Borel determinacy formalization exists externally (arXiv:2502.03432,
  Lean v4.28); only its tree layer is in Mathlib. Our cone theorem is designed to consume a
  determinacy instance later (LEDGER gap 2).
- No prior formal statement of Martin's conjecture was found in any proof assistant.

## Anti-fooling checklist status

1. `#print axioms` on every headline theorem: standard axioms only (see `axiom_audit.lean`).
2. Vacuity anchors, all proved: `∅′` not partial recursive; `X ≤ᵀ X′` via a genuine
   unbounded search (not vacuous — its proof constructs a real reduction); bottom degree =
   computable points; `equiv_iff_exists_equivVia` shows the index-witness machinery is
   non-degenerate; `martinLT_jump` shows the Martin order machinery is non-degenerate.
3. No claim of proving or refuting the conjecture is made. The conjecture appears only as
   *stated* `Prop`s; the proved theorems (strictness, cone theorem, `martinLT_jump`) are
   known results, correctly attributed.
4. Nothing contains `sorry`.

## Honest assessment of novelty

- **Novel (to Lean, per the search above):** enumeration theorem for `Nat.RecursiveIn`;
  jump strictness; the formal statements of Martin's conjecture and its variants; the cone
  theorem modulo an explicit determinacy hypothesis.
- **Not novel mathematically:** everything proved is classical (Post/Kleene-era or Martin
  1968); the contribution is formalization only.
- **Caveats:** the T2 statements should be refereed against the literature by an expert
  (LEDGER gaps 3–5 list the specific conventions at risk: prewellordering phrasing,
  Lachlan's uniformity convention, Borel = product-measurable identification).

## Session 2 (2026-08-13 afternoon, ~45m): five further results

All sorry-free, standard axioms only (`axiom_audit.lean` extended):

### `Hierarchy.lean` — the jump hierarchy
`0 <ᵀ 0′ <ᵀ 0″ <ᵀ ⋯`: jump iterates are strictly increasing
(`TuringDegree.strictMono_jump_iterate`), giving typeclass instances
**`Infinite TuringDegree`** and **`NoMaxOrder TuringDegree`** on Mathlib's own
degree structure.

### `TopologicalTriviality.lean` — unconditional cone dichotomy at the bottom
`Cantor.patch_equiv`: finite prefixes are free for Turing degrees (the prefix
is hard-coded as a primrec lookup table).  Hence
**`Martin.eq_univ_of_isOpen_turingInvariant`**: every nonempty *open*
Turing-invariant set is all of Cantor space — so the conclusion of Martin's
cone theorem holds for open and closed Turing-invariant sets **with no
determinacy hypothesis** (`cone_dichotomy_of_isOpen` / `_isClosed`).  This
also explains *why* the cone theorem only becomes substantive higher in the
Borel hierarchy.

### `UniformJump.lean` — the jump is computably uniformly invariant
**`Martin.computablyUniformlyTuringInvariant_jump`**: a computable function
transforms index witnesses for `X ≡ₜ Y` into index witnesses for
`X′ ≡ₜ Y′` — the strong (Steel/Slaman–Steel-style) uniformity notion, and
the model example for the hypothesis of Lachlan's theorem.  New
infrastructure built for it: `exists_code_of_partrec` (one code valid for
*every* oracle), an s-m-n layer (`idCode`, `curry`, primrec `curryEnc`), and
`trE₂` (the splicing translation, jointly primrec in the spliced index — the
`n = 4` case of the course-of-values recursion is absorbed by
`encode_ofNatCode`).

### `MeasurableJump.lean` — the jump is Borel
**`Martin.measurableSet_mem_eval`**: for every code, the set of oracles on
which a computation converges to a given value is Borel (induction on codes;
convergence decomposes into countable unions/intersections; the `oracle`
case depends on one coordinate).  Hence **`Martin.measurable_jump`** and
**`Martin.regular_jump`**: the jump is a `Regular` function — Borel, Turing
invariant, Martin above the identity — i.e. a certified member of the class
Part II of the conjecture quantifies over.

### `RegularChain.lean` — the provable part of the Part II picture
* **`Martin.measurableSet_cone`**: cones are Borel sets.
* `Cantor.bigJoin` + `Martin.onCone_and` / **`Martin.onCone_forall`**: the
  cone filter is closed under countable conjunction (countable completeness —
  the combinatorial basis of Martin measure).
* **The ω-chain `const <ₘ id <ₘ (·′) <ₘ (·″) <ₘ ⋯` inside `Regular`**:
  `martinLT_const_id`, `regular_jumpIter`, `martinLT_jumpIter`, and
  `partII_succ_provable_half` (`Regular` is jump-closed and `F <ₘ jump ∘ F`).
  Part II asserts this chain is *cofinal-and-complete* (nothing regular fits
  strictly between successive entries, and above `id` everything regular
  appears); the chain's existence and strictness — the provable half — is
  now formal.

### `Locality.lean` — the use principle (session 2, addendum)
**`OracleCode.eval_locality`**: a converging oracle computation consults only
finitely many bits of its oracle — proved by induction on codes, extracting
the finite "use" directly from the convergence derivation (no step-indexed
universal machine needed).  Corollaries: convergence is an *open* condition
on the oracle (`Martin.isOpen_mem_eval`) and **the jump predicate is Σ⁰₁-open
in the oracle** (`Martin.isOpen_jumpP`), sharpening measurability.  This is
the foundation for any future finite-extension/forcing argument
(Kleene–Post, Sacks-style constructions).  Also added: `MartinLE.trans` and
`martinLE_jumpIter_of_le` (any two jump iterates are Martin comparable — the
totality half of Part II, verified on the chain).

**Session 2 totals: 6 new files, full build 1025 jobs, still 0 sorries and 0
custom axioms (37-line `axiom_audit.lean`, every line standard).**

### `KleenePost.lean` — the Kleene–Post theorem (session 2, finale)
**`KleenePost.kleene_post : ∃ A B, ¬ A ≤ₜ B ∧ ¬ B ≤ₜ A`** — incomparable
Turing degrees exist (Kleene–Post 1954), by the classical finite-extension
argument built directly on the use principle: `KleenePost.step` extends any
pair of finite strings to defeat one reduction requirement (forcing
convergence and flipping the diagonal bit, or exploiting unforceable
divergence); `stages` iterates the step by classical choice with even/odd
requirement scheduling; `A`/`B` are the limits.  Degree-level corollaries on
Mathlib's `TuringDegree`: **`TuringDegree.exists_incomparable`** and
**`TuringDegree.not_isTotal_le`** (the Turing degrees are not linearly
ordered).  Believed to be the first machine-checked Kleene–Post in Lean.
This was listed as out of reach in the session-1 ledger ("needs finite
approximation infrastructure that does not exist yet") — `eval_locality`
turned out to be exactly that infrastructure.

**Final session-2 totals: 8 new files, full build 1026 jobs, 0 sorries,
0 custom axioms (41-line `axiom_audit.lean`, every line standard).**

## Session 3 (2026-08-13, ~1h): the direct attack on the conjecture

Four new files (`MartinMeasure`, `Reduction`, `BoundedCase`,
`OrderPreservingCase`) plus `ATTACK.md`; all sorry-free, standard axioms
(audit now 55 lines, all clean); full build 1030 jobs.  All results take
`TuringDeterminacy` as an explicit hypothesis (AD-style for the class of all
sets; the Borel restriction is Martin's ZFC Borel-determinacy theorem, not
yet in Lean).

* **σ-pigeonhole** (`exists_onCone_of_cover`): Martin measure is formally a
  countably complete ultrafilter on invariant determined sets.
* **Comparability trichotomy** (`comparability_on_cone`) and **the
  reduction** (`partI_of_cores`): Part I of Martin's conjecture is formally
  reduced to two open cores — `RegressiveImpliesConstant` and
  `IncomparableImpliesConstant`; in the other two comparability regimes
  Part I is proved outright.
* **Index stabilization** (`exists_uniform_index_on_cone`): the classical
  first step of Lachlan/Steel/Slaman–Steel, formalized.
* **Boundedness lemma** (`bounded_implies_constant`): degree-bounded
  invariant functions are constant on a cone — Part I holds outright for
  them (`partI_of_bounded`).
* **Escape theorem** (`counterexample_escapes`) + sharpened cores: any
  counterexample must escape every fixed degree on a cone.
* **Order-preserving skeleton**: the determinacy-free dichotomy
  (`orderPreserving_measurePreserving_or_avoids`, with `MeasurePreserving` =
  Lutz Def 1.37) and the formal Lutz–Siskind proof skeleton
  (`partI_orderPreserving_of_lemmas`).
* **Counterexample profile** (`counterexample_profile`): the combined
  formal description of what any Part I counterexample must be.

**Honest outcome of the direct attempts on the open cores** (full log in
`ATTACK.md`): four genuine lines of attack (join-limit coding, Baire/density
arguments, Posner–Robinson leverage, post-stabilization comparison) each die
at one of three precisely identified missing pillars — pointed perfect
trees, Posner–Robinson/Kumabe–Slaman forcing, or Steel's comparison games.
These are the same pillars the human proofs of the known partial results
rest on.  The conjecture itself remains open; what changed is that its open
content is now *formally isolated* — the escaping cores — with everything
around them machine-checked.

### Session 3 addendum: first stone of pillar (i)

`UniformJoin.lean`: the **uniformly pointed join-cone** package —
`join_realizes`, `equivVia_join_uniform` (controlled congruence of canonical
representatives via a computable index transformation, built from explicit
mixer/projection codes and the `trOracle` splice), and
`uniformlyTuringInvariant_comp_join`.  Full build 1031 jobs, audit 58 lines
all standard, 0 sorries.

### Session 3 capstone: the full reduction (`FullReduction.lean`)

**`martinConjecture_of_cores`**: under Turing determinacy, the Borel Martin
conjecture — Part I *and* Part II — follows from **five precisely isolated
open cores**: (1) regressive ⟹ constant, (2) incomparable ⟹ constant,
(3) no pointwise-incomparable pairs of regular functions, (4) no strictly
descending ω-chains of regular functions, (5) jump minimality.  Supporting
new theorems: `comparison_on_cone` (pairwise trichotomy),
`partII_total_of_core`, `partII_WF_of_core` (via the descending-chain
characterization of well-foundedness, with `MartinLT` proved a strict
order), `partII_succ_of_core`.  Each core is a known theorem for uniformly
invariant (Steel; Slaman–Steel) and order-preserving (Lutz–Siskind)
functions and open in general.  Everything outside the cores is now
machine-checked: **the open content of Martin's conjecture is formally
isolated, with a single assembly theorem**.

Final session-3 totals: 7 new files (`MartinMeasure`, `Reduction`,
`BoundedCase`, `OrderPreservingCase`, `UniformJoin`, `FullReduction`, plus
`ATTACK.md`), full build 1034 jobs, **0 sorries, 0 custom axioms** (64-line
audit, every line standard).

### Session 3 coda: first discharged determinacy instances

`DeterminacyInstances.lean`: **`turingDeterminacy_isOpen`** and
**`turingDeterminacy_isClosed`** — the `TuringDeterminacy` hypothesis is
*proved* for open and for closed sets, via topological triviality (such
invariant sets are `∅` or everything).  Degenerate by nature, but they make
the conditional framework unconditional at the clopen level and are the
template for the real future target, `TuringDeterminacy MeasurableSet`
(= Martin's Borel determinacy).  Final build: 1035 jobs, 66-line audit, all
standard axioms, 0 sorries.

### Session 3 final result: the reduction is exact (`CoreAnalysis.lean`)

* **`incomparable_core_iff_never`**: the incomparable core is secretly an
  *impossibility statement* — its hypothesis and conclusion are jointly
  contradictory (`not_constant_and_incomparable`: a constant value lies
  below `join C B`, refuting incomparability there), so the core asserts
  exactly that the fourth comparability regime never occurs.
* **`partI_iff_cores`**: under Turing determinacy the reduction of Part I to
  the two cores is an **equivalence** — the isolated open content is exact,
  with no loss in either direction.

Also `partII_total_iff_core`, `partII_WF_iff_core`, `partII_succ_iff_core`,
and `partII_iff_cores`: the Part II reductions are likewise exact — the
five-core isolation of the whole conjecture is lossless in both directions.

Grand totals for session 3: 8 new theorem files + `ATTACK.md`; build 1036
jobs; 69-line axiom audit, every line standard; 0 sorries anywhere.

## Session 4 (2026-08-13, ~1h): the universal machine and its harvest

The single blocker identified in `ATTACK.md` — the step-indexed universal machine for
`OracleCode` — is now **built and fully proved**, unlocking the recursion theorem and the
limit lemma.  Seven new files, all sorry-free, standard axioms only.

* **`Evaln.lean`** — `evaln k L c n`: step-indexed evaluation of oracle code `c` on input
  `n` with fuel `k` and finite oracle table `L`.  Proved: `evaln_sound` (bounded answers
  are correct), `evaln_complete` (every converging computation is captured at some stage,
  via `graphOf`), `evaln_mono` (answers persist as fuel/table grow), and a bounded search
  `searchList` with exact spec for the `rfind` case.
* **`EvalnPrim.lean`** — **`evaln_prim`**: `evaln` is *primitive recursive* jointly in
  `(k, L, c, n)`.  The proof: the `n ≤ k` guard makes each stage a finite table
  (`stageTable`), which satisfies a course-of-values recursion over the packed index
  `pair k (encode c)` (`stageStep`, correctness `stageStep_spec` by the full code-number
  case analysis), discharged by `Primrec.nat_strong_rec`.
* **`Universal.lean`** — **`eval_universal`**: relative to any total 0/1 oracle, the
  two-argument evaluator `(e, n) ↦ eval O (ofNatCode e) n` is itself recursive in the
  oracle, by dovetailing `evaln` over stages using the oracle's own graph
  (`graphEnc_recursiveIn`).  Then **`exists_fixedPoint`**: Kleene's second recursion
  theorem, relativized — every computable code transformation has an oracle-relative fixed
  point (diagonal `curryEnc x x`).
* **`RecursionTheorem.lean`** — named corollaries: **`exists_quine`** (a self-outputting
  code), `no_fixedPointFree`, `exists_selfHalting_code`.
* **`LimitLemma.lean`** — **`dom_iff_jumpP`**: Σ₁-completeness of the jump (halting
  questions reduce primitively to diagonal jump questions).  **`recursiveIn_jump_of_limit`**:
  the substantive direction of the Shoenfield limit lemma (`X`-computable pointwise-convergent
  approximations have `X′`-computable limits).
* **`JumpApprox.lean`** — **`jump_limitApprox`**: the jump is Δ⁰₂-in-`X` — it has an
  `X`-computable, monotone, pointwise-convergent stage approximation (`jumpApproxN`).
* **`LimitLemmaFull.lean`** — **`limit_lemma`**: the **full Shoenfield Limit Lemma**,
  relativized — `f ≤ᵀ X′ ↔ f has an X-computable stage approximation converging pointwise`.
  The `→` direction runs the reduction under the jump's stage approximation via the reusable
  table-builder `exists_tableEnc`, closed by `evaln_mono`.

* **`SmnPadding.lean`** — the **s-m-n / parametrization theorem** (`smn`, with `curryEnc`
  the primrec index transform) and the **Padding Lemma** (`infinite_indices`: every
  function recursive in `O` has infinitely many indices), plus `exists_fixedPoint_code`.
* **`CantorLimit.lean`** — the limit lemma repackaged for Cantor points and degrees
  (`le_jump_iff_limitApprox`), with the capstone `jump_jump_not_limitApprox`: the double
  jump has no `X`-limit-computable approximation (so the jump hierarchy is genuinely
  proper).  `Martin.EquivVia` gains `refl`/`symm`; jump-join degree relations.
* **`PostDomain.lean`** — **Post's theorem, Σ₁ direction**: the domain of any partial
  `O`-recursive function is `≤ₘ O′` (`domain_manyOne_jump`) and decidable in `O′`
  (`domain_recursiveIn_jump`).
* **`ExtHalting.lean`** — **the extension-halting problem is `0′`-decidable**
  (`extHalting_recursiveIn_jump`) — the recursion-theoretic crux of the finite-extension
  (Kleene–Post-below-`0′`) method.  The remaining `0′`-recursive construction is scoped in
  `ATTACK.md`.

These are, to our knowledge, the first machine-checked Lean proofs of the universal oracle
machine, the relativized recursion theorem, and the (relativized) Shoenfield limit lemma.
The recursion theorem was the exact artifact all four attack lines in `ATTACK.md` funneled
through; with it, Lachlan's theorem and Steel's uniform case become concrete formalization
plans rather than research (see `ATTACK.md`, "next milestones").

## Session 5 (2026-08-13, continuing): the effective Kleene–Post theorem

The `ATTACK.md`-scoped `0′`-recursive construction is now **built and fully proved**,
completing the finite-extension-below-`0′` method end to end.  One new file,
`EffectiveKP.lean` (~990 lines, sorry-free, standard axioms only).

* **`effective_kleene_post`** — the headline:
  `∃ A B : ℕ → Bool, A ≤ᵀ 0′ ∧ B ≤ᵀ 0′ ∧ ¬(A ≤ᵀ B) ∧ ¬(B ≤ᵀ A)`.  Two reals, each
  Turing-below the halting problem, that are Turing-incomparable — the effective refinement
  of Kleene–Post (the plain version only bounds the pair below `0″`).
* **The construction (`cond`)** — a finite-extension priority-free construction on
  `List ℕ` strings of 0/1 bits: at even stage `2e` diagonalize against `Φₑᴮ = A`; at odd
  `2e+1` against `Φₑᴬ = B`.  Each `reqStep` consults the extension-halting oracle
  (`ExtHalting`, Σ₁, hence `0′`-decidable) and appends a diagonalizing bit or a default `0`.
* **Incomparability (`not_A_le_B`, `not_B_le_A`)** — via the `evaln`
  soundness/completeness/monotonicity bridge: `defeat_even`/`defeat_odd` show the stage-`e`
  requirement makes `Φₑ` differ from the target at the diagonalized position.
* **The `0′`-bound — the session's technical core.**  The entire stage recursion is
  *encoded* as a single `ℕ →. ℕ` function `condN` (each pair `(σ,τ)` packed as
  `encPair σ τ`), and shown recursive in `jump ∅` by running the encoded stage step
  `reqStepEnc` — itself recursive in `0′` — inside a `Nat.RecursiveIn.prec` fold.
  `condN_spec` proves the encoding faithful (`condN r = encPair (cond r).1 (cond r).2`);
  `bitgA/bitgB_recursiveIn` extract the reals' bits; `A_le_jump`/`B_le_jump` bridge to the
  Cantor-point/jump representation (`toPFun (jump ∅) = jumpFn ∅`).

* **`exists_intermediate_degree`** — an immediate corollary: since `A, B ≤ᵀ 0′` are
  incomparable, `A` is a **non-computable intermediate degree** `∅ <ᵀ A <ᵀ 0′` — Post's
  problem solved (non-uniformly, via Kleene–Post; the r.e. version is Friedberg–Muchnik).

This is, to our knowledge, the first machine-checked Lean proof that incomparable degrees
exist *below the halting problem* (a strictly stronger statement than plain Kleene–Post),
and the first fully `0′`-computable finite-extension construction in Lean.  It closes the
last item scoped in `ATTACK.md` and completes T1's optional Kleene–Post target at full
strength, and yields an intermediate degree as a one-line corollary.

**Groundwork toward Lachlan's theorem (T4).**  After literature research (Bard 2019 /
Lutz thesis Ch. 3), the modern proof of Lachlan's theorem was scoped and its reusable
foundations built and proved (`UniformFunctionals.lean`, `ReOperator.lean`):

* **`OracleCode.eval_trE_comp`** — **computable composition of Turing functionals**:
  `Φ_i^A = Φ_{trE j·i}^X` whenever `Φ_j^X = A`, with the index map primitive recursive
  (`trE_primrec`).  This packages the existing `trOracle`/`eval_trOracle` oracle-substitution
  operator as Bard's `∗` — the linchpin of his computable-uniformity lemma, and the reason
  Turing functionals form a computable monoid under composition.
* **`Cantor.joinFam_le`** — **Bard's Fact 3.1**: a family of reals uniformly computable
  from `A` (via a primrec index function) has join `≤ᵀ A`.  With `Cantor.le_iff_bitg`, the
  general `X ≤ᵀ Y ↔ bit-graph of X recursive in Y` bridge.
* **`OracleCode.reReal_le_jump`** — **`Wˣ ≤ᵀ X′` for every r.e. operator** (Post's `Σ₁`
  theorem for operators): the determinacy-free easy half of Lachlan's local dichotomy
  (Lutz Cor. 3.11).  Plus `reReal_eq_of_reduces` (operator-level composition transport).
* **`OracleCode.mem_reReal_iff_haltsOn_prefix`** — **the use principle for r.e. operators**:
  `n ∈ Wˣ ⟺ machine e halts on n under some finite prefix of X`'s bit-graph; with
  `haltsOn_mono` (monotone in the prefix) and **`isOpen_reReal`** (r.e. operators are open
  /continuous in the oracle).  This is the continuity-in-the-oracle cornerstone of Lachlan's
  *continuous* case, from `evaln` soundness/completeness against the prefix table
  `graphOf (bitg X)`.

* **`OracleCode.continuous_case`** — **the continuous case of Lachlan's local dichotomy is
  now COMPLETE** (Lutz Cor. 3.11, the determinacy-free half): *if the r.e. operator `W`
  (index `e`) is continuous at `X`* — every `n`'s membership `n ∈ Wˣ` is settled by a finite
  prefix of `X` (`haltsOn (X↾ℓ) ∨ ¬ extHaltsFrom (X↾ℓ)`) — *then `Wˣ ≤ᵀ X ⊕ 0′`*.  On input
  `n` the reduction μ-searches for the least *decisive* prefix length `ℓ` (both tests
  `0′`-decidable: `haltsOn_recursiveIn_jump`, `extHaltsFrom_recursiveIn_jump`; the prefix is
  `X`-computable via `graphEnc`), then reads off the answer.  Built over the two-oracle set
  `{toPFun X, jumpFn ∅}` and cut down to `join X 0′` via `Nat.RecursiveIn.subst`; the
  correctness kernel `decisive_answer` shows the positive test reads the true bit at any
  decisive stage (monotonicity + `graphOf` prefixing).  This is a genuine half of Lachlan's
  theorem for r.e. operators.

A key finding: the modern proof needs **no recursion theorem** (contrary to the folklore
framing), and its heaviest ingredient (computable composition) was already in the codebase.
The **continuous half of Lachlan's local dichotomy is now fully proved**; what remains for
the full theorem is the `y_e` diagonalization (Lutz Thm 3.10, the discontinuous case —
an oracle-machine construction on the scale of the effective-KP build) and the fixed-word
part of computable uniformity (Bard Lemma 3.4); see `ATTACK.md` "Next formal milestones".

## Session 6 (2026-08-13/14, the marathon): Lachlan's local dichotomy + jump inversion

An extended autonomous run.  Complete, sorry-free, standard-axiom additions, all
believed new to Lean, plus a capstone and the discontinuous-case reduction:

* **Lachlan's theorem, continuous case** (`ContinuousCase.lean`, `continuous_case`):
  literature research (Bard 2019 / Lutz thesis Ch. 3) established that the modern proof needs
  *no recursion theorem* and that its heaviest ingredient — computable composition of
  functionals — was already in the codebase (`trOracle`, packaged as `eval_trE_comp`).  The
  determinacy-free continuous half is fully proved: a continuous r.e. operator has
  `Wˣ ≤ᵀ X ⊕ 0′`, by a `μ`-search over prefix lengths with both tests `0′`-decidable and the
  prefix `X`-computable, assembled over `{toPFun X, jumpFn ∅}` and cut to `join X 0′` via
  `Nat.RecursiveIn.subst`.  Groundwork: `UniformFunctionals`, `ReOperator`, `OperatorLocal`.
* **The Friedberg Jump Inversion Theorem** (`JumpInversion.lean`, ~830 lines, `jump_inversion`):
  `∀ C ≥ᵀ 0′, ∃ A ≤ᵀ C, A′ ≡ᵀ C` — the marathon's centerpiece.  The full finite-extension
  construction relative to `C`, with all three reductions proved: `A ≤ᵀ C` (the encoded
  construction `jstrEnc` is recursive in `C` via `prec`), `A′ ≤ᵀ C` (the jump is read off the
  `C`-computable stage decisions through the operator use principle `dom_iff_jExists`), and
  `C ≤ᵀ A′` — the decode — by reconstructing the coding positions from `A′` through an
  `A′`-computable length recursion (`jLenEnc`), using `jReal C ≤ᵀ A′`.  Packaged as
  `jump_range_iff`: the jump's range is *exactly* the cone above `0′`.
* **Capstone** (`DegreeCapstone.lean`, `exists_intermediate_non_jump`): combining the effective
  Kleene–Post intermediate degree with the jump-range characterization, there is a degree
  `∅ <ᵀ A <ᵀ 0′` that is *not a jump* — the jump misses the intermediate degrees.

The reusable technique across `condN`/`jstrEnc`/`jLenEnc`: encoded finite-extension
constructions made recursive in an oracle via `Nat.RecursiveIn.prec` over an encoded step, the
step's recursiveness mirroring `reqStepEnc_recursiveIn` (decision/oracle-bind `>>=` `Nat.rec`
over the decision bit) with "search = least witness" bridges.

* **Discontinuous case + the full local dichotomy** (`DiscontinuousCase.lean`): the partner of
  the continuous case, a complete arc.  `discontinuous_reduction`: if the operator `W` (index
  `e`) is *computably uniformly invariant* and admits a *coding-real family* at a discontinuity
  marker `n₀` (`HasCodingFamily` — the splicing + s-m-n witnesses, isolated as a named
  hypothesis in the codebase's reduce-to-lemmas style), then `X′ ≤ᵀ Wˣ`, by the recursion-
  theoretic assembly of s-m-n and the universal machine (`eval_universal`) at the fixed marker.
  With Post's theorem this sharpens to `discontinuous_equiv_jump` (`Wˣ ≡ᵀ X′`).  Assembled into
  `local_dichotomy_high` — Lutz Cor 3.11's clean form: for `X ≥ᵀ 0′`, `Wˣ ≤ᵀ X` (continuous) or
  `Wˣ ≡ᵀ X′` (discontinuous) — and the payoff `no_operator_post_solution`: such an operator is
  never strictly between `X` and `X′`, which is exactly why Lachlan's theorem rules out uniform
  solutions to Post's problem.

* **The explicit universal machine** (`UniversalCode.lean`, `eval_univCode`): `univCode :
  OracleCode` with `eval (toPFun X) univCode ⟨e,n⟩ = eval (toPFun X) (ofNatCode e) n` for every
  total `0/1` oracle `X` — a *single* code uniform across oracles, the "step-indexed universal
  machine" `OracleCode.lean`'s design note said was not built (`eval_universal` gives only the
  per-oracle `RecursiveIn` form).  Built from the explicit oracle graph-prefix encoder `cGraph`
  + oracle-free `evaln`/`ts`/`extv` codes (`exists_code_of_partrec`) + the `rfind` search, with
  correctness by `evaln` soundness/completeness.  This is what the discontinuous case's recovery
  machine needs (a code that runs uniformly with the varying oracle `Y_c`).

**Correction to an earlier boundary claim.**  Prior notes (including an earlier draft of this
section) said the discontinuous case is "blocked by the absence of a universal code."  That was
**wrong**: `Universal.lean` already had `eval_universal`/`exists_fixedPoint`, and the explicit
`univCode` is now built too.  The genuinely-remaining content for Lachlan's theorem is
(i) **discharging `HasCodingFamily`** — the `Y_c` splicing (recipe in `ATTACK.md`) + its `cY`/`cM`
codes (the latter now buildable from `univCode`) + s-m-n; and (ii) **Bard's Lemma 3.8** (turning
bare uniform invariance into computable uniformity).  Neither is the universal code.

## Concrete next steps for a future run

1. ~~Primrec-ness of `trOracle` on encodings~~ Done (`JumpInvariance.lean`). Remaining
   refinement: extract the *uniformity* content (the translation gives computable index
   transforms, so the jump should be provably `ComputablyUniformlyTuringInvariant`).
2. `curry`/`smn` + recursion theorem for `OracleCode` ⟹ **Lachlan's theorem** (T4, the
   recommended named target — pure recursion theory).
3. Open (Gale–Stewart) determinacy for the concrete game encoding ⟹ unconditional cone
   theorem for open Turing-invariant sets; or port/bridge Manthe's Borel determinacy for the
   full Borel cone theorem.
4. `evaln` universal machine for `OracleCode` (unlocks c.e.-relative-to-oracle, jump as
   Σ⁰₁-complete, Kleene–Post).
5. Upstream candidates for Mathlib: `OracleCode` + `exists_code` + jump strictness align
   with the Duve–Roth roadmap and fill their `sorry`s.
