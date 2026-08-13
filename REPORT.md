# Final report: Martin's conjecture in Lean 4 / Mathlib

**Date:** 2026-08-13 (four work sessions).
**Toolchain:** Lean 4 `v4.34.0-rc1`, Mathlib master (pinned in `lakefile.toml` /
`lake-manifest.json`). Full `lake build`: green, ~1045 jobs, 29 files, ~5.9k lines.
**Sorry count: 0. Custom axioms: 0** (89 headline theorems audited; every one uses only
`propext`, `Classical.choice`, `Quot.sound`).

## Headline results (all sorry-free, standard axioms; believed new to Lean)

Recursion-theory foundation (`OracleCode.*`, `Cantor.*`):
- **Enumeration theorem** for oracle computability (`exists_code`); **jump strictness**
  `X <ᵀ X′` (`jumpFn_gt`, `Cantor.lt_jump`, `TuringDegree.lt_jump`); jump is
  degree-invariant and order-preserving (`jumpFn_congr`), descends to `TuringDegree`.
- **Kleene–Post**: incomparable Turing degrees exist (`kleene_post`,
  `TuringDegree.not_isTotal_le`).
- **The universal machine**: step-indexed `evaln` with soundness/completeness, and
  **`evaln_prim`** (it is primitive recursive).
- **Relativized recursion theorem** (`exists_fixedPoint`), **s-m-n** (`smn`), **padding
  lemma** (`infinite_indices`), quine (`exists_quine`).
- **Σ₁-completeness of the jump** (`dom_iff_jumpP`); **the full Shoenfield limit lemma**
  `f ≤ᵀ X′ ↔ f is X-limit-computable` (`limit_lemma`, `Cantor.le_jump_iff_limitApprox`);
  the jump is Δ⁰₂-in-X (`jump_limitApprox`).
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
