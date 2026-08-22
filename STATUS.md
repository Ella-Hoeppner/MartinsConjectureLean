# Status — Martin's conjecture in Lean 4 / Mathlib

Machine-checked formal progress on **Martin's conjecture** on degree-invariant functions.
Full `lake build` green; **0 sorries, 0 custom axioms** (every headline theorem audited via
`#print axioms` — only `propext, Classical.choice, Quot.sound`). Determinacy is **never**
axiomatized: it is threaded as an explicit hypothesis `TuringDeterminacy Γ` (with
`Γ := fun _ => True` the ZF+AD form; open/closed instances are ZFC theorems).

This file is the current-state map. `ATTACK.md` is the living log of the open-problem attack
(constraints + counterexample attempts). Everything below is in namespace `Martin`.

---

## The conjecture, and exactly what is open

**Part 1** (`ConstantOnCone F ∨ AboveIdOnCone F` for Turing-invariant `F`) reduces, provably
and losslessly, to two open cores (`CoreAnalysis.partI_iff_cores`):
- `RegressiveImpliesConstant` — `F X <ᵀ X` on a cone ⟹ constant on a cone;
- `IncomparableImpliesConstant` — `F X ⊥ᵀ X` on a cone ⟹ constant on a cone.

Both cores hold for **uniformly**-invariant `F` (Slaman–Steel, `partI_uniform`) and for
**degree-bounded** `F` (`bounded_implies_constant`). The general (non-uniform) case on the
**Turing** degrees is the 50-year-open content (Lutz proved it on the *hyperarithmetic*
degrees via ordinal machinery unavailable here).

**The two orthogonal inputs Part 1 rests on** (both determinacy theorems; the class-specific
one is the open one):

1. **Determinacy input** — `MartinDichotomy` (≡ `MartinPPT`, `martinPPT_iff_dichotomy`): every
   set contains a pointed perfect tree or its complement contains a cone. Its **invariant case
   is proved** (`perfectDichotomy_invariant`); a cone is *unconditionally* a full pointed
   perfect tree with the effective `recover` field (`cone_contains_PPT`). Only the
   **non-invariant** case is unformalized (Martin's fusion). **This half is mathematically
   known** — formalizing it is optional cleanup, not on the critical path; `MartinPPT` can
   always be taken as a hypothesis (same trust level as `TuringDeterminacy`).

2. **Class-specific input** — `escaping ⟹ MP` (`escapingMP_iff_no_fixedIncomparable`,
   `EscapingDichotomy.lean`): equivalent to "no escaping invariant `F` is Turing-incomparable
   to a fixed degree on a cone." **This is the actual open problem.** See `ATTACK.md`.

`partI_of_dichotomy_noFixedIncomparable` (`PartIRecast.lean`) is the sharpest packaging:
Part 1 ⟸ (1) + (2).

**Cleanest single-hypothesis form** (`partI_general_of_uniformity`, `MartinResults.lean`): full
Part 1 ⟸ the *one* implication "`TuringInvariant F ⟹ UniformlyTuringInvariant F` (on a cone)" —
a **sufficient** condition (the route by which the Borel case is proven; not necessary, since Part 1
doesn't imply uniformity). Everything downstream is machine-checked; `ATTACK.md` analyses exactly why
determinacy does not deliver this bridge for non-definable `F` (cone dichotomy vs cone uniformization).

---

## What is machine-checked (headline map)

**Recursion-theory foundation** (`OracleCode.*`, `Cantor.*`, `Universal.lean`, `Jump.lean`):
oracle enumeration theorem, the step-indexed universal machine `evaln` + `evaln_prim`, the
relativized Kleene recursion theorem (`exists_fixedPoint`), s-m-n/padding, Σ₁-completeness of
the jump, Shoenfield limit lemma, jump strictness `X <ᵀ X′` and its degree-invariance.

**Kleene–Post** (`KleenePost.lean`, `EffectiveKP.lean`): incomparable degrees exist, and the
effective version `∅ <ᵀ A <ᵀ 0′`.

**Cone theorem / Martin measure** (`ConeTheorem.lean`, `MartinMeasure.lean`, `ConeFilter.lean`):
`cone_theorem` (dichotomy from `GameDetermined`), the σ-pigeonhole `exists_onCone_of_cover`,
and the measure packaged as a first-class Mathlib `Filter` — `coneFilter`, proper + countably
complete (`CountableInterFilter`), ultrafilter on invariant sets (`coneFilter_dichotomy`),
and `pushCone_dichotomy`/`pushCone_comp`/`pushCone_id`/`pushCone_const` (the invariant
pushforward `F ↦ F_*U` is a monoid action; carries `id ↦ U`, `const ↦ principal`).

**Lachlan's theorem, globalized** (`LachlanTheorem.lean`): for a computably-uniformly-invariant
r.e. operator above id on a cone, `Wˣ ≡ᵀ X` or `Wˣ ≡ᵀ X′` on a cone (both cases built:
`ContinuousCase.lean`, `DiscontinuousCase.lean`, `CodingFamily*.lean`).

**Bard's Lemma 3.4** (`BardUniformity.lean`, `MartinResults.lean`): `uti_computable`
(uniform ⟹ computably-uniform), unlocking `partI_uniform` and both cores for the uniform class.
`partI_uniform_general` (the `Measurable`-free uniform Part I) and the capstones
`partI_Borel_of_uniformity_bridge` / `partI_general_of_uniformity`: the bridge
"Turing-invariant ⟹ uniformly Turing-invariant" is a **sufficient condition** for Part I
(everything downstream is machine-checked) — the route by which the Borel case is proven. It is
sufficient, *not* necessary (constant/above-id functions needn't be uniform), and its truth for
non-definable `F` is itself open. `escapingMP_of_uniformity_bridge`: the bridge subsumes the
`escaping ⟹ MP` route. (Why determinacy doesn't deliver the bridge: `ATTACK.md`.)

**Measure-preserving reduction** (`MeasurePreserving.lean`, `PointedTree.lean`, `MartinTree.lean`,
`RawPPT.lean`, `PerfectEmbedding.lean`): Theorem 3.4 ⟸ `GroszekSlaman` ⟸ `MartinPPT`, with
`recover` (Lutz–Siskind Lemma 2.1 = `lemma21`) and `realizes` (Prop 1.10 =
`realizes_of_perfectEmbedding`) both **proved as theorems**, not assumed.

**Pointed perfect trees, invariant case fully built** (`ConeTree.lean`, `ConeRawPPT.lean`):
`invariant_cofinal_contains_PPT` — a Turing-invariant cofinal determined set contains a full
`PPT`, via `codeReal_equiv` (`codeReal Y ≡ᵀ Y`, a two-direction `RecursiveIn` reduction).

**Regressive-core decomposition** (`RegressiveJumpDecomp.lean`): `regressive_jump_dichotomy` — a
new jump-distance σ-pigeonhole (each degree has countably many predecessors) splits the open
regressive core into **Case B** (`X ≤ᵀ (F X)^(k)`: `F` preserves the arithmetic degree, finitary)
or **Case A** (`X ≰ᵀ (F X)^(n)` ∀n: Lutz's `ω₁^x` hyperarithmetic regime). Packaged as a core-reduction
`regressiveCore_of_cases`. Pinpoints the obstruction as the lack of a well-founded rank on the Turing
degrees; see `ATTACK.md`.

**The Fodor engine** (`OrdinalUltrapower.lean`): `no_descending_ordinal_cone` — the cone measure's
ordinal ultrapower is well-founded (countable completeness ⟹ no infinite `≺`-descending sequence of
ordinal-valued functions on cones). `no_regressive_of_ordinal_rank`: the regressive core follows from
a degree-invariant ordinal rank a regressive `F` strictly decreases. This isolates the *sole* missing
ingredient — the rank `ω₁^x`.

**The Church–Kleene ordinal `ω₁^x`** (`ChurchKleene.lean`): `churchKleene` (relativized `ω₁^X` = sup of
order types of `X`-computable well-orders, correctly guarded `≤ᵀ X`), with `churchKleene_mono` +
`churchKleene_invariant` proven. Instantiating the engine: `no_omega1_decreasing_conePreserving` (no
cone-preserving regressive `F` strictly decreases `ω₁^x`) and `regressive_omega1_dichotomy` (a regressive
`F` preserves or strictly decreases `ω₁^x` on a cone). So a cone-preserving counterexample is
**`ω₁`-preserving** — the genuinely open case (Lutz's hyperarithmetic method handles the `ω₁`-decreasing
case on `D_h`; the `ω₁`-preserving Turing case needs `Σ¹₁`-bounding that fails on cones).

New constraints (`CounterexampleConstraints.lean`): `arithmetically_bounded_implies_constant`
(counterexample is *arithmetically* escaping), `nonconstant_above_or_incomparable_fixed` (per-degree
trap). Both open cores are reduced to jump-distance sub-cores (`regressiveCore_of_cases`,
`incomparableCore_of_cases`).

**Counterexample constraints** (`EscapingDichotomy.lean`, `PartIRecast.lean`,
`CounterexampleConstraints.lean`): machine-checked profile of any Part-1 counterexample —
`nonMP_incomparable_cone`/`_interval` (incomparable to a whole cone of fixed degrees, uniform
over each countable interval), `nonMP_kernel_avoids_cone` (kernel ideal is proper),
`nonconstant_values_uncountable`, `counterexample_full_profile`,
`incomparable_case_doubly_incomparable`, and `regressive_conePreserving_descending_chain`.
The precise barrier (no Turing-code extraction from a non-definable invariant `F`) and all
construction probes are logged in `ATTACK.md`.

---

## Reusable engineering notes (Lean/Mathlib gotchas)

- **`PFun` is not reducible.** `simp`/`rw` refuse to act on `Part.some x >>= f` for variable
  `f : ℕ →. ℕ`. Workarounds: state things with `f : ℕ → Part ℕ`; use the `mem_eval_*`
  characterizations in `OracleCode.lean`; `show _ = _ from Part.bind_some _ _` casts.
- **`Nat.rec_add_one` won't fire** on `Nat.rec` with `Part ℕ` motive via `rw`/`simp`; use
  `show (Nat.rec (motive := fun _ => Part ℕ) _ _ m).bind _ = _` to expose iota reduction.
- **`rw` under `have`-binders fails** when the target is in the binder's proof term; `simp only`
  often succeeds where `rw` fails.
- **`Primrec.list_rec` step arg needs `.to₂`.** Deep/nested `list_foldr_prim` blows up `whnf`:
  pass all implicits explicitly `(f := ..)(base := ..)(op := ..)` and
  `set_option maxHeartbeats 8000000 in`. Use `cond b 1 0` (not `if b then`) to match `list_rec`.
- **Search-over-`allBoolLists` + oracle-prefix pattern** (`existsOK_prim`/`consb_prim` in
  `EffectiveTreeReduction.lean`): `list_foldr_prim` + `foldr_or_mem`/`foldr_and_mem`; read the
  oracle via `graphEnc`/`graphEnc_recursiveIn`; bridge `==` to `Primrec.eq.decide` with
  `beq_eq_decide` (`primrec_beq`). This is the template for any effective-reduction build.
- **`Cantor.le_iff_bitg`** turns `X ≤ᵀ Y` into a `RecursiveIn {toPFun Y}` goal about `bitg X`.
- `if_pos`/`if_neg` are deprecated in current Mathlib (warnings only).
