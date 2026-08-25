# Status — Martin's conjecture in Lean 4 / Mathlib

Machine-checked formal progress on **Martin's conjecture** on degree-invariant functions.
Full `lake build` green; **0 sorries, 0 custom axioms** (every headline theorem audited via
`#print axioms` — only `propext, Classical.choice, Quot.sound`). Determinacy is **never**
axiomatized: it is threaded as an explicit hypothesis `TuringDeterminacy Γ` (with
`Γ := fun _ => True` the ZF+AD form; open/closed instances are ZFC theorems).

This file is the current-state map. `ATTACK.md` is the living log of the open-problem attack
(constraints + counterexample attempts). Everything below is in namespace `Martin`.

### Session 2026-08-25 — GENUINE ATTACK on the open core (not bookkeeping)
- **`MartinOmega1Approach.lean`**: reframe `IncomparableConstant ⟺ NoIncomparableSelfMap` (no invariant
  `F` has `F X ⊥ᵀ X` on a cone); the **graph-orbit device** `graphOrbit_strictMono` (iterate `X⊕F X`,
  choice-free strict increase on cone). The ω₁-chain approach it points to is a **provable no-go**
  (limit stages need `ω₁↪ℝ`, which AD forbids); Fodor-on-`ω₁ˣ` dies identically → unified obstruction:
  lifting per-degree info to ω₁-level needs a Turing code (Am region has none) or choice (AD-forbidden).
  Full writeup `MARTIN_PART1_APPROACH_OMEGA1.md`. Also `incomparable_jump_not_below` (`X≰ᵀF X ⟹ X'≰ᵀF X`).
- **`LevelCoordinatedTree.lean`** + `MARTIN_PART1_STRUCTURAL_AM.md`: the structural/∞-Borel route.
  **Theorem A** (math): Borel invariant `F` of Baire rank ρ has `F X ≤ᵀ X^(ρ)`, ρ **fixed** ⟹ Borel `Am`
  is a *transfinite `Bm`* at fixed level (Lutz's rank-unboundedness is **∞-Borel-specific**, not Borel).
  `level_of_cores` unifies finite `Bm` (`L=jump^[k]`) + Borel `Am` (`L=X^(ρ)`) at any invariant increasing
  level `L`. **Sharpened crux**: for Borel `F` the coordinated tree is dischargeable (Theorem A gives the
  code uniformly=NO good-rep barrier; Silver gives injectivity), so Borel `Am` collapses to the
  **domination step** — and the *uniform* half of domination is **provably impossible** for incomparable `F`
  (`incomparable_jump_not_below`); only *per-function* domination survives = the exact recursion-theoretic
  open crux. Caveat verified: Theorem A is type-A uniformity (`F X=Φ_e^{X^(ρ)}`) NOT type-B uniform
  invariance (`F X≤ᵀF Y` fails), so it does NOT solve Borel Part 1.

### Session 2026-08-25 additions (autonomous run — earlier structural bookkeeping)
- **`MartinGameCode.lean` + `GameCapstone.lean`** (prior session, verified): `GameCodeBelow`
  (`codeGame σ ≤ᵀ σ`) PROVED ⟹ **`MartinPPT` (Martin's Lemma 2.3) is a theorem modulo determinacy**
  (`martinPPT_of_gameDeterminacy`); hence Thm 3.4, Part 1 ⟺ escaping⟹MP, and order-preserving Part 1
  all rest on determinacy (+ at most one named lemma).
- **`MeasurePreservingFilter.lean`**: MP/escaping/above-id/constant and Part 1 itself as
  Martin-measure-pushforward (ultrafilter/Rudin–Keisler) statements; `RKle` + `pushCone_rkle_id` (the
  RK order on pushforwards is trivial — why RK-descent cannot prove Part 1).
- **`GraphFunction.lean`**: the graph `X ↦ X ⊕ F X = id ⊔ F`; the Martin order is an upper semilattice
  (`martinJoin_le`); precise reason MartinPPT cannot grip a counterexample.
- **`OrderPreservingCore.lean`**: `uncountableCofinal_iff_avoiding` — the order-preserving branch rests
  on **exactly one** open coding lemma (its two named hypotheses are equivalent).
- **`PosnerRobinson.lean`**: Posner–Robinson via the direct `G := jReal A` construction — the full
  theorem `posnerRobinsonFull (A) (h : ReadBack A) : ∃ G, A ⊕ G ≡ᵀ G'` bracketed by an explicit
  `ReadBack` Prop, with `readBack_iff` (bracket = exactly the hard read-back reduction), the cone case
  `A ≥ᵀ 0'` as a corollary, and `not_readBack_of_computable` (the gap provably FAILS for computable `A` —
  machine-checking it is a genuine obstruction, not accidentally provable).
- **`IncomparableArithReduction.lean`**: **a finer classification of Part 1's sole open content** —
  `partI_of_three_cases_and_arith`: Part 1 ⟸ `RegressiveSlamanSteel` (known) + `StrictArithRegressiveConstant`
  (the arithmetic-degrees regressive theorem, discharging the `AnBm` jump-distance sub-case) + three
  arithmetically-typed sub-cases (`AnAm`/`BnAm`/`BnBm`). Honest: a structural sharpening (one sub-case
  identified with a recognized open theorem), not a crossing. Also: `incomparableConstant_iff_four_subcases`
  (the four-way split is LOSSLESS) and `incomparable_not_below_argJoin` (a counterexample value escapes
  `X⊕Z` for every fixed `Z` — sharper than escaping).
- **`ArithRegressiveSkeleton.lean`**: `StrictArithRegressiveConstant` (the `AnBm` target) opened into its
  three *relativized* Slaman–Steel steps (tree / domination / coding relative to `X^(k)`); assembly PROVED,
  including the AnBm twist that step-3's `x ≤ᵀ F x` on a branch is a *contradiction* (vs the Turing case's
  "above identity"), the three steps bracketed.
- **`BnAmPartTwo.lean` + `OpenContentCapstone.lean`**: **the incomparable core has a COHERENT FOUR-FACE MAP.**
  For `G X := jump^[k](F X)` (invariant, above-id on the `Bn` cone): `bnAm_jumpComp_not_finite_jump` —
  `BnAm` forces `G` to *infinite* Part-2 rank (a structural leak into Part 2, not a reduction);
  `bnBm_jumpComp_finite_bounded` — `BnBm`
  keeps `G` at *finite* rank (`X ≤ᵀ G X ≤ᵀ X^(k+m)`). So the `Am`/`Bm` split (`F X ≰ₐ X` vs `F X ≤ₐ X`) IS
  the infinite/finite Part-2-rank split. Two of the four faces are the two known Martin regimes (AnBm=Part-1-regressive,
  BnAm=Part-2-increasing).
  `escapingMP_of_three_cases_and_arith` ports the decomposition to the canonical `escaping⟹MP` phrasing.
  The leak is abstracted to `am_not_finite_jump_of_increasing` (it uses *only* that the operator is
  increasing, `A ≤ᵀ op A`) — the precise property the enumeration-degree *skip* lacks, machine-connecting
  the analysis to Nakid-Cordero's e-degree contrast (arXiv:2510.19147; `ATTACK.md` B9+). Primary packaging
  `partI_of_arith_bnBm_escaping`: Part 1 ⟸ known SS + arith-regressive theorem + `ArithEscapingHalf` (Am,
  Part-2-flavoured) + `SubcaseBnBm`.
- **`BnBmSkeleton.lean`**: **`BnBm` reduces to the SAME relativized Slaman–Steel skeleton as `AnBm`**
  (`bnBm_of_cores`, machine-checked): the coordinated tree computing `F` from `x^(k)`, step-3's `x ≤ᵀ F x`
  on branches contradicting *incomparability* (branches on the incomp cone) exactly as `AnBm`'s contradicts
  arith-strictness. So the whole `Bm` region (`AnBm ∪ BnBm`) is uniformly relativized-S-S coordinated-tree
  brackets; the genuine CBER difficulty is concentrated in `BnBm`'s step-1 (`HasBnBmUniformTree`, an
  arith-*preserving* injective uniformization) — a distinct, plausibly harder bracket, NOT a separate
  method. `arithBelowHalf_of_bnBm_cores`: `ArithBelowHalf` ⟸ the `AnBm` + `BnBm` step-1 brackets.
  (Honest correction to earlier framing: `BnBm` is not "native to neither regime" — it is the
  incomparable-core instance of the Part-1 coordinated-tree method.)
- **`RegressiveSkeleton.lean`**: the KNOWN Slaman–Steel regressive theorem opened into its three steps
  (coordinated tree / branch domination / branch coding); assembly + downstream PROVED
  (`regressiveSlamanSteel_of_cores`, `regressiveImpliesConstant_of_cores`), the two hard steps bracketed.
- **`PartIIUniform.lean`**: **Part 2 opened for the uniform class** (previously untouched — Part 2 was
  proven for no class). `UniformRegular` + the Steel jump-chain inside it; assembly + exactness both ways
  (`partIIUniform_iff_cores`: uniform Part 2 ⟺ its three cores); comparison trichotomy + successor
  provable half proved; the three cores (comparison/well-foundedness/jump-minimality) bracketed.
- Extensive `ATTACK.md` original-research log: every fresh angle on the incomparable core funnels to the
  same barrier; sharpest new proof-level localization = the S-S *domination* step needs `x ≥ᵀ f x`, which
  incomparability denies. No crossing (expected). 82 files, full build green, all std axioms.

---

## The conjecture, and exactly what is open

**Part 1** (`ConstantOnCone F ∨ AboveIdOnCone F` for Turing-invariant `F`) reduces, provably
and losslessly, to two cores (`CoreAnalysis.partI_iff_cores`):
- `RegressiveImpliesConstant` — `F X <ᵀ X` on a cone ⟹ constant on a cone;
- `IncomparableImpliesConstant` — `F X ⊥ᵀ X` on a cone ⟹ constant on a cone.

**⚠️ CORRECTION (2026-08-23): the regressive core is NOT open — it is a KNOWN Slaman–Steel theorem.**
Slaman–Steel proved Part 1 for *all* regressive functions on the Turing degrees (Lutz–Siskind Thm 1.4:
`f(x) ≤ᵀ x ⟹ f` constant or `f(x) ≡ᵀ x` on a cone).  So `RegressiveImpliesConstant` follows outright
(`regressiveImpliesConstant_of_slamanSteel`, from `RegressiveSlamanSteel`).  The **sole genuinely-open
content of Part 1 is the incomparable core** (`IncomparableImpliesConstant`, functions "off to the
side").  Definitive statement: `partI_open_content_TFAE` — Part 1 ⟺ incomparable core ⟺ (escaping⟹MP)
⟺ (no escaping `F` incomparable to a fixed degree) are all equivalent, i.e. **one** open problem.
Earlier sections of this file (and the ω₁^x work below) mislabeled the *Turing* regressive core
as open, conflating it with Lutz's *hyperarithmetic-degrees* regressive result (`arXiv:2306.05746`, a
different degree structure); read them with that correction in mind.  Both cores additionally hold for
**uniformly**-invariant `F` (`partI_uniform`) and **degree-bounded** `F` (`bounded_implies_constant`).

**The two orthogonal inputs Part 1 rests on** (both determinacy theorems; the class-specific
one is the open one):

1. **Determinacy input** — `MartinDichotomy` (≡ `MartinPPT`, `martinPPT_iff_dichotomy`): every
   set contains a pointed perfect tree or its complement contains a cone. Its **invariant case
   is proved** (`perfectDichotomy_invariant`); a cone is *unconditionally* a full pointed
   perfect tree with the effective `recover` field (`cone_contains_PPT`).
   **The non-invariant case (Martin's Lemma 2.3 / "Martin's fusion") — its mathematical content
   is now MACHINE-CHECKED** (`MartinGame.lean`, 2026-08-23). The correct proof (Marks–Slaman–Steel
   Lemma 3.5) uses the *asymmetric* game — I plays `x`, II plays `y`, II loses unless `y ≥ᵀ x`, else
   I wins iff `x ≥ᵀ y ∧ x ∈ A`. Proved: `winsI_martinGame_of_cofinal` (cofinal ⟹ player I wins),
   `cofinal_realizes_cone`, and `martinGamePerfectEmbedding`/`cofinal_perfectEmbedding` (the pointed
   perfect embedding into `A` — the "game half" `PerfectEmbedding.lean` flagged as the sole gap).
   `MartinGameFusion.lean`/`MartinGameTree.lean` reduce the **whole** non-invariant case to a single
   computability fact `GameCodeBelow` (`codeGame σ ≤ᵀ σ`). **✅ That fact is now PROVED**
   (`MartinGameCode.gameCodeBelow`, 2026-08-23): `embVal_le` presents the game embedding as recursive-in-`σ`
   (primitive recursion on histories via `Nat.RecursiveIn.prec`), wrapped in the graph-prefix+`Primrec`
   pattern of `codeReal_le`. **So `MartinPPT` (Martin's Lemma 2.3) is now a THEOREM modulo only determinacy**:
   `martinPPT_of_gameDeterminacy` (`MartinGameCode.lean`). Downstream, everything that assumed `MartinPPT`
   is now dischargeable from determinacy — `GameCapstone.lean`: `measurePreservingAboveId_of_gameDeterminacy`
   (Lutz–Siskind **Theorem 3.4 from determinacy alone**), `partI_of_gameDeterminacy_escaping`,
   `partI_iff_escapingMP_of_gameDeterminacy` (**Part 1 ⟺ escaping⟹MP on determinacy alone**),
   `partI_iff_pushforward_of_gameDeterminacy`. All standard axioms only. Nothing here is a hypothesis
   anymore except determinacy itself; the open content is the incomparable core (input 2 below).

2. **Class-specific input** — `escaping ⟹ MP` (`escapingMP_iff_no_fixedIncomparable`,
   `EscapingDichotomy.lean`): equivalent to "no escaping invariant `F` is Turing-incomparable
   to a fixed degree on a cone." **This is the actual open problem.** See `ATTACK.md`.

`partI_of_dichotomy_noFixedIncomparable` (`PartIRecast.lean`) is the sharpest packaging:
Part 1 ⟸ (1) + (2).

**Cleanest corrected statements of the open content** (2026-08-23, given the KNOWN regressive theorem
`RegressiveSlamanSteel` and `MartinPPT`): `partI_iff_incomparable` — Part 1 ⟺ the incomparable core;
`escapingMP_iff_incomparable` — `escaping ⟹ MP` ⟺ the incomparable core; `partI_iff_escapingMP` — the
chain, so **all three coincide**.  There is genuinely *one* open problem (the incomparable core =
`escaping ⟹ MP`), the regressive core being a Slaman–Steel theorem.

**Cleanest single-hypothesis form** (`partI_general_of_uniformity`, `MartinResults.lean`): full
Part 1 ⟸ the *one* implication "`TuringInvariant F ⟹ UniformlyTuringInvariant F` (on a cone)" —
a **sufficient** condition (the intended route to the Borel case — though `Borel ⟹ uniform` is itself
**open**, ≈ Steel's conjecture; not necessary, since Part 1 doesn't imply uniformity). Everything
downstream is machine-checked; `ATTACK.md` analyses exactly why determinacy does not deliver this bridge
for `F` (cone dichotomy vs cone uniformization).

**Sharpened to Steel's conjecture** (`partI_general_of_steelBridge`, `MartinResults.lean`): full Part 1
⟸ "every `TuringInvariant F` is `MartinEquiv` (cone-`≡ᵀ`) to *some* uniformly-invariant `G`" — which is
**exactly Steel's conjecture** ("every definable Turing-degree function is equivalent to a uniformly
invariant one"), the literature's canonical reduction target. This *generalizes* the uniformity-bridge
form (take `G := F`). The contrapositive `counterexample_refutes_steel` shows a Part-1 counterexample
refutes Steel's conjecture. Grounding: Nakid-Cordero 2025 (arXiv:2510.19147) prove the bridge *fails* in
the enumeration degrees — so it is genuinely Turing-specific, not pure logic.

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
(everything downstream is machine-checked) — the intended route to the Borel case, **but the bridge is
open even for Borel** (Part 1 for general Borel is open; ≈ Steel's conjecture). It is sufficient, *not*
necessary (constant/above-id functions needn't be uniform), and its truth for `F` is itself open. `escapingMP_of_uniformity_bridge`: the bridge subsumes the
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
`churchKleene_invariant` + `omega_le_churchKleene` (`ω₁^X ≥ ω`, non-degeneracy — the rank is not
trivially `0`, so the engine constraint is non-vacuous) proven. Instantiating the engine:
`no_omega1_decreasing_conePreserving` (no cone-preserving regressive `F` strictly decreases `ω₁^x`) and
`regressive_omega1_dichotomy` (a regressive `F` preserves or strictly decreases `ω₁^x` on a cone). So a
cone-preserving counterexample is **`ω₁`-preserving**. **Sharper framing** (see `ATTACK.md`): the engine
*already* kills the `ω₁`-**decreasing** case (= `F X <_h X`, which is *all* of Lutz's `D_h` regressive
setting) via ordinal well-foundedness — no `Σ¹₁`-bounding. So the genuine open residual is the
`ω₁`-**preserving** = **hyp-preserving Turing case** (`F X ≡_h X`, `F X <ᵀ X`), a Turing-specific
phenomenon *vacuous* on `D_h` (Lutz never sees it), with no ordinal rank (the Turing degrees inside one
hyperarithmetic degree are ill-founded).

New constraints (`CounterexampleConstraints.lean`): `arithmetically_bounded_implies_constant`
(counterexample is *arithmetically* escaping), `nonconstant_above_or_incomparable_fixed` (per-degree
trap). Both open cores are reduced to jump-distance sub-cores (`regressiveCore_of_cases`,
`incomparableCore_of_cases`).

**Order-preserving case, reduced to the coding step** (`CounterexampleConstraints.lean`, following
Lutz–Siskind §4).  `partI_orderPreserving_of_coding`: Part 1 for *every* order-preserving `F` follows
from `MartinPPT` (⟹ Thm 3.4) plus the single atomic `OrderPreservingUncountableCofinal` — the
Groszek–Slaman–Kihara perfect-set coding (Cor 4.5).  The elementary pieces are all **proved**:
`nonconstant_values_uncountable` (Case 1: countable range ⟹ constant), `orderPreserving_mp_of_rangeCofinal`
(cofinal ⟹ MP), `orderPreserving_range_countablyDirected` (§4.2 directedness, via the reusable
`Cantor.component_le_joinFam`).  Chain: `avoidingImpliesConstant_of_theorem46` ⟶
`orderPreservingNonconstantMP_of_uncountableCofinal` ⟶ `partI_orderPreserving_of_theorem46`.  So the
sole remaining unformalized ingredient of the order-preserving case is the coding.

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
