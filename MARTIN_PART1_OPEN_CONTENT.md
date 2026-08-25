# The open content of Part 1 of Martin's conjecture: an arithmetic decomposition

*A rigorous exposition of the structural findings formalized in this project
(`RegressiveJumpDecomp.lean`, `IncomparableArithReduction.lean`, `RegressiveSkeleton.lean`,
`ArithRegressiveSkeleton.lean`, `BnAmPartTwo.lean`, `OpenContentCapstone.lean`).
All claims marked "formalized" are machine-checked in Lean 4 with only the standard axioms
`propext, Classical.choice, Quot.sound`, with determinacy threaded as an explicit hypothesis.*

## 1. Setup and the sole open core

Work in `2^ω` with Turing reducibility `≤ᵀ`, the Turing jump `X ↦ X'`, and the **Martin (cone)
measure** `U`: a set `A` of reals is `U`-large ("holds on a cone") iff it contains a Turing cone
`{X : Y ≤ᵀ X}` for some `Y`. Under Turing determinacy, `U` is a countably-complete ultrafilter on the
Turing-invariant sets (Martin's cone theorem). A function `F : 2^ω → 2^ω` is **Turing-invariant** if
`X ≡ᵀ Y ⟹ F X ≡ᵀ F Y`.

**Part 1 of Martin's conjecture** asserts: every Turing-invariant `F` is *constant on a cone* or *above
the identity on a cone* (`F X ≥ᵀ X` on a cone).

By comparability of `F X` and `X` (four regimes `≡ᵀ / >ᵀ / <ᵀ / ⊥ᵀ`, decided cone-wise by determinacy),
Part 1 reduces losslessly to two **cores** (`CoreAnalysis.partI_iff_cores`, formalized):
- **regressive core:** `F X ≤ᵀ X` on a cone `⟹` constant on a cone;
- **incomparable core:** `F X ⊥ᵀ X` on a cone `⟹` constant on a cone.

The regressive core is a **theorem of Slaman–Steel** (1988): a regressive Turing-invariant function is
constant on a cone or `≡ᵀ`-the-identity on a cone. (In this project it is a named input
`RegressiveSlamanSteel`, with its Slaman–Steel proof *structured into three steps* in
`RegressiveSkeleton.lean`; see §5.) Hence:

> **The incomparable core is the sole genuinely-open content of Part 1.**

Equivalently (`escapingMP_iff_incomparable`, formalized), it is `escaping ⟹ measure-preserving`: an
invariant `F` whose values avoid every fixed degree from below on a cone (`F X ≰ᵀ Z`) reaches every fixed
degree from above on a cone (`Z ≤ᵀ F X`).

## 2. The jump-distance decomposition

Write `X^(k)` for the `k`-th Turing jump, and the two **arithmetic** relations
`X ≤ₐ Y :⇔ ∃ k, X ≤ᵀ Y^(k)` (arithmetic reducibility) and `X ≡ₐ Y`, `X <ₐ Y` accordingly. Arithmetic
reducibility is the transitive closure of "`≤ᵀ` a finite jump"; `X ≤ₐ Y` says `X` is arithmetic in `Y`.

For an incomparable `F` (`F X ⊥ᵀ X`), apply Martin's cone theorem twice — once to
`{X : X ≤ₐ F X}` and once to `{X : F X ≤ₐ X}` (both Turing-invariant) — to split the incomparable core,
on a cone, into **four sub-cases** by the *arithmetic* position of `F X` relative to `X`
(`RegressiveJumpDecomp.incomparableCore_of_cases`, formalized):

| sub-case | `X` vs `F X` (Turing) | `X` vs `F X` (arithmetic) |
|---|---|---|
| **AnBm** | `⊥ᵀ` | `F X <ₐ X` (F X arithmetically below) |
| **BnAm** | `⊥ᵀ` | `X <ₐ F X` (F X arithmetically above) |
| **BnBm** | `⊥ᵀ` | `F X ≡ₐ X` (arithmetically equivalent) |
| **AnAm** | `⊥ᵀ` | `⊥ₐ` (arithmetically incomparable) |

Here `An : ∀ k, X ≰ᵀ (F X)^(k)` (i.e. `X ≰ₐ F X`), `Bm : ∃ k, F X ≤ᵀ X^(k)` (i.e. `F X ≤ₐ X`), and
dually for `Bn`, `Am`. Every incomparable `F` lands, on a cone, in exactly one sub-case.

## 3. The AnBm sub-case is the arithmetic-degrees regressive theorem

The **AnBm** sub-case is exactly: `F X` is *arithmetically strictly below* `X` (`F X <ₐ X`), yet
Turing-incomparable to `X`. This is `arithmetic`-regressive. Define the arithmetic analogue of the
regressive core:

> **`StrictArithRegressiveConstant`:** every Turing-invariant `F` with `F X <ₐ X` on a cone is constant
> on a cone.

**Formalized (`IncomparableArithReduction`):**
- `incomparable_AnBm_of_strictArithRegressive` — the AnBm sub-case follows from
  `StrictArithRegressiveConstant`;
- `incomparableCore_of_three_cases_and_arith` — the incomparable core reduces to
  `StrictArithRegressiveConstant` **plus** handlers for the three sub-cases AnAm, BnAm, BnBm;
- `partI_of_three_cases_and_arith` — hence Part 1 reduces to `RegressiveSlamanSteel` (known) +
  `StrictArithRegressiveConstant` + three arithmetically-typed sub-cases.

**Honest status of this reduction.** `StrictArithRegressiveConstant` is *strictly weaker than the full
incomparable core* (it is one of the four sub-cases). But it is not weaker than AnBm — its own open
content *is* AnBm. So this is a **rephrasing** of the sub-case (`F X <ₐ X` for `F`) in
arithmetic-reducibility terms, not a reduction-to-something-easier.

**Important caveat (an honesty correction).** `StrictArithRegressiveConstant` is a statement about
*Turing*-invariant `F` (it inherits `F`'s Turing-invariance). It is therefore **not** literally "the
arithmetic-degrees Martin conjecture," which would concern `≡ₐ`-**invariant** functions on the arithmetic
degrees `D_a` (`X ≡ₐ Y ⟹ F X ≡ₐ F Y`). Turing-invariance does **not** imply `≡ₐ`-invariance (`X ≡ₐ Y` is
weaker than `X ≡ᵀ Y`, so Turing-invariance says nothing about `≡ₐ`-equivalent inputs). So AnBm is a
Turing-invariant, arithmetic-*regressive* statement — *analogous* to, but genuinely distinct from, the
`≡ₐ`-invariant arithmetic Martin conjecture. Its value is that it suggests attacking AnBm by the
Slaman–Steel *method* carried out relative to finite jumps (§4), while making the invariance subtlety
explicit.

## 4. Which *method* could reach AnBm, and why neither known one does

The regressive theorem — "is a regressive invariant function constant on a cone?" — is settled at two
*invariance* levels, by two different methods:

| invariance | domain | regressive theorem | method |
|---|---|---|---|
| **Turing** `≡ᵀ` | `D_T` | Slaman–Steel 1988 | coordinated tree + domination + growth-rate coding (§5) |
| **hyperarithmetic** `≡_h` | `D_h` | Lutz 2024 (`arXiv:2306.05746`) | `ω₁^x` ordinal rank / Σ¹₁-bounding |

AnBm is a **Turing**-invariant function that is *arithmetic*-regressive (`F X <ₐ X`). It is *not* the
`≡ₐ`-invariant "arithmetic level" of this hierarchy (the §3 caveat — different invariance notion), but its
arithmetic-reducibility hypothesis places it, in spirit, between the two rows, and — the point — **neither
known method reaches it.** Two independent reasons:

**(a) It does not collapse to the Turing theorem** (level induction fails). One might hope to prove
`F X ≤ᵀ X^(k+1)` by relativizing the Turing theorem to `X'` (since `X^(k+1) = (X')^(k)`). This fails
because a **Turing**-invariant `F` need not be **jump**-invariant: `X' ≡ᵀ Y'` does not imply `X ≡ᵀ Y`
(the jump is not degree-injective downward — Sacks/Shoenfield), so `F` induces no well-defined function
on the jumps, and the relativized theorem has nothing to apply to.

**(b) Lutz's hyperarithmetic theorem does not apply** (invariance mismatch). Lutz proves the regressive
theorem for `≡_h`-**invariant** functions on the hyperarithmetic degrees `D_h`. A Turing-invariant `F`
is generally *not* hyp-invariant: `X ≡_h Y` (weaker than `≡ᵀ`) does not give `X ≡ᵀ Y`, so
Turing-invariance does not force `F X ≡_h F Y`, and `F` induces no function on `D_h`. The invariance
notion is genuinely different.

This is the crisp reason the arithmetic-regressive theorem is a *distinct*, open target: it sits at a
reducibility where neither the Turing method (which needs Turing-invariance and has no jump handle) nor
the hyperarithmetic method (which needs hyp-invariance) directly applies. A proof would presumably use
the Slaman–Steel *method* — a pointed perfect tree on which `F` is uniformized, plus domination and a
growth-rate coding — carried out at the arithmetic level; this is what `RegressiveSkeleton.lean`
isolates abstractly (§5), and relativizing that machinery to `X^(k)` is the concrete obstacle.

## 5. The Slaman–Steel method, abstractly (why it settles Turing but not the incomparable core)

`RegressiveSkeleton.lean` structures the Slaman–Steel proof of the regressive core into three steps for a
non-constant regressive invariant `F`:
1. **coordinated tree** (`HasRegressiveUniformTree`): a pointed perfect tree `T` with a single code `e`
   computing `F` on all branches, `F` injective on branches;
2. **domination** (`BranchDomination`): on branches, every `g ≤ᵀ x` is dominated by some `h ≤ᵀ F x` —
   *else `x` diagonalizes against `F x = Φ_e^x`*;
3. **coding** (`BranchCoding`): code the bits of `x` into the relative growth rates of two
   `F x`-computable fast-growing functions, forcing `x ≤ᵀ F x` on branches; with regressivity, `F x ≡ᵀ x`
   on the tree's cone.

The assembly (steps ⟹ regressive theorem) and all downstream logic are **formalized**; steps 1–2 are the
recursion-theoretic content, bracketed.

**The precise reason this method does not transfer to the incomparable core.** Step 2 (domination) needs
`x` to *compute* `F x` in order to diagonalize against `F x = Φ_e^x`. For regressive `F` this holds
(`F x ≤ᵀ x`). For **incomparable** `F`, `x ≱ᵀ F x`, so `x` cannot access `F x` to diagonalize — the
domination step has no purchase. Thus the incomparable core is not merely "no code" but specifically
"**no domination handle**": even granting a code for `F` on a tree, the growth-rate coding cannot start,
because the argument must dominate the value and incomparability forbids exactly that. This is the
sharpest proof-level statement of why the one method that settles the regressive case fails here.

## 6. Status of the other three sub-cases

- **BnAm** (`X <ₐ F X`, Turing-incomparable): `F X` is arithmetically strictly above `X`. **This
  sub-case leaks into Part 2** (`BnAmPartTwo.bnAm_jumpComp_not_finite_jump`, formalized). The derived
  function `G X := jump^[k](F X)` is Turing-invariant and, on the `Bn` cone, above identity
  (`X ≤ᵀ (F X)^(k) = G X`), so Part 2 assigns it a jump-hierarchy rank. That rank cannot be *finite*:
  `G ≡ᵀ jump^[j]` on a cone would give `F X ≤ᵀ (F X)^(k) ≡ᵀ X^(j)`, contradicting `Am` (`F X ≰ₐ X`, the
  defining `m`-component of `BnAm`) at `m = j`. So
  `BnAm` survives only by exhibiting a *transfinite*-rank increasing function — precisely a Part-2 object,
  whose existence off the uniform class is itself open. So `BnAm` *produces* a Part-2 object and is at
  least as hard as understanding it. (Caveat, stated honestly: this is a structural leak, **not** a
  reduction of `BnAm` to Part 2 — even granting Part 2 the graph/`jump^[k]∘F` equivalence `≡ᵀ X^(α)` does
  not by itself force `F` constant, since recovering `F` from the derived object is the separate
  non-invariant "odd-part" problem. The value is locating `BnAm` in Part-2 territory, not dissolving it.)
- **BnBm** (`F X ≡ₐ X`, Turing-incomparable): the *arithmetic-preserving, Turing-dropping* phenomenon —
  `F` maps `X` to another Turing degree in the same arithmetic degree. This is genuinely `Turing`-specific
  (vacuous on `D_h`, where `F X <_h X` always strictly drops `ω₁^x`), which is precisely why Lutz's
  method never encounters it. No ordinal rank is available (the Turing degrees inside one hyperarithmetic
  degree are ill-founded). **However, `BnBm` is not structurally exotic: it reduces to the *same*
  relativized Slaman–Steel skeleton as `AnBm`** (`BnBmSkeleton.bnBm_of_cores`, machine-checked) — the
  coordinated tree computing `F` from `x^(k)`, with step-3's `x ≤ᵀ F x` on branches contradicting
  *incomparability* `¬ x ≤ᵀ F x` (branches sit on the incomparability cone) exactly as `AnBm`'s
  contradicts arith-strictness. The genuine CBER difficulty is concentrated in the step-1 bracket
  `HasBnBmUniformTree` (an arith-*preserving* injective uniformization coordinated with the tree) — a
  distinct, plausibly harder, open bracket, but the *method* is not new.
- **AnAm** (arithmetically incomparable): the transfinite residue. Splitting by `ω₁^{F X}` vs `ω₁^X` and
  invoking the project's ordinal-ultrapower engine (`no_omega1_decreasing_conePreserving`, formalized)
  would kill the `ω₁`-decreasing case — *but only under cone-preservation* (`base ≤ᵀ F X` on the cone),
  which an incomparable `F` does not provide. This cone-preservation caveat is the barrier. Like `BnAm`,
  `AnAm` also **leaks to Part 2 via the graph** (`am_graph_not_finite_jump`): since `AnAm` has `Am`
  (`F X ≰ₐ X`), the invariant above-identity function `X ↦ X ⊕ F X` has transfinite Part-2 rank. So the
  whole `Am` region (`F X ≰ₐ X`, = `BnAm ∪ AnAm`) is Part-2-flavoured; only `BnBm` (inside the `Bm` region)
  is native to neither Martin regime.

**The primary divide is `Bm` vs `Am` (i.e. `F X ≤ₐ X` vs `F X ≰ₐ X`):**
- `Bm` = `AnBm ∪ BnBm`: `F X ≤ᵀ X^(k)`. `AnBm` is the arithmetic-degrees **regressive** theorem
  (Part-1 method, structured); `BnBm` is the arithmetic-preserving CBER residue.
- `Am` = `BnAm ∪ AnAm`: the graph `X ⊕ F X` is a **transfinite-rank Part-2** object
  (`am_graph_not_finite_jump`). Part-2-flavoured.

## 7. Summary and open questions

The sole open content of Part 1 is now decomposed into four arithmetically-typed pieces, and each connects
to a **recognizable regime**:
- **AnBm** (`F X <ₐ X`) is the arithmetic-degrees regressive theorem — the missing middle of the
  Turing/arithmetic/hyperarithmetic hierarchy — now structured via relativized Slaman–Steel
  (`ArithRegressiveSkeleton`).
- **BnAm** (`X <ₐ F X`) **produces a Part-2 object**: it forces `jump^[k]∘F` to be a transfinite-rank
  above-identity function (`bnAm_jumpComp_not_finite_jump`) — a structural leak into Part 2, not a
  reduction (see §6 caveat).
- **BnBm** (`F X ≡ₐ X`) and **AnAm** (arithmetically incomparable) are the genuinely Turing-specific
  transfinite residue — the arithmetic-preserving-Turing-dropping phenomenon and the `ω₁`-decreasing
  case respectively, each with a precise obstruction below.

So the incomparable core is not a monolith. Organized by the **primary arithmetic divide** `F X ≤ₐ X`
(`Bm`) vs `F X ≰ₐ X` (`Am`) — machine-checked lossless as `incomparableConstant_iff_arith_halves`, and
lifted to the canonical open statement as `escapingMP_iff_arith_halves` (`escaping ⟹ MP` ⟺
`ArithBelowHalf ∧ ArithEscapingHalf`):
- the entire `Am` half (`BnAm ∪ AnAm`) **produces a transfinite-rank Part-2 object** via the graph
  `X ⊕ F X` (`am_graph_not_finite_jump`) — Part-2-flavoured (structurally, not by reduction);
- the `Bm` half is `AnBm` (the arithmetic **regressive** theorem, structured) together with `BnBm`.

**Why `Bm`/`Am` is exactly the right divide.** `Bm` (`F X ≤ₐ X`) says `F X` is computable from a *finite
jump* `x^(k)` of the argument — precisely the hypothesis a coordinated tree needs (a single code
`F x = Φ_e^{x^(k)}` on branches). So the `Bm` half is exactly the **coordinated-tree-amenable** region,
and both its faces (`AnBm`, `BnBm`) reduce to that method (`arithBelowHalf_of_all_tree_cores`). `Am`
(`F X ≰ₐ X`) says `F X` *escapes every finite jump* of `x`, so no such code exists and the coordinated-tree
method cannot even start — which is exactly why the `Am` half instead routes through the graph into Part-2
(transfinite) territory. The primary arithmetic divide is therefore the boundary of the relativized
Slaman–Steel method itself.

Both faces of the `Bm` half now reduce to the **same relativized Slaman–Steel skeleton**
(`ArithRegressiveSkeleton` for `AnBm`, `BnBmSkeleton` for `BnBm`; both machine-checked assemblies),
differing only in the source of the step-3 contradiction — arith-strictness for `AnBm`, incomparability
for `BnBm`. So **every one of the four faces lands in a recognizable regime**: `AnBm`/`BnBm` are
relativized-S-S coordinated-tree brackets (Part-1 method), `BnAm`/`AnAm` produce transfinite-rank Part-2
objects via the graph. The genuine Turing-specific/CBER difficulty is not a *separate method* — it is
concentrated in the `BnBm` step-1 bracket `HasBnBmUniformTree` (arithmetic-preserving injective
uniformization), a distinct and plausibly harder instance of the same coordinated-tree crux that `AnBm`
also brackets.

**Concrete open questions this raises:**
1. *Does the arithmetic-degrees regressive theorem hold?* I.e. is a Turing-invariant `F` with
   `F X <ₐ X` on a cone constant on a cone? A proof would carry the Slaman–Steel coordinated-tree +
   domination + coding argument out relative to a finite jump — the obstacle being that the tree and the
   domination must be arranged relative to `X^(k)` while `F` is only Turing-invariant. This is now
   **structured in full** (`ArithRegressiveSkeleton`): the three relativized Slaman–Steel steps are named
   `Prop`s, and the assembly is machine-checked — including the AnBm-specific twist that step 3's `x ≤ᵀ F x`
   on a branch is a *contradiction* (against branch-strictness `X ≰ₐ F X`) rather than the Turing case's
   "above identity". What remains open is exactly the three bracketed steps (the relativized tree
   existence, domination, and coding).
2. *Does determinacy supply the `BnBm` coordinated tree* (`HasBnBmUniformTree`)? `BnBm` reduces to the
   same relativized-S-S skeleton as `AnBm` (`BnBmSkeleton.bnBm_of_cores`, machine-checked), so its open
   content is exactly this step-1 bracket: a tree computing an arithmetic-*preserving* injective `F` from
   `x^(k)`, with branches on the incomparability cone. This is the CBER/MSS heart — the same coordinated-tree
   crux as (1), in a distinct and plausibly harder instance.
3. *Can the `Am` region (`F X ≰ₐ X`) be reduced, not merely leaked, to Part 2?* The graph `X ⊕ F X` is a
   transfinite-rank Part-2 object, but recovering `F` from it is the non-invariant "odd-part" problem; and
   the `ω₁`-decreasing part of `AnAm` needs the ordinal-ultrapower engine freed of cone-preservation.
   Unlike the `Bm` region, the `Am` region is *not* coordinated-tree-amenable (`F X` escapes every finite
   jump of `x`), so it genuinely needs the transfinite machinery or a new idea.

None of these is a two-line corollary of the tools available; the incomparable core's resistance is
inner-model-theoretic in flavour (cf. Siskind, *Aspects of Martin's Conjecture and Inner Model Theory*),
consistent with its ~50-year-open status. The value here is a **sharp, machine-checked map** of exactly
what a proof of Part 1 must still supply.

**Bottom line (machine-checked, `partI_of_arith_bnBm_escaping`).** Part 1 holds given four inputs, sorted
by recognizability:
1. `RegressiveSlamanSteel` — **known** (the Turing regressive theorem);
2. `StrictArithRegressiveConstant` — the arithmetic-degrees **regressive** theorem (a recognizable target,
   structured into three relativized Slaman–Steel steps);
3. `ArithEscapingHalf` — the `F X ≰ₐ X` region, which **produces a transfinite-rank Part-2 object** via the
   graph (Part-2-flavoured);
4. `SubcaseBnBm` — the arithmetic-preserving Turing-dropping case; itself reduces to the *same* relativized
   Slaman–Steel skeleton as (2) (`BnBmSkeleton.bnBm_of_cores`), so its residual open content is the step-1
   bracket `HasBnBmUniformTree` — the CBER/MSS heart, a distinct and plausibly harder instance of the same
   coordinated-tree crux.
So the open content of Part 1, stripped to its irreducible core, is **two coordinated-tree brackets**
(the `AnBm` and `BnBm` step-1's of relativized Slaman–Steel) plus the Part-2-flavoured `Am` region — one
method, not a monolithic mystery. The genuine difficulty lives entirely in whether determinacy supplies a
coordinated tree computing an incomparable/arith-regressive `F` from a finite jump of the branch.

## 8. The barrier, precisely (why no available tool crosses)

Every attempted proof of the incomparable core reduces to one demand on the (non-definable) invariant
`F`, and the four sub-cases show *where* each demand fails. The demands, and the single obstruction
underlying them:

**The obstruction (one sentence):** determinacy provides *cone dichotomy* — Martin's cone theorem, that an
invariant set contains a cone or its complement does — but Part 1 needs *cone uniformization*: an
effective (Turing, on a cone) selection extracting a code `Φ_e` from `F`. Definable ≠ Turing-uniform, and
no determinacy hypothesis (AD, AD_ℝ, AD⁺) manufactures a Turing functional; it manufactures definability.

This splits into three "walls," each of which an arbitrary invariant `F` denies:
1. **No code / effectiveness.** Recursion-theoretic arguments (Posner–Robinson, Steel's game, the
   recursion theorem) need `F` as an oracle/code; but `F` is a function on *all* reals, not a single
   real, so it cannot be oracle-ized without losing invariance.
2. **Definable ≠ computable selection.** AD uniformizes the good-representative relation `G_e = {Y : F Y =
   Φ_e^Y}` definably, never by a Turing functional. This is *orthogonal to determinacy strength*.
3. **Regularity is orthogonal to cones.** AD's measure/Baire/perfect-set regularity lives on
   conull/comeager sets; Turing cones are **null and meager**, so regularity never transfers to a cone.
   (`(B5)` in the attack log: `F` is continuous on a comeager perfect set, but that set does not realize
   a cone; a cone-realizing pointed perfect tree is where AD's continuity says nothing.)

The **regressive core is settled** because regressivity supplies wall 1: `F X ≤ᵀ X` gives a code, and the
Slaman–Steel coordinated tree + *domination* (which needs `x ≥ᵀ F x` — §5) + coding then run. The
incomparable core denies wall 1 *at the level of `x` itself*: `F X ⊥ᵀ X` gives no code from `x` directly.
But the decomposition refines this. On the **`Bm` region** (`F X ≤ₐ X`, i.e. `AnBm ∪ BnBm`) there *is* a
code — from a **finite jump** `x^(k)` — and the whole coordinated-tree method runs relative to `x^(k)`
(`arithBelowHalf_of_all_tree_cores`), the residual barrier being only the *uniformity* of that code (the
step-1 brackets `HasArithRegressiveUniformTree` / `HasBnBmUniformTree`). On the **`Am` region**
(`F X ≰ₐ X`) there is no code from *any* finite jump — the strongest denial of wall 1 — which is exactly
why the `Am` region is not coordinated-tree-amenable and leaks instead to (transfinite) Part 2. So wall 1
is not monolithic: it is overcome at the finite-jump level on `Bm` (leaving a uniformity bracket) and
genuinely absent on `Am`.

## 9. Characterizations of the three residue sub-cases

These are the machine-adjacent findings that pin *why* each residue sub-case resists (attack-log B7–B8):

- **AnAm (arithmetically incomparable).** The ordinal-ultrapower engine
  (`no_omega1_decreasing_conePreserving`, formalized) kills the `ω₁`-decreasing part — *but only under
  cone-preservation*, and cone-preservation is **un-manufacturable** for an incomparable `F`: a fixed
  base `G := F ⊕ base` floors the `ω₁`-descent at the fixed ordinal `ω₁^{base}` (so no *infinite* descent,
  no contradiction), while incomparability forces a *bounded kernel*
  (`nonMP_kernel_avoids_cone`, formalized), so no unbounded base below `F X` exists to avoid the floor.
  The measure-theoretic obstruction (bounded kernel) and the ordinal one (cone-preservation caveat) are
  **the same obstruction**.
- **BnBm (arithmetically equivalent, Turing-incomparable).** Here `F` preserves the ω-jump:
  `(F X)^(ω) ≡ᵀ X^(ω)` (from `F X ≤ᵀ X^(k)` ⟹ `(F X)^(n) ≤ᵀ X^(k+n)`, dually). So on this cone `F` is the
  *identity on the ω-jump degrees* yet *Turing-nontrivial below the ω-jump* — a rigidity-relative-to-the-
  ω-jump question, genuinely Turing-specific and **invisible to the ω₁-engine** (finite jumps strictly
  increase `ω₁^x`, so arithmetic equivalence gives no `ω₁^x` control). This is the *arithmetic-preserving,
  Turing-dropping* phenomenon: `F` shuffles the Turing degrees *inside a single arithmetic equivalence
  class*, which is precisely the domain of Marks–Slaman–Steel's work on arithmetic equivalence `≡_A` and
  countable Borel equivalence relations. **This `≡_A`/CBER content is exactly the step-1 bracket
  `HasBnBmUniformTree`** (`BnBmSkeleton`): `BnBm` reduces to the same relativized-S-S coordinated-tree
  skeleton as `AnBm`, and the arith-preserving injective uniformization the tree demands *is* the MSS
  transversal question. So the MSS framework is not an alternative to the coordinated-tree method — it is
  what that method's step 1 asks for on this sub-case.
- **BnAm (arithmetically above, Turing-incomparable).** `F X >ₐ X`; the derived above-identity function
  `jump^[k]∘F` has *infinite* Part-2 rank (`bnAm_jumpComp_not_finite_jump`, formalized), so `BnAm` produces
  a transfinite-rank Part-2 object — a structural leak into Part 2 (not a reduction; recovering `F` is the
  odd-part problem). Together with `AnAm` it forms the `Am` region, uniformly leaked to Part 2 via the
  graph (`am_graph_not_finite_jump`).

## 10. Why no counterexample can be exhibited

A final structural point, dual to the above. Under determinacy, **no *definable* `F` is a
counterexample**: a Borel (indeed ∞-Borel-with-a-code) invariant `F` is *uniform on a cone*
(Slaman–Steel), hence satisfies Part 1 (`partI_uniform`, formalized). So every *writable* candidate `F`
must fail one of {invariant, incomparable, non-constant, definable}: the definable ones collapse to
uniform-hence-Part-1 (a definable "leftmost incomparable value" is not degree-invariant — it depends on
the real, not its degree); the AC-choice ones (`g(d) < d`) are non-measurable and vanish under
determinacy. So the incomparable core is a statement one can neither *prove* with the available tools nor
*refute* with an exhibited example — its content is exactly that determinacy forbids the non-definable
choice, and understanding that impossibility is inner-model-theoretic (Siskind). This is why the value
delivered is a sharp map of the open content rather than a resolution.
