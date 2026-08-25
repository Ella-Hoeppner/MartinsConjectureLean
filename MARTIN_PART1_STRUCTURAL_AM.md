# The structural (∞-Borel) attack on the `Am` region

*Developing the route the ω₁-obstruction (`MARTIN_PART1_APPROACH_OMEGA1.md`) pointed to: elementary
determinacy gives only countable/{0,1} information and the `Am` region has no **Turing** code, so use the
**definability / ∞-Borel** code of `F` to manufacture a "pseudo-code" on a cone. This note develops that
route rigorously, and — the main new content — **cleanly separates the Borel case (which has a fixed jump
level and avoids Lutz's obstruction entirely) from the genuine ∞-Borel case (where the obstruction lives).**
Not a solve; a sharp localization with a correct entry-point theorem.*

Recall the `Am` region: invariant `F`, `F X ⊥ᵀ X` on a cone, `F X ≰ₐ X` (F escapes every *finite* jump of
`X`) — the region with no Turing code and the open heart.

## 1. Entry point (rigorous): a Borel invariant `F` sits at a FIXED jump level

> **Theorem A.** If `F : 2^ω → 2^ω` is Turing-invariant and **Borel** of Baire rank `ρ`, then
> `F X ≤ᵀ X^(ρ)` on a cone, with `ρ` a **fixed** ordinal (independent of `X`).

*Proof.* A Borel function of Baire rank `ρ` is computed by `ρ` iterations of "take a limit", each of which is
one Turing jump: `F X ≤ᵀ (X ⊕ b)^(ρ)` where `b` is a Borel code for `F` of rank `ρ` (equivalently: the graph
is `Δ⁰_ρ(b)`, so the unique `y` with `(X,y) ∈ graph` is uniformly `≤ᵀ (X⊕b)^(ρ)`). On the cone above `b`,
`(X⊕b) ≡ᵀ X`, so `F X ≤ᵀ X^(ρ)`. ∎

Consequences, by whether `ρ` is finite:
- **`ρ` finite** ⇒ `F X ≤ᵀ X^(ρ)` is arithmetic ⇒ `F X ≤ₐ X` ⇒ the **`Bm` region**, handled by the
  relativized Slaman–Steel coordinated tree at finite level (`ArithRegressiveSkeleton` / `BnBmSkeleton`).
- **`ρ` transfinite** ⇒ `F X ≤ᵀ X^(ρ)` for a **fixed transfinite** `ρ` ⇒ the `Am` region, but at a *single
  fixed level*.

## 2. Main point: Borel `Am` has NO rank-unboundedness — it is a transfinite `Bm`

The obstruction that stops Lutz's method from descending to the Turing degrees is **rank unboundedness**: for
a general hyp-regressive `F`, `F X ≤ᵀ X^(α_X)` with `α_X < ω₁ˣ` *varying and unbounded* on a Turing cone
(because `ω₁ˣ` is unbounded below `ω₁` there), so no fixed level works. **Theorem A shows this never happens
for Borel `F`:** the level is the *fixed* Baire rank `ρ`. So:

> The Borel `Am` region is exactly a **transfinite `Bm` region** at the fixed level `ρ` — the *same* situation
> as the finite `Bm` region one level up. It reduces to a coordinated tree computing `F X = Φ_e^{X^(ρ)}` on
> branches with the incomparability branch-field — the verbatim transfinite analogue of `BnBmSkeleton`, with
> **`ρ` fixed and no `Σ¹₁`-bounding needed**.

So for Borel `F`, Lutz's obstruction is *absent*, and Part 1 reduces to a single bracketed step: the
**level-`ρ` coordinated tree**. This is a genuine clarification — the Borel case was lumped with "the
hard transfinite / Lutz-Turing gap", but it is not there; it is structurally the finite `Bm` case at a fixed
transfinite level.

**Caveat — this does NOT make Borel `F` uniformly invariant (why Borel Part 1 stays open).** Theorem A gives
uniformity **from the argument** (type A: `F X = Φ_e^{X^(ρ)}`, a single functional applied to the ρ-jump), which
is *not* uniform **invariance** (type B: a single functional reducing the *values* `F X ≤ᵀ F Y` from `X ≡ᵀ Y`).
Indeed `F X = Φ_e^{X^(ρ)}` and `X ≡ᵀ Y` give `F X ≤ᵀ Y^(ρ)`, but **not** `F X ≤ᵀ F Y` — recovering `Y^(ρ)`
from `F Y` fails because `F Y ≤ᵀ Y^(ρ)` *strictly* (F loses the jump information; this is exactly the
incomparable case `F Y ⊥ᵀ Y`). So Slaman–Steel's uniform-invariance Part 1 does **not** apply, and the
level-`ρ` coordinated tree (bridging type-A uniformity to Part 1 via domination+coding) is genuinely required.
This `(A) ↛ (B)` gap is the reason Borel Part 1 is open despite Theorem A.

## 2.5. For Borel `F`, the coordinated TREE is dischargeable — the open step is DOMINATION

The level-`ρ` coordinated tree (`LevelCoordinatedTree.LevelUniformTree`) has five fields; for Borel `F`
**four of them come for free**, leaving only the domination/coding steps:

- `computes` and `regressive_branch` (`F x = Φ_e^{x^(ρ)}`, `F x ≤ᵀ x^(ρ)`): **Theorem A** gives these
  *uniformly on the whole cone*, with a **single** `e` from the Borel code — so there is **no
  good-representative barrier** for Borel `F` (the barrier that blocks the general case is dissolved by the
  Borel code).
- `injective` (`F` injective on branches): the relation `F X ≡ᵀ F Y` is a Borel equivalence relation with
  **uncountably many classes** (`nonconstant_values_uncountable`), so **Silver's dichotomy** yields a perfect
  set of pairwise-`≢ᵀ` (hence distinct) values — `F` is injective on it.
- `incomparable_branch` (`¬ x ≤ᵀ F x`): holds on the incomparability cone.

Modulo a pointed-perfect refinement (intersecting Silver's perfect set with the cone's pointed tree,
`MartinPPT`-style), `HasLevelUniformTree` **holds for Borel `F`**. So the entire open content of Borel `Am`
collapses to the **domination step** `LevelBranchDomination`: on a branch `x`, every `≤ᵀ x` function is
dominated by a `≤ᵀ F x` function.

**And domination is exactly where incomparability bites.** In the *regressive* case (`F x ≤ᵀ x`) the
`F x`-computable functions sit inside the `x`-computable ones and Slaman–Steel *derive* domination; the coding
then gives `x ≤ᵀ F x`. For **incomparable** `F` (`F x ⊥ᵀ x`), `x` carries information `F x` lacks, so whether
`F x`-computable functions dominate `x`-computable ones depends on the relative domination degrees of two
*incomparable* reals — genuinely unclear, and (by the coding) domination would *force* `x ≤ᵀ F x`,
contradicting incomparability. So **domination cannot hold on a tree unless the incomparable case is already
impossible** — the domination bracket *is* the incomparable core in disguise, now pinned to a single
recursion-theoretic property at the fixed level `ρ`.

> **Sharpened localization.** For Borel `F`, Part 1 (`Am`) reduces — with the tree, the code, and injectivity
> all discharged — to the *single* question: *can the Slaman–Steel domination hold on a coordinated tree for a
> Turing-incomparable `F`?* Equivalently, must `x`-computable functions be dominated by `F x`-computable ones
> on a coordinated tree. This is the exact recursion-theoretic heart, at fixed level `ρ`.

**Uniform vs. per-function domination — the obstruction is half-provable.** There are two readings:
- **Uniform:** a *single* `h ≤ᵀ F x` dominates *every* `g ≤ᵀ x`. Such an `h` is (up to `≡ᵀ`) a modulus
  dominating all `x`-computable functions, hence computes `x'`; so uniform domination forces `x' ≤ᵀ F x`,
  whence `x ≤ᵀ F x` — **contradicting incomparability**. So **uniform domination is provably impossible for
  incomparable `F`.** The Slaman–Steel method, *if it needs uniform domination, provably cannot reach the
  incomparable core.*
- **Per-function:** for *each* `g ≤ᵀ x`, *some* `h_g ≤ᵀ F x` dominates `g` (`h_g` may depend on `g`). This
  does **not** force `x' ≤ᵀ F x` (no single dominant), so it is not immediately contradictory. It is the
  only version that could survive, and whether a coordinated tree can *arrange* per-`g` domination for an
  incomparable `F` (via Kumabe–Slaman genericity, without making `F x` high over `x`) is **the** open crux.

> **Net.** The half of the domination that is *uniform* is killed by incomparability outright; the surviving
> open content is exactly "per-function domination on a coordinated tree for incomparable `F`", at the fixed
> Borel level `ρ`. This is a sharp, concrete recursion-theoretic target — and it explains structurally why the
> Slaman–Steel machinery (built to derive `x ≤ᵀ F x`) sits in tension with the incomparable core (where
> `x ≤ᵀ F x` is false): the tension is precisely the uniform-domination impossibility.

## 2.6. HONEST LIMITATION: the coordinated-tree method is *circular* for the incomparable core

Chasing the domination step to its end forces a correction to the optimistic "the incomparable core reduces
to a coordinated tree" framing (the `BnBmSkeleton` / `LevelCoordinatedTree` reductions). The three brackets
combine as:
`(coordinated tree) ∧ (domination) ∧ (coding: domination ⟹ x ≤ᵀ F x)  ⟹  x ≤ᵀ F x`.
For **regressive** `F` (`F x ≤ᵀ x`) this is fine — with `F x ≤ᵀ x` it gives `F x ≡ᵀ x`, the "≡ identity"
outcome — and Slaman–Steel *prove* domination and coding, so the method works. For the **incomparable** core,
`x ≤ᵀ F x` is **false** (`F x ⊥ᵀ x`). Hence:

> For an incomparable `F`, establishing (tree ∧ domination ∧ coding) yields `⊥`. So proving the domination
> bracket (given the tree and coding) is *equivalent to* proving the core itself — the coordinated-tree
> method provides **no genuine reduction** of the incomparable core. The `level_of_cores` / `bnBm_of_cores`
> assemblies are valid implications whose hypotheses are jointly **as hard as the conclusion**.

Concretely: the *uniform* half of domination is outright impossible (`incomparable_jump_not_below`:
`X ≰ᵀ F X ⟹ X′ ≰ᵀ F X`), and the *per-function* half + coding is equivalent to the core. Slaman–Steel's
machinery is **inherently a regressive-case tool** (its engine derives `x ≤ᵀ F x`), and it is *structurally
incapable* of reaching the incomparable core without a genuinely new ingredient.

**Correction of record.** Earlier this session I framed the incomparable core as "reducing to the same
relativized-Slaman–Steel coordinated tree as the regressive case" (the four-face map, `BnBmSkeleton`). That
reduction is *logically valid but circular*: its domination bracket is not an independent, easier sub-problem
— it is the core in disguise. The genuine content is negative and clarifying: **the coordinated-tree method
cannot prove the incomparable core**, so a fundamentally different mechanism (measure-preserving / structural
/ inner-model) is required. This is the honest state.

## 3. The graph confirms it: Borel `F` gives a hyp-preserving `BnBm`

For Borel `F`, `G X = X ⊕ F X ≡_h X` (since `F X ≤ᵀ X^(ρ) ≤_h X`) while `G X >ᵀ X` (incomparability). So the
graph is `≡_h`-preserving and `≤ᵀ`-strictly-increasing — the hyperarithmetic analogue of `BnBm`. The
graph-orbit `Gⁿ X` stays inside the single hyp degree `[X]_h`, where `ω₁ˣ` is **constant**; and each `F`-step
adds `≤ ρ` to the jump level, so along the orbit `F(Gⁿ X) ≤ᵀ (Gⁿ X)^(ρ)` with the **same fixed `ρ`**. This is
`am_graph_not_finite_jump` / `BnBmSkeleton`, one hierarchy up, with the level pinned by the Baire rank.

## 4. Where the genuine difficulty actually is: the ∞-Borel (ordinal-code) case

Theorem A **fails** for `F` that is merely `∞`-Borel with an **ordinal** code `S` (the general case under
AD⁺): then `F X` is `Δ¹₁(S,X)` in the ordinal parameter `S`, *not* `Δ¹₁(X)`, so `F X ≤ᵀ X^(ρ)` fails for any
fixed `ρ`, and indeed `F X` need not be hyp-in-`X` at all. Here — and *only* here — the "level" is genuinely
`S`-relative and unbounded on Turing cones, which is the true form of the rank-unboundedness obstruction.

> **Corrected diagnosis.** Rank-unboundedness (Lutz's Turing obstruction) is an **∞-Borel** phenomenon, not a
> Borel one. Borel `F` ⇒ fixed level `ρ` ⇒ level-`ρ` coordinated tree (transfinite `Bm`). Genuine ∞-Borel `F`
> ⇒ the ordinal code `S` carries `Θ`-level information no cone base captures, and transferring `S` onto a cone
> **is** Steel's conjecture. So the frontier splits: Borel = "prove the fixed-level coordinated tree"; ∞-Borel
> = "transfer the ordinal code `S`" (Steel).

## 5. Status and the two concrete open steps

Not a solve. Developing the structural route rigorously yields:
- **Theorem A** (rigorous): Borel invariant `F` of Baire rank `ρ` has `F X ≤ᵀ X^(ρ)`, `ρ` fixed, on a cone.
- **Clarification** (main new content): the Borel `Am` region has *no* rank-unboundedness — it is a
  transfinite `Bm` at fixed level `ρ`, reducing to a **level-`ρ` coordinated tree** (the transfinite twin of
  the machine-checked `BnBmSkeleton`). Lutz's obstruction is confined to the genuine ∞-Borel case.
- **Two concrete open steps, cleanly separated:**
  1. **Borel:** the *level-`ρ` coordinated tree* (fixed transfinite `ρ`, incomparability branch-field). A
     natural next formalization target — the transfinite generalization of `BnBmSkeleton`, parameterized by
     an ordinal jump level, with the assembly identical (step-3's `x ≤ᵀ F x` contradicts incomparability).
  2. **∞-Borel:** transfer of the ordinal code `S` onto a cone = Steel's conjecture — genuinely
     inner-model-theoretic (Siskind), and provably beyond the Borel case.

This is real progress on the actual open problem: it shows the Borel case is *not* where Lutz's difficulty
lives (contrary to the natural first guess, and to §3 of the ω₁ note as first drafted), and pins the genuine
obstruction to the ordinal-code transfer. The most promising concrete crossing is the **level-`ρ` coordinated
tree for Borel `F`** — where "Borel graph rank `ρ`" gives exactly the fixed level a coordinated tree needs.

## 7. Strategic synthesis: the ONLY viable route is measure-preserving, not coordinated trees

Combining §2.6 with the codebase's engine (this supersedes the "§6 open step 1" optimism):

- **Coordinated trees are ruled out** for the incomparable core (§2.6): a regressive tool whose domination
  bracket is *equivalent to* the core. "Open step 1 (the level-ρ tree)" is therefore not an easier target —
  it is the core in disguise.
- **The measure-preserving engine is different and viable.** `measurePreservingAboveId_of_martinPPT`
  (= Groszek–Slaman, machine-checked) proves `MP ⟹ above-id` *without* coordinated-tree coding — it exploits
  the cofinal value distribution of an MP function on a pointed perfect tree and does **not** derive
  `x ≤ᵀ F x` for the target `F`. So it is *not* circular for the incomparable core.
- Hence the sole open content — `escaping ⟹ MP` (≡ the incomparable core, `escapingMP_iff_incomparable`) —
  must be attacked **measure-theoretically**: show an *escaping* `F` (values `≰ᵀ` every fixed `Z` from below)
  is *measure-preserving* (values `≥ᵀ` every fixed `Z`, i.e. cofinal). Equivalently, the pushforward
  ultrafilter `F_*U` avoids all lower cones ⟹ `F_*U = U`. Graph identity: since `G = id ⊕ F` is above-id so
  `G_*U = U`, and `F = oddPart ∘ G`, we get **`F_*U = (oddPart)_*U`** — so `escaping ⟹ MP` is exactly
  "`(oddPart)_*U` avoids lower cones ⟹ it equals `U`".

> **Bottom line of the whole attack.** The incomparable core is *not* a coordinated-tree problem (that route
> is provably circular). It is a **value-distribution / ultrafilter** problem — `escaping ⟹ MP`: an
> unbounded-below invariant pushforward of the Martin measure is cofinal-above. That is the single crux; it
> uses a genuinely non-regressive engine (Groszek–Slaman for the `MP ⟹ above-id` half); and it is where any
> real proof must land.

## 8. Engine-level localization of `escaping ⟹ MP` (traced through Groszek–Slaman)

Reading the machine-checked `measurePreservingAboveId_of_groszekSlaman`, the `MP ⟹ above-id` engine uses
measure-preservation at exactly two points:
1. `MP ⟹ increasing modulus g` (`measurePreserving_hasModulus`) — the cofinal growth of the values;
2. **`Tr.code ≤ᵀ F x`** on a cone (`hmp Tr.code`) — the values dominate the inverting tree's *fixed* code.

Then modulus-inversion on a branch gives `x = g(h x) ≤ᵀ h x ⊕ Tr.code ≤ᵀ F x`, and invariance transports to
`d ≤ᵀ F d`. So the engine's *only* obstruction to running on an escaping `F` is step 2: it needs
`Tr.code ≤ᵀ F x` (i.e. `F x ≥ᵀ Tr.code`), whereas escaping gives only `F x ≰ᵀ Tr.code`. By cone-dichotomy on
the invariant `{x : Tr.code ≤ᵀ F x}`, exactly one holds on a cone:
- `F x ≥ᵀ Tr.code` (then GS runs → `x ≤ᵀ F x` → contradiction with incomparability → constant); or
- `F x ⊥ᵀ Tr.code` (`Tr.code` is *avoided*) → GS stalls.

**Correction — the two steps do not separate; the engine consumes MP *monolithically*.** Step 1's modulus is
`g X = X ⊕ b(X)` where `b(X)` is the MP-witness base at `Z = X` (`measurePreserving_hasModulus`), so the
modulus already packages the *entire* MP data (a witness for every `Z`), and `Tr.code` is derived from `g`.
So one cannot isolate "MP at the single code `Tr.code`" — the code depends on all of MP. Hence:

> **Honest crux (corrected).** The Groszek–Slaman engine is *entirely downstream of MP*: both the modulus and
> the `Tr.code ≤ᵀ F x` step consume measure-preservation as a whole. So `escaping ⟹ MP` does **not** reduce
> to a single value-vs-code comparison — it is the *monolithic* measure-theoretic gap "escaping values are
> cofinal-above", with no engine-internal shortcut. What the trace *does* establish cleanly: the open content
> is purely a **value-distribution** fact about `F` (are the values cofinal?), with **no** coordinated-tree /
> `x ≤ᵀ F x`-coding content — GS supplies all of that for free once MP is in hand. This correctly separates
> "the hard part" (MP itself, a statement about where `F`'s values land) from "the downstream part" (GS,
> machine-checked). It is the measure-theoretic route, and it is monolithic.
