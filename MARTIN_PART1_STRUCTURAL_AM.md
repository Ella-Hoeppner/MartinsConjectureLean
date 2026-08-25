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
