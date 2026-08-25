# The open content of Part 1 of Martin's conjecture: an arithmetic decomposition

*A rigorous exposition of the structural findings formalized in this project
(`RegressiveJumpDecomp.lean`, `IncomparableArithReduction.lean`, `RegressiveSkeleton.lean`).
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
content *is* AnBm. So this is a **classification**, not a reduction-to-something-easier: it identifies an
ad-hoc jump-distance sub-case with a *recognizable* target, the arithmetic-degrees regressive theorem.

## 4. The three-level analogy, and why the arithmetic level is genuinely separate

The regressive question — "is a regressive invariant function constant on a cone?" — makes sense for
each of three reducibilities, giving a natural hierarchy:

| reducibility | regressive theorem | status |
|---|---|---|
| **Turing** `≤ᵀ` | Slaman–Steel 1988 | **theorem** |
| **arithmetic** `≤ₐ` | `StrictArithRegressiveConstant` | **open** (= AnBm) |
| **hyperarithmetic** `≤_h` | Lutz 2024 (`arXiv:2306.05746`) | **theorem** (on `D_h`) |

So the arithmetic level is the *missing middle*. Two independent reasons it does not reduce to its
neighbours:

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

- **BnAm** (`X <ₐ F X`, Turing-incomparable): `F X` is arithmetically strictly above `X`. There is no
  strictly-weaker *named* target: the natural analogue would be an "arithmetic above-identity" theorem,
  which is itself the arithmetic Part 1 for the above case — no more tractable than the sub-case.
- **BnBm** (`F X ≡ₐ X`, Turing-incomparable): the *arithmetic-preserving, Turing-dropping* phenomenon —
  `F` maps `X` to another Turing degree in the same arithmetic degree. This is genuinely `Turing`-specific
  (vacuous on `D_h`, where `F X <_h X` always strictly drops `ω₁^x`), which is precisely why Lutz's
  method never encounters it. No ordinal rank is available (the Turing degrees inside one hyperarithmetic
  degree are ill-founded).
- **AnAm** (arithmetically incomparable): the transfinite residue. Splitting by `ω₁^{F X}` vs `ω₁^X` and
  invoking the project's ordinal-ultrapower engine (`no_omega1_decreasing_conePreserving`, formalized)
  would kill the `ω₁`-decreasing case — *but only under cone-preservation* (`base ≤ᵀ F X` on the cone),
  which an incomparable `F` does not provide. This cone-preservation caveat is the barrier.

## 7. Summary and open questions

The sole open content of Part 1 is now decomposed into four arithmetically-typed pieces, exactly one of
which (AnBm) is a **recognizable open theorem** — the arithmetic-degrees regressive theorem, the missing
middle of the Turing/arithmetic/hyperarithmetic hierarchy. The other three are the genuinely Turing-
specific residue, each with a precise obstruction.

**Concrete open questions this raises:**
1. *Does the arithmetic-degrees regressive theorem hold?* I.e. is a Turing-invariant `F` with
   `F X <ₐ X` on a cone constant on a cone? A proof would carry the Slaman–Steel coordinated-tree +
   domination + coding argument out relative to a finite jump — the obstacle being that the tree and the
   domination must be arranged relative to `X^(k)` while `F` is only Turing-invariant.
2. *Is the arithmetic-preserving Turing-dropping phenomenon (BnBm) possible for a Turing-invariant
   function under determinacy?* Ruling it out is the deepest Turing-specific piece.
3. *Can the ordinal-ultrapower engine be freed of the cone-preservation hypothesis?* This would settle
   the `ω₁`-decreasing part of AnAm.

None of these is a two-line corollary of the tools available; the incomparable core's resistance is
inner-model-theoretic in flavour (cf. Siskind, *Aspects of Martin's Conjecture and Inner Model Theory*),
consistent with its ~50-year-open status. The value here is a **sharp, machine-checked map** of exactly
what a proof of Part 1 must still supply.
