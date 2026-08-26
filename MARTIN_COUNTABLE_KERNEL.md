# Killing Siskind case (2): the countable-kernel sharpening, and why modern AD ultrafilter theory does not transfer

*Session 2026-08-26. Target: RK-rigidity of the Martin measure `U_M` (= Part 1, Lutz–Siskind Thm 5.15),
reduced to killing **case (2)** of the Siskind trichotomy (Thm 1.5.8): no nonprincipal `V ≤_RK U_M`
concentrates on complements of cones. Brought to bear: Goldberg's Ultrapower Axiom / Ketonen order,
Goldberg–Sargsyan–Siskind iteration-tree analysis, ultrapower comparison, and the Fubini/normality tools.
One genuine machine-checked sharpening; a precise map of why each modern tool stalls.*

## 0. The exact reduction (sourced, verbatim-checked)

- **Thm 5.15 (AD + Uniformization_ℝ):** Part 1 ⟺ every nonprincipal `V ≤_RK U_M` equals `U_M`.
- **Trichotomy (Siskind thesis Thm 1.5.8, AD⁺):** a countably complete ultrafilter `W` on `D_T` is
  principal, or **case (2)** `{x | C̄_x ∈ W} ∈ W`, or `= U_M`.
- **Prop 5.24 (ZF+AD):** if `{x | Cone(x) ∈ V} ∈ V` then `V = U_M` — collapses every *non*-case-(2)
  nonprincipal `V` to `U_M`, via PSP + **Cor 4.5** (perfect ∧ countably-directed ⟹ cofinal, itself from the
  Kolmogorov-complexity coding **Thm 4.3**).

So the whole open content is: **kill case (2) among the RK-predecessors of `U_M`.**

## 1. The modern AD ultrafilter theory does NOT transfer (hard no-go, verified)

- **Goldberg's Ketonen order / UA / Dodd-soundness** (arXiv:2006.03293) is defined **only for ultrafilters
  on a wellordered set** (Def 3.5.10 associates a Ketonen order to a *wellorder*). Under AD, `D_T` is not
  wellorderable, so the Ketonen order, UA-comparison, and the "normal ⟹ irreducible" (Prop 5.3.4) results
  **do not type-check for `U_M`**. This is definitional, not a missing lemma. Goldberg's own open question
  "is every irreducible ultrafilter Dodd-sound?" shows there is no clean *manifest-property* characterization
  of irreducibility even in ZFC to import.
- **UA does hold in `HOD^{L(ℝ)}`** (Woodin), and **GSS (arXiv:2603.20951) Thm 3.9** even represents the
  ultrapower of `HOD` by the Martin measure as an iteration tree on `HOD` — BUT it represents a **single**
  ultrapower map; it has **no comparison/rigidity theory between two distinct ultrafilters**. Its own abstract:
  "the precise structure of the iteration trees ... remains a mystery." So it gives a structural handle on
  `Ult(HOD, U_M)`, not a weapon against a *predecessor*.
- **Ultrapower comparison** `Ult(V) → Ult(U_M)` (the RK factor embedding) is stated but never *exploited*
  against case (2) anywhere in Lutz/Siskind. Siskind's own expectation: resolving case (2) needs "more
  sophisticated Descriptive Set Theory," not inner-model comparison.

## 2. The Fubini/commutativity tool goes the WRONG way

- `U_M` is **not commutative** (Siskind Cor 1.5.7, witness `R(x,y) ⟺ x ∉ C_y`).
- Commutativity is **RK-downward-closed** (Lemma 1.5.6): `U ≤_RK W` and `W` commutative ⟹ `U` commutative.
- This kills things **above** `U_M` (`U_L, U_B` are commutative, so `U_M ⋠_RK U_L, U_B` — Thm 5.22/5.23 via
  the `x↦ω₁ˣ` + Fubini argument). For a **predecessor** `V ≤_RK U_M`, downward-closure propagates
  commutativity *down from the non-commutative top* — **no constraint reaches `V`.** Confirmed dead end.
- The naive commutativity swap on the antichain relation `R(x,z) ⟺ f(z) ⋡_T f(x)` is **satisfied** in both
  directions (an antichain is symmetric) — so the generic antichain is commutativity-*consistent*. This is
  exactly why case (2) is hard, and matches the earlier "countable diagonal gives no contradiction."

## 3. The genuine new result: the kernel of a case-(2) predecessor is COUNTABLE

For `V = F_*U_M` (`F` Turing-invariant, WLOG under Uniformization_ℝ):
`Cone(d) ∈ V ⟺ {X | d ≤_T F X} ∈ U_M ⟺ d ≤_T F X` on a cone `⟺ BelowF F d`.
So the Prop-5.24 set `A_V = {d | Cone(d) ∈ V}` **is exactly the repo kernel** `BelowF F`
(`coneInPushforward_iff_belowF`, `Iff.rfl`).

Prop 5.24's proof shows `A_V` is always countably-directed (countable completeness of `V`), and — the
contrapositive content via PSP + Cor 4.5 — if `A_V` is *uncountable* it is cofinal, forcing `V = U_M`. Hence:

> **FACT COUNT.** For a case-(2) predecessor `V = F_*U_M`, the kernel `BelowF F` is **countable**, hence
> bounded by a **single real** `r_K` (join of a generating sequence, `DC_ℝ`).

This is **strictly sharper** than the repo's `nonMP_kernel_avoids_cone` (which gave only *some* upper-bound
cone). Machine-checked as `case2_kernel_bounded_of_countable` (`CountableKernel.lean`), conditional on the
named classical inputs `Prop524Countable` (the PSP/Cor-4.5 DST, already isolated as `Prop524`) and
`CountableUpperBound` (`DC_ℝ`).

## 4. Why FACT COUNT still does NOT close case (2) (the exact barrier, machine-stated)

The single-real bound `r_K` is a **lower-side** constraint: it bounds *what `F` dominates* (`BelowF F`,
the degrees below the values). The incomparable core needs the **value** `F X` itself constrained. These are
on opposite sides of `F`, and the KNOWN Slaman–Steel machinery proves they cannot be bridged:

- `incomparable_escapes_params` (repo, from the known regressive theorem): an incomparable-to-argument `F`
  has, for **every** real `p`, `¬ (F X ≤_T X ⊕ p` on a cone`)` — the values are *not* `X`-plus-parameter
  computable. In particular (take `p = r_K`) `F X ⊀_T X ⊕ r_K` on every cone
  (`no_regressivity_relative_to_kernel_bound`).
- So the counterexample is pinned: **dominates only `≤_T r_K`** (below) yet its **value is not computable
  from `X ⊕ r_K`** (above), with `F X` sideways. Consistent, not contradictory (`case2_sharpened_profile`).

**Root cause.** FACT COUNT is *intersection-type* (lower/domination) data — exactly what ordinal/measure/
countable-completeness tools can see. Case (2) lives in the *per-`X` value* `{0,1}` fact `F X ⊥_T d`, which no
invariant ordinal function or countable intersection reaches (an invariant ordinal determining the degree
would well-order `D_T`, `ω₁ ↪ ℝ`, AD-forbidden). Same wall as `MeasurePreservingCK`, now reached from the
predecessor/countability direction — a new, independent confirmation of its exact location.

## 5. The single most promising remaining move

The countability sharpening does buy a real structural handle: **the entire domination kernel of a
counterexample lives below one real `r_K`.** The only remaining *live* lead that could exploit this is **Lutz
thesis §5.11**: the (conjectural, expected under AD + V=L(ℝ)) principle "if the `I`-positive-set forcing for
`V` is **proper** (Slaman's variant: does not collapse `𝔠`), then `V` is not RK-below `U_M`." A case-(2)
predecessor with a one-real-bounded kernel is a highly *constrained* ideal, which is precisely the input a
forcing/properness argument wants — and this route is genuinely inner-model-flavored but, crucially, does
**not** go through Goldberg's Ketonen/UA apparatus (which we proved inapplicable). That is the sharpest
concrete direction this session produced; it is where a proof would have to live.

## Machine-checked artifacts (`CountableKernel.lean`, std axioms, build green)
`coneInPushforward_iff_belowF`, `case2_kernel_bounded_of_countable`, `escapes_above_kernel_bound`,
`kernel_bound_gives_no_regressivity`, `no_regressivity_relative_to_kernel_bound`, `case2_sharpened_profile`.

## Honest bottom line
Not solved (50-year open problem; open even for experts under AD⁺). Contributions: (1) a hard verified no-go
— the Goldberg UA/Ketonen/GSS machinery does not transfer to `U_M` (wrong base: not wellordered; single
ultrapower, no comparison); (2) the commutativity tool provably points away from predecessors; (3) a genuine
new machine-checked sharpening (kernel of a case-(2) predecessor is countable / one-real-bounded); (4) the
exact barrier, now visible from the countability side: the value-level `{0,1}` data is orthogonal to every
intersection-type (measure/ordinal) tool; and (5) the one remaining live lead (Lutz §5.11 properness), for
which the one-real kernel bound is a natural input.
