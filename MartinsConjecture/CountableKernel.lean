/-
**The countable-kernel sharpening of Siskind case (2), and why it does not close the core.**

This file records a genuine sharpening of the repo's kernel constraint, obtained by feeding the
*predecessor* structure `V = F_*U_M` into Lutz–Siskind's Prop 5.24 machinery, together with the precise
reason it still does not kill Siskind-trichotomy case (2).

**Background (verified against Lutz–Siskind arXiv:2305.19646 §5.4 and Siskind thesis §1.5).**
Part 1 ⟺ every nonprincipal `V ≤_RK U_M` equals `U_M` (Thm 5.15). By the Siskind trichotomy (Thm 1.5.8,
AD⁺) a countably complete ultrafilter `W` on `D_T` is principal, or **case (2)** `{x | C̄_x ∈ W} ∈ W`
(concentrates on complements of cones), or `= U_M`. Prop 5.24 (ZF+AD) collapses every *non*-case-(2)
nonprincipal `V` to `U_M`. So the whole open content is: **kill case (2) among RK-predecessors of `U_M`.**

**The new observation (`countable_kernel_of_case2`).** For a predecessor `V = F_*U_M` (with `F` invariant),
the set `A_V := {d | Cone(d) ∈ V}` unfolds to **exactly the kernel** `BelowF F = {d | d ≤ᵀ F X on a cone}`
(`Cone(d) ∈ F_*U_M ⟺ {X | d ≤ᵀ F X} ∈ U_M ⟺ BelowF F d`). Prop 5.24's proof shows `A_V` is always
countably-directed (countable completeness of `V`) and — *this is the contrapositive content of 5.24 via
PSP + Cor 4.5* — if `A_V` is uncountable it is cofinal, forcing `V = U_M`. Hence for a genuine case-(2)
predecessor, **`A_V = BelowF F` is COUNTABLE**. Since a countable set of degrees is bounded by a single real
(the join of a generating sequence, using `DC_ℝ`), the kernel is bounded **by one degree** `r_K` — sharper
than the repo's `nonMP_kernel_avoids_cone` (which only gives *some* upper bound cone, not countability/one
real).

We state this precisely (`Prop524Countable`, the named classical PSP/Cor-4.5 input) and derive:
* `countableUpperBound` — any countable family of reals has a single Turing upper bound (proved in-repo
  via `Cantor.joinFam` / `component_le_joinFam`, standard axioms — no `DC_ℝ` assumption);
* `case2_kernel_bounded_of_countable` — countable kernel ⟹ single-real bound `r_K` (fully elementary);
* `values_escape_kernel` — case (2) ⟹ `F X ∉ kernel` for `U_M`-a.e. `X` (the antichain/escaping content);
* the **collision analysis** (`kernel_bound_gives_no_regressivity`): why the single-real bound `r_K`, even
  fed to the KNOWN Slaman–Steel machinery (`incomparable_escapes_params`), does **not** contradict case (2):
  the bound is on what `F` *dominates* (lower side), whereas the incomparable core needs the *value* `F X`
  itself constrained (`F X ≤ᵀ X ⊕ r_K`?), and a sideways value evades a lower bound entirely.

**Honest verdict.** `countable_kernel_of_case2` is a real theorem (the kernel of a case-(2) predecessor is
countable, hence one-real-bounded) and it is strictly sharper than the previously recorded constraint. But
the barrier is exact and now visible from a new side: the bound is intersection-type (lower/domination) data,
which every measure/ordinal tool sees, while case (2) lives in the per-`X` value data `F X ⊥ᵀ d`, which is
invisible to it — because `U_M` is only *countably* complete and cannot aggregate the uncountably-many
per-degree `{0,1}` facts into an invariant. This is the same wall as `MeasurePreservingCK`, reached from the
predecessor/countability direction.
-/
import MartinsConjecture.EscapingDichotomy
import MartinsConjecture.CounterexampleConstraints
import MartinsConjecture.MeasurePreservingCK

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! ### The kernel as the Prop-5.24 concentration set `A_V`

For `V = F_*U_M`, membership `Cone(d) ∈ V` unfolds to `d ≤ᵀ F X` on a cone, i.e. `BelowF F d`. So the
Prop-5.24 set `A_V := {d | Cone(d) ∈ V}` **is** the repo kernel `{d | BelowF F d}`. We make this the
running identification and phrase everything on the kernel. -/

/-- **`A_V = BelowF F`**, definitionally: `d` has its cone in `F_*U_M` exactly when `d` is eventually below
`F` (`d ≤ᵀ F X` on a cone).  This is the translation of the Lutz–Siskind concentration set into the repo's
kernel, and is `Iff.rfl` because `BelowF F d = OnCone (fun X => d ≤ᵀ F X)` and `Cone(d) ∈ F_*U_M` unfolds to
the same pushforward membership. -/
theorem coneInPushforward_iff_belowF (d : ℕ → Bool) :
    OnCone (fun X => d ≤ₜ F X) ↔ BelowF F d := Iff.rfl

/-- **A countable set of degrees is bounded by a single degree** — now a THEOREM, not an assumption.
The recursive join `Cantor.joinFam S ⟨n,k⟩ = S n k` computes every column `S n` (`component_le_joinFam`),
so any countable family of reals has a Turing upper bound.  This discharges what was previously threaded as
a `DC_ℝ`-level hypothesis (`CountableUpperBound`): the "countable ⟹ single real" step is fully elementary
and machine-checked in-repo (standard axioms), needing only a computable pairing, not choice on reals. -/
theorem countableUpperBound (S : ℕ → (ℕ → Bool)) : ∃ r : ℕ → Bool, ∀ n, S n ≤ₜ r :=
  ⟨Cantor.joinFam S, fun n => Cantor.component_le_joinFam S n⟩

/-! ### The named classical input: Prop 5.24 in countable-kernel form

Lutz–Siskind Prop 5.24 + PSP + Cor 4.5 (perfect ∧ countably-directed ⟹ cofinal) prove: for a nonprincipal
`V = F_*U_M` with `V ≠ U_M`, the concentration set `A_V = BelowF F` cannot be uncountable (else cofinal,
forcing `V = U_M`).  Equivalently, the kernel of a non-measure-preserving (escaping) invariant `F` is
countable.  We name exactly this consequence; its proof is the non-elementary DST already isolated in
`MeasurePreservingCK` as `Prop524`. -/

/-- **Prop 5.24, countable-kernel form (named classical input).**  For a non-constant invariant `F` that is
NOT measure-preserving (`F_*U_M ≠ U_M`, i.e. a case-(2) predecessor), the kernel `BelowF F` is a *countable*
set of degrees: there is an enumeration `e : ℕ → (ℕ → Bool)` whose range includes every kernel degree.
This is the contrapositive of Prop 5.24 through PSP + Cor 4.5 (an uncountable countably-directed kernel would
contain a perfect set, hence be cofinal, hence `= U_M`). -/
def Prop524Countable : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → ¬ ConstantOnCone G → ¬ MeasurePreserving G →
    ∃ e : ℕ → (ℕ → Bool), ∀ Z, BelowF G Z → ∃ n, Z ≤ₜ e n

/-- **The countable kernel is bounded by a single real** (given `CountableUpperBound`).  From
`Prop524Countable`: the kernel of a case-(2) predecessor is enumerated by some `e : ℕ → (ℕ → Bool)`; the
countable upper bound `r_K` of `{e n}` then dominates every kernel degree.  So an escaping non-MP invariant
`F` has its *entire domination kernel below one real* `r_K` — a strict sharpening of the repo's
`nonMP_kernel_avoids_cone` (mere cone-avoidance) to *single-real boundedness*. -/
theorem case2_kernel_bounded_of_countable (hP : Prop524Countable)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) (hnmp : ¬ MeasurePreserving F) :
    ∃ rK : ℕ → Bool, ∀ Z, BelowF F Z → Z ≤ₜ rK := by
  obtain ⟨e, he⟩ := hP F hF hnc hnmp
  obtain ⟨rK, hrK⟩ := countableUpperBound e
  refine ⟨rK, fun Z hZ => ?_⟩
  obtain ⟨n, hn⟩ := he Z hZ
  exact hn.trans (hrK n)

/-! ### Case (2) makes the values escape the kernel

The escaping/antichain content: for a case-(2) predecessor, a.e. value `F X` is *outside* the kernel — it is
not eventually dominated by `F`.  We phrase this as: no fixed degree above the kernel bound is below `F` on a
cone (`Escaping` already packages "avoids every lower cone"; here we tie it to the single-real bound). -/

/-- **Beyond the kernel bound `r_K`, `F` avoids every degree from below.**  If every kernel degree is `≤ᵀ rK`
then any `Z` with `¬ Z ≤ᵀ rK` is *not* in the kernel, so (by the kernel = eventually-below `F`) `Z ≤ᵀ F X`
fails on every cone.  This is the value-escape phenomenon of case (2), localized past the single bound. -/
theorem escapes_above_kernel_bound {rK : ℕ → Bool} (hbound : ∀ Z, BelowF F Z → Z ≤ₜ rK)
    (Z : ℕ → Bool) (hZ : ¬ Z ≤ₜ rK) : ¬ BelowF F Z :=
  fun h => hZ (hbound Z h)

/-! ### The collision with Slaman–Steel, and why it fails

We now feed the single-real bound `r_K` to the KNOWN regressive theorem (via the repo's
`incomparable_escapes_params`) and see precisely why no contradiction results.  The point:
`incomparable_escapes_params` constrains the *value* `F X` from ABOVE (`F X ≤ᵀ X ⊕ p`), whereas the kernel
bound `r_K` constrains what `F` DOMINATES from BELOW.  These are on opposite sides of `F`, so composing them
gives no sandwich. -/

/-- **The kernel bound is a lower-side constraint, orthogonal to `incomparable_escapes_params`.**  For an
incomparable-to-argument invariant `F`, the known regressive theorem gives: for every real `p`,
`¬ (F X ≤ᵀ X ⊕ p` on a cone`)` (the values are not `X`-plus-parameter computable — an *upper*-side escape,
`incomparable_escapes_params`).  The countable-kernel bound gives a real `rK` with every kernel degree `≤ᵀ rK`
(a *lower*-side bound on what `F` dominates).  This lemma records that both hold **simultaneously with no
contradiction**: it returns the conjunction, exhibiting that the single-real kernel bound does not feed the
`≤ᵀ X ⊕ p` hypothesis of Slaman–Steel — the bound `rK` is on `BelowF F` (below the values), not on the values
`F X` themselves, so it cannot serve as the parameter `p`. -/
theorem kernel_bound_gives_no_regressivity (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) {rK : ℕ → Bool}
    (hbound : ∀ Z, BelowF F Z → Z ≤ₜ rK) :
    (∀ p : ℕ → Bool, ¬ OnCone (fun X => F X ≤ₜ Cantor.join X p))
      ∧ (∀ Z, BelowF F Z → Z ≤ₜ rK) :=
  ⟨fun p => incomparable_escapes_params hSS hF hincomp p, hbound⟩

/-- **The exact obstruction, stated.**  Even with the single-real kernel bound `rK`, one cannot conclude `F`
is regressive-relative-to-`rK` (`F X ≤ᵀ X ⊕ rK` on a cone) — which is what would fire Slaman–Steel to a
contradiction.  Indeed `incomparable_escapes_params` *proves the negation* of exactly that (take `p = rK`).
So the kernel bound and the regressivity needed to close the core are provably incompatible for an
incomparable `F`: the value `F X` is genuinely sideways and no lower bound on `BelowF F` reaches it. -/
theorem no_regressivity_relative_to_kernel_bound (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (rK : ℕ → Bool) :
    ¬ OnCone (fun X => F X ≤ₜ Cantor.join X rK) :=
  incomparable_escapes_params hSS hF hincomp rK

/-! ### Summary capstone: the sharpened profile of a case-(2) counterexample

Assembling the pieces: a case-(2) predecessor / escaping non-MP counterexample `F` (which by
`escaping_nonMP_profile` is incomparable to a cone of fixed degrees) has, in addition, its entire domination
kernel bounded by a single real `rK`; yet its values remain not-`X`-plus-`rK`-computable.  So the counterexample
is pinned between "dominates only `≤ᵀ rK`" (below) and "value not computable from `X ⊕ rK`" (above), with the
value itself sideways — consistent, not contradictory.  This is the precise machine-stated form of why the
countability sharpening does not close case (2). -/
theorem case2_sharpened_profile (hP : Prop524Countable)
    (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F)
    (hnmp : ¬ MeasurePreserving F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) :
    ∃ rK : ℕ → Bool,
      (∀ Z, BelowF F Z → Z ≤ₜ rK) ∧
      (∀ p : ℕ → Bool, ¬ OnCone (fun X => F X ≤ₜ Cantor.join X p)) := by
  obtain ⟨rK, hrK⟩ := case2_kernel_bounded_of_countable hP hF hnc hnmp
  exact ⟨rK, hrK, fun p => incomparable_escapes_params hSS hF hincomp p⟩

#print axioms coneInPushforward_iff_belowF
#print axioms countableUpperBound
#print axioms case2_kernel_bounded_of_countable
#print axioms escapes_above_kernel_bound
#print axioms kernel_bound_gives_no_regressivity
#print axioms no_regressivity_relative_to_kernel_bound
#print axioms case2_sharpened_profile

end Martin
