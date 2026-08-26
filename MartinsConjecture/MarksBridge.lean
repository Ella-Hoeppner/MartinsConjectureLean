/-
**Proposition 5.37 (Lutz thesis): Marks's conjecture gives the strict half of RK-rigidity.**

Lutz–Siskind reduce the strict half of Part 1's open core (`U_M` is RK-minimal — no nonprincipal
`V` strictly `≤_RK U_M`) to **Marks's conjecture**:

> (Marks) every function `f : 2^ω → 2^ω` is either *constant on a pointed perfect tree* or
> *injective on a pointed perfect tree*.

This file formalizes that reduction against the repo's existing strict-half machinery
(`MartinStrictHalf.lean` / `MeasurePreservingCK.lean`).  For an invariant `F`:

* the **constant** alternative makes `F` constant on the cone the tree realizes (`ConstantOnCone F`
  — the pushforward `F_*U_M` is principal); while
* the **injective** alternative makes `F` injective on that cone, hence dominated-invertible
  (`dominatedInvertible_of_injectiveOnCone`), hence `StrictHalfFor F` (`U_M ≤_RK F_*U_M`) — so the
  pushforward is *not* strictly below `U_M`.

The bridge is `PPT.realizes`: a pointed perfect tree realizes every degree above its code, so the
constancy / injectivity of `F` on the *branches* transports to the *cone*.  The Marks conjecture
itself (that such a tree always exists) is the honest open input — kept as the hypothesis
`MarksTree F` / `MarksConjecture` and never assumed proved.  The open difficulty is exactly making
the tree **pointed** for a non-uniform `F` (Lutz Lemma 2.7's tree-thinning needs `f` to be a Turing
functional, which the incomparable core is not — the `ℕ`-range wall of `uniformization-engine-wall`).
-/
import MartinsConjecture.MartinStrictHalf
import MartinsConjecture.MartinTree

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A Marks tree for `F`**: a pointed perfect tree on whose branch-degrees `F` is either constant
(`F x ≡ᵀ F y` for all branches) or injective (`F x ≡ᵀ F y → x ≡ᵀ y`).  This is the conclusion of
Marks's conjecture applied to the invariant function inducing `F`. -/
def MarksTree (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ T : PPT,
    (∀ x y, T.mem x → T.mem y → F x ≡ₜ F y) ∨
    (∀ x y, T.mem x → T.mem y → F x ≡ₜ F y → x ≡ₜ y)

/-- **Prop 5.37, core dichotomy.**  A Marks tree for an invariant `F` forces `F` to be constant on a
cone or dominated-invertible.  (The tree realizes a cone above its code; constancy / injectivity on
branches transports to that cone by invariance.) -/
theorem constantOrDominatedInvertible_of_marksTree
    (hF : TuringInvariant F) (hMarks : MarksTree F) :
    ConstantOnCone F ∨ DominatedInvertible F := by
  obtain ⟨T, hconst | hinj⟩ := hMarks
  · -- Constant on the branches ⟹ constant on the cone above `T.code`.
    left
    obtain ⟨x0, hx0mem, _⟩ := T.realizes T.code (Cantor.le.refl T.code)
    refine ⟨F x0, T.code, fun X hX => ?_⟩
    obtain ⟨x, hxmem, hxX⟩ := T.realizes X hX
    exact (hF X x hxX.symm).trans (hconst x x0 hxmem hx0mem)
  · -- Injective on the branches ⟹ injective on the cone ⟹ dominated-invertible.
    right
    refine dominatedInvertible_of_injectiveOnCone hF (base := T.code) ?_
    intro X Y hX hY hFXY
    obtain ⟨x, hxmem, hxX⟩ := T.realizes X hX
    obtain ⟨y, hymem, hyY⟩ := T.realizes Y hY
    have hxy : x ≡ₜ y :=
      hinj x y hxmem hymem ((hF x X hxX).trans (hFXY.trans (hF y Y hyY).symm))
    exact hxX.symm.trans (hxy.trans hyY)

/-- **Prop 5.37, packaged with the strict half.**  A Marks tree for an invariant `F` gives
`ConstantOnCone F ∨ StrictHalfFor F` — i.e. the pushforward `F_*U_M` is principal or is *not* strictly
below `U_M`.  This is exactly the injective case of Lutz Prop 5.37, machine-checked. -/
theorem constantOrStrictHalf_of_marksTree (hM : MartinPPT)
    (hF : TuringInvariant F) (hMarks : MarksTree F) :
    ConstantOnCone F ∨ StrictHalfFor F :=
  (constantOrDominatedInvertible_of_marksTree hF hMarks).imp id
    (fun hdi => (strictHalf_iff_dominatedInvertible hM hF).mpr hdi)

/-- **Marks's conjecture** (the honest open input): every invariant function has a Marks tree. -/
def MarksConjecture : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → MarksTree F

/-- **The strict half of RK-rigidity, from Marks's conjecture** (Lutz Prop 5.37).  If Marks's
conjecture holds then every non-constant invariant `F` satisfies the strict half `StrictHalfFor F`
(`U_M ≤_RK F_*U_M`); equivalently `U_M` has no nonprincipal strict `≤_RK`-predecessor. -/
theorem strictHalf_of_marksConjecture (hM : MartinPPT) (hMarks : MarksConjecture)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) : StrictHalfFor F :=
  (constantOrStrictHalf_of_marksTree hM hF (hMarks F hF)).resolve_left hnc

#print axioms constantOrDominatedInvertible_of_marksTree
#print axioms constantOrStrictHalf_of_marksTree
#print axioms strictHalf_of_marksConjecture

end Martin
