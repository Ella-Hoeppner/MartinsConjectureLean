/-
The order-preserving analysis: measure preservation and the Lutz–Siskind
skeleton.

`MeasurePreserving` is Lutz's Def 1.37: for every `Z`, `F`'s values are above
`Z` on a cone.  For *order-preserving* `F` the upward closure of value-cones
makes half the analysis elementary:

* `orderPreserving_measurePreserving_or_avoids` — **without any determinacy**:
  an order-preserving function is either measure preserving, or its range
  avoids a cone entirely;
* with determinacy, an order-preserving function is measure preserving,
  bounded on a cone (hence constant on a cone), or *escaping while avoiding
  a cone* (`orderPreserving_trichotomy`) — the last case being precisely the
  residual configuration that Lutz–Siskind's hard lemma rules out;
* `partI_orderPreserving_of_lemmas` — the **formal Lutz–Siskind skeleton**:
  their theorem (Part I for order-preserving functions) follows from the two
  main lemmas of their paper, here taken as named hypotheses
  (`MeasurePreservingAboveId`, `AvoidingImpliesConstant`).

Everything here is sorry-free; the two named hypotheses delimit exactly what
remains to formalize of the Lutz–Siskind proof.
-/
import MartinsConjecture.BoundedCase

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- `F` is **measure preserving** [Lutz, Def 1.37]: for every `Z`, the values
of `F` are above `Z` on a cone. -/
def MeasurePreserving (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ Z : ℕ → Bool, OnCone fun X => Z ≤ₜ F X

/-- For order-preserving `F`, a value-cone `{X | Z ≤ₜ F X}` that is inhabited
contains a cone — upward closure, no determinacy. -/
theorem orderPreserving_onCone_of_exists (hop : OrderPreserving F)
    {Z X₀ : ℕ → Bool} (h : Z ≤ₜ F X₀) : OnCone fun X => Z ≤ₜ F X :=
  ⟨X₀, fun X hX => h.trans (hop X₀ X hX)⟩

/-- **The elementary dichotomy for order-preserving functions** (no
determinacy): either `F` is measure preserving, or the range of `F` avoids
the cone above some `Z₀`. -/
theorem orderPreserving_measurePreserving_or_avoids (hop : OrderPreserving F) :
    MeasurePreserving F ∨ ∃ Z₀ : ℕ → Bool, ∀ X, ¬ Z₀ ≤ₜ F X := by
  by_cases hcof : ∀ Z : ℕ → Bool, ∃ X, Z ≤ₜ F X
  · left
    intro Z
    obtain ⟨X₀, hX₀⟩ := hcof Z
    exact orderPreserving_onCone_of_exists hop hX₀
  · right
    push_neg at hcof
    exact hcof

/-- **Cofinal range ⟹ measure-preserving** (order-preserving `F`, no determinacy).  The elementary
half of Lutz–Siskind's Theorem 4.6 Case 2: if the range of an order-preserving `F` is cofinal in the
Turing degrees (every `Z` is `≤ᵀ` some value), then `F` is measure-preserving — each value-cone is
upward-closed by order-preservation.  So the entire content of Case 2 is the *coding* step producing
cofinality from an uncountable range; this discharges the rest. -/
theorem orderPreserving_mp_of_rangeCofinal (hop : OrderPreserving F)
    (hcof : ∀ Z : ℕ → Bool, ∃ X, Z ≤ₜ F X) : MeasurePreserving F := by
  intro Z
  obtain ⟨X₀, hX₀⟩ := hcof Z
  exact orderPreserving_onCone_of_exists hop hX₀

/-- **Trichotomy for order-preserving functions** (with determinacy): `F` is
measure preserving, or constant on a cone, or — the residual open-to-us
configuration — escaping while avoiding a cone. -/
theorem orderPreserving_trichotomy (hTD : TuringDeterminacy fun _ => True)
    (hop : OrderPreserving F) :
    MeasurePreserving F ∨ ConstantOnCone F ∨
    ((∀ Z, OnCone fun X => ¬ F X ≤ₜ Z) ∧ ∃ Z₀, ∀ X, ¬ Z₀ ≤ₜ F X) := by
  rcases orderPreserving_measurePreserving_or_avoids hop with h | h
  · exact Or.inl h
  · by_cases hnc : ConstantOnCone F
    · exact Or.inr (Or.inl hnc)
    · exact Or.inr (Or.inr
        ⟨counterexample_escapes hTD hop.turingInvariant hnc, h⟩)

/-- Named hypothesis: Lutz–Siskind's main lemma (their Thm 1.39, ZF+AD+DC_ℝ;
Borel version in ZFC): a Turing-invariant measure-preserving function is
above the identity on a cone. -/
def MeasurePreservingAboveId : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → MeasurePreserving F →
    AboveIdOnCone F

/-- Named hypothesis: the companion lemma — an order-preserving function
whose range avoids a cone is constant on a cone. -/
def AvoidingImpliesConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F →
    (∃ Z₀, ∀ X, ¬ Z₀ ≤ₜ F X) → ConstantOnCone F

/-- **The formal Lutz–Siskind skeleton**: Part I of Martin's conjecture for
order-preserving functions follows from the two main lemmas of
Lutz–Siskind's proof. -/
theorem partI_orderPreserving_of_lemmas
    (h1 : MeasurePreservingAboveId) (h2 : AvoidingImpliesConstant) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F →
      ConstantOnCone F ∨ AboveIdOnCone F := by
  intro F hop
  rcases orderPreserving_measurePreserving_or_avoids hop with h | h
  · exact Or.inr (h1 F hop.turingInvariant h)
  · exact Or.inl (h2 F hop h)

/-- **The counterexample profile**: under Turing determinacy, any
Turing-invariant counterexample to Part I of Martin's conjecture must, on a
cone, be strictly regressive or pointwise incomparable with the identity,
and its values must escape every fixed degree on a cone.  (Combined with the
classical results: it must also fail to be uniformly invariant [Steel;
Slaman–Steel] and fail to be order preserving [Lutz–Siskind] — which is
exactly why no candidate has ever been found.) -/
theorem counterexample_profile (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F)
    (hno : ¬ (ConstantOnCone F ∨ AboveIdOnCone F)) :
    (OnCone (fun X => F X <ₜ X) ∨ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) ∧
    (∀ Z, OnCone fun X => ¬ F X ≤ₜ Z) := by
  have hnc : ¬ ConstantOnCone F := fun h => hno (Or.inl h)
  have hna : ¬ AboveIdOnCone F := fun h => hno (Or.inr h)
  constructor
  · rcases comparability_on_cone hTD hF with h | h | h | h
    · exact absurd (onCone_mono (fun X hX => hX.2) h) hna
    · exact absurd (onCone_mono (fun X hX => hX.1) h) hna
    · exact Or.inl h
    · exact Or.inr h
  · exact counterexample_escapes hTD hF hnc

#print axioms orderPreserving_measurePreserving_or_avoids
#print axioms orderPreserving_trichotomy
#print axioms partI_orderPreserving_of_lemmas
#print axioms counterexample_profile

end Martin
