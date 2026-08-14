/-
**The two Part I open cores collapse to one kernel for uniformly-invariant
functions.**

`Reduction.lean` reduces Part I of Martin's conjecture to two open cores — the
*regressive* case (`RegressiveImpliesConstant`) and the *incomparable* case
(`IncomparableImpliesConstant`).  Both are stated for arbitrary Turing-invariant
`F` and are open in general, but *known* for uniformly-invariant functions
(Slaman–Steel 1988).

This file isolates exactly what "known for uniformly invariant" needs: a single
kernel `SteelUniformKernel` — *a uniformly-invariant function that is not constant
on a cone lies above the identity on a cone*.  We prove, sorry-free:

* `regressive_uniform_of_steel`, `incomparable_uniform_of_steel` — **both cores,
  for the uniform class, follow from the kernel**;
* `partI_uniform_of_steel` — the kernel gives Part I (`PartI_Uniform_Borel`);
* `steelUniformKernel_iff_cores` — and conversely the kernel is *equivalent* to
  the two uniform cores together (via the comparability trichotomy + Turing
  determinacy).

So the entire Slaman–Steel Part I for uniformly-invariant functions is exactly
the one statement `SteelUniformKernel`.  That kernel is the recursion-theoretic /
pressing-down content (normality of the Martin measure); it is threaded here as a
named hypothesis rather than assumed proved — the honest boundary of what the
current infrastructure delivers.
-/
import MartinsConjecture.Reduction

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- **The Slaman–Steel kernel** for Part I (uniform class): a uniformly-invariant
function that is *not* constant on a cone lies *above the identity* on a cone.
Equivalently (contrapositive), a uniformly-invariant function that is not above
the identity on a cone is constant on a cone — Part I of Martin's conjecture for
the uniform class.  This packages the recursion-theoretic content (Slaman–Steel
1988: a pressing-down argument on the Martin measure). -/
def SteelUniformKernel : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, UniformlyTuringInvariant F →
    ¬ ConstantOnCone F → AboveIdOnCone F

/-- **The regressive core for uniformly-invariant functions**, from the kernel:
if a uniformly-invariant `F` is strictly below the identity on a cone, it is
constant on a cone.  (If it were not constant, the kernel would force it above
the identity — impossible below it.) -/
theorem regressive_uniform_of_steel (hker : SteelUniformKernel)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hreg : OnCone (fun X => F X <ₜ X)) : ConstantOnCone F := by
  by_contra hnc
  obtain ⟨B1, hB1⟩ := hreg
  obtain ⟨B2, hB2⟩ := hker F hF hnc
  have h1 : F (Cantor.join B1 B2) <ₜ Cantor.join B1 B2 :=
    hB1 _ (Cantor.left_le_join B1 B2)
  have h2 : Cantor.join B1 B2 ≤ₜ F (Cantor.join B1 B2) :=
    hB2 _ (Cantor.right_le_join B1 B2)
  exact h1.2 h2

/-- **The incomparable core for uniformly-invariant functions**, from the kernel:
if a uniformly-invariant `F` is pointwise incomparable with the identity on a
cone, it is constant on a cone. -/
theorem incomparable_uniform_of_steel (hker : SteelUniformKernel)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ConstantOnCone F := by
  by_contra hnc
  obtain ⟨B1, hB1⟩ := hinc
  obtain ⟨B2, hB2⟩ := hker F hF hnc
  have h1 : ¬ F (Cantor.join B1 B2) ≤ₜ Cantor.join B1 B2 ∧
      ¬ Cantor.join B1 B2 ≤ₜ F (Cantor.join B1 B2) :=
    hB1 _ (Cantor.left_le_join B1 B2)
  have h2 : Cantor.join B1 B2 ≤ₜ F (Cantor.join B1 B2) :=
    hB2 _ (Cantor.right_le_join B1 B2)
  exact h1.2 h2

/-- **Part I for uniformly-invariant functions**, from the kernel: every
uniformly-invariant function is constant on a cone or above the identity on a
cone. -/
theorem partI_uniform_of_steel (hker : SteelUniformKernel) :
    PartI_Uniform_Borel := by
  intro F _ hF
  by_cases hc : ConstantOnCone F
  · exact Or.inl hc
  · exact Or.inr (hker F hF hc)

/-- **Conversely, the kernel follows from the two uniform cores** (under Turing
determinacy, via the comparability trichotomy): a non-constant uniformly-invariant
function cannot be regressive or incomparable (both force constancy by the cores),
so by trichotomy it is equivalent to or strictly above the identity — either way,
above it. -/
theorem steel_of_uniform_cores (hTD : TuringDeterminacy fun _ => True)
    (hreg : ∀ F, UniformlyTuringInvariant F →
      OnCone (fun X => F X <ₜ X) → ConstantOnCone F)
    (hinc : ∀ F, UniformlyTuringInvariant F →
      OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) → ConstantOnCone F) :
    SteelUniformKernel := by
  intro F hF hnc
  rcases comparability_on_cone hTD hF.turingInvariant with h | h | h | h
  · obtain ⟨B, hB⟩ := h
    exact ⟨B, fun X hX => (hB X hX).2⟩
  · obtain ⟨B, hB⟩ := h
    exact ⟨B, fun X hX => (hB X hX).1⟩
  · exact absurd (hreg F hF h) hnc
  · exact absurd (hinc F hF h) hnc

/-- **The Slaman–Steel Part I content is exactly one kernel.**  For uniformly-
invariant functions, the two Part I open cores together are *equivalent* to the
single statement "non-constant ⟹ above the identity".  This pinpoints the precise
recursion-theoretic obligation behind Part I for the uniform class. -/
theorem steelUniformKernel_iff_cores (hTD : TuringDeterminacy fun _ => True) :
    SteelUniformKernel ↔
      ((∀ F, UniformlyTuringInvariant F →
          OnCone (fun X => F X <ₜ X) → ConstantOnCone F)
       ∧ (∀ F, UniformlyTuringInvariant F →
          OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) → ConstantOnCone F)) := by
  constructor
  · intro hker
    exact ⟨fun F hF => regressive_uniform_of_steel hker F hF,
      fun F hF => incomparable_uniform_of_steel hker F hF⟩
  · rintro ⟨hreg, hinc⟩
    exact steel_of_uniform_cores hTD hreg hinc

#print axioms regressive_uniform_of_steel
#print axioms incomparable_uniform_of_steel
#print axioms partI_uniform_of_steel
#print axioms steelUniformKernel_iff_cores

end Martin
