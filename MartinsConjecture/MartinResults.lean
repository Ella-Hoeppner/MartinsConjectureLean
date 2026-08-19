/-
**Capstones**: with Bard's Lemma 3.4 (`uti_computable`) discharging the
computable-uniformity hypothesis, both headline results now hold for *bare*
uniform Turing invariance.

* `partI_uniform` — **Part I of Martin's conjecture for uniformly-invariant
  functions** (Slaman–Steel 1988), and both Part I open cores for that class
  (`regressive_uniform`, `incomparable_uniform`);
* `lachlan_dichotomy_cone_uniform`, `lachlan_no_post_solution_cone_uniform` —
  **Lachlan's theorem for r.e. operators**, for bare uniform invariance.

Everything is conditional only on Turing determinacy (threaded explicitly); no
axioms beyond `propext`, `Classical.choice`, `Quot.sound`. -/
import MartinsConjecture.BardUniformity
import MartinsConjecture.LachlanTheorem
import MartinsConjecture.MeasurePreserving

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- **The Steel kernel holds** (no longer a hypothesis): a non-constant
uniformly-invariant function is above the identity on a cone.  Proof: Bard 3.4
(`uti_computable`) supplies computable uniformity, then `steel_kernel_computable`. -/
theorem steelUniformKernel_holds (hTD : TuringDeterminacy fun _ => True) :
    SteelUniformKernel :=
  fun F hF hnc => steel_kernel_computable hTD (uti_computable hF) hnc

/-- **Part I of Martin's conjecture for uniformly-invariant functions**
(Slaman–Steel 1988): every uniformly-invariant `F` is constant on a cone or above
the identity on a cone. -/
theorem partI_uniform (hTD : TuringDeterminacy fun _ => True) : PartI_Uniform_Borel :=
  partI_uniform_of_steel (steelUniformKernel_holds hTD)

/-- **The regressive Part I core, proved for the uniform class**: a
uniformly-invariant function strictly below the identity on a cone is constant on
a cone. -/
theorem regressive_uniform (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hreg : OnCone (fun X => F X <ₜ X)) : ConstantOnCone F :=
  regressive_uniform_of_steel (steelUniformKernel_holds hTD) F hF hreg

/-- **The incomparable Part I core, proved for the uniform class.** -/
theorem incomparable_uniform (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ConstantOnCone F :=
  incomparable_uniform_of_steel (steelUniformKernel_holds hTD) F hF hinc

/-- **Lachlan's theorem for r.e. operators, bare-uniformity form**: a
*uniformly*-invariant r.e. operator above the identity on a cone satisfies, on a
cone, `Wˣ ≡ᵀ X` or `Wˣ ≡ᵀ X′`.  (Bard 3.4 removes the computable-uniformity
hypothesis of `lachlan_dichotomy_cone`.) -/
theorem lachlan_dichotomy_cone_uniform (e : ℕ)
    (hu : UniformlyTuringInvariant (reReal e)) (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy fun _ => True) :
    MartinEquiv (reReal e) (fun X => X) ∨ MartinEquiv (reReal e) (fun X => Cantor.jump X) :=
  lachlan_dichotomy_cone e (uti_computable hu) habove hTD

/-- **No r.e.-operator solution to Post's problem, bare-uniformity form.** -/
theorem lachlan_no_post_solution_cone_uniform (e : ℕ)
    (hu : UniformlyTuringInvariant (reReal e)) (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy fun _ => True) :
    ¬ OnCone (fun X => X <ₜ reReal e X ∧ reReal e X <ₜ Cantor.jump X) :=
  lachlan_no_post_solution_cone e (uti_computable hu) habove hTD

/-- **The uniform class satisfies the class-specific half of the measure-preserving
decomposition**: a non-constant uniformly-invariant function is measure-preserving.
This is the uniform analogue of the Lutz–Siskind lemma (non-trivial order-preserving
⟹ measure-preserving), obtained here from `steel_kernel_computable` — so the whole of
Part 1 for uniformly-invariant functions factors through `partI_iff_measurePreserving`
as this lemma plus Thm 3.4. -/
theorem uniform_nonconstant_measurePreserving (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : UniformlyTuringInvariant F) (hnc : ¬ ConstantOnCone F) :
    MeasurePreserving F :=
  aboveId_measurePreserving (steel_kernel_computable hTD (uti_computable hF) hnc)

#print axioms partI_uniform
#print axioms regressive_uniform
#print axioms incomparable_uniform
#print axioms lachlan_dichotomy_cone_uniform
#print axioms uniform_nonconstant_measurePreserving

end Martin
