/-
**Isolating the open content of the regressive / incomparable cores.**

Part 1 of Martin's conjecture is fully proved in this project for *uniformly*
Turing-invariant functions (`partI_uniform`, and the two cores
`regressive_uniform`, `incomparable_uniform`).  For *arbitrary* Turing-invariant
functions the regressive and incomparable cores are open on the Turing degrees.

The literature's strategy (Slaman–Steel; Lutz, *Martin's conjecture for
regressive functions*, JML 2024) is a **reduction to the uniform case**: show
that a regressive invariant function is, on a cone, Martin-equivalent to a
*uniformly* invariant one, and then invoke the uniform theorem.  Lutz carries out
the reduction on the **hyperarithmetic** degrees using an ordinal jump hierarchy;
on the Turing degrees the reduction is exactly the open point.

This file *pins that open point down*: it proves that the reduction hypothesis —
"every regressive (resp. incomparable) invariant function is Martin-equivalent to
a uniformly-invariant one" — **suffices** to close the corresponding core,
discharging the entire remaining argument through the uniform results already
formalized here.  The transfer lemmas (`constantOnCone_of_martinEquiv`,
`regressive_of_martinEquiv`, `incomparable_of_martinEquiv`) show the two class
properties are Martin-equivalence invariants, so the reduction genuinely only has
to produce *a* uniform representative of the degree.
-/
import MartinsConjecture.MartinResults

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F G : (ℕ → Bool) → ℕ → Bool}

/-! ### Martin-equivalence invariance of the class properties -/

/-- Being constant on a cone is a **Martin-equivalence invariant**: if `F ≡ₘ G`
and `G` is constant on a cone, so is `F` (same constant). -/
theorem constantOnCone_of_martinEquiv (hFG : MartinEquiv F G) (hG : ConstantOnCone G) :
    ConstantOnCone F := by
  obtain ⟨C, hGC⟩ := hG
  exact ⟨C, hFG.trans hGC⟩

/-- Being **regressive** (strictly below the identity) on a cone is a
Martin-equivalence invariant. -/
theorem regressive_of_martinEquiv (hFG : MartinEquiv F G)
    (hreg : OnCone (fun X => F X <ₜ X)) : OnCone (fun X => G X <ₜ X) := by
  refine onCone_mono ?_ (onCone_and hFG hreg)
  rintro X ⟨hequiv, hlt⟩
  refine ⟨hequiv.2.trans hlt.1, fun hXG => hlt.2 (hXG.trans hequiv.2)⟩

/-- Being **incomparable** with the identity on a cone is a Martin-equivalence
invariant. -/
theorem incomparable_of_martinEquiv (hFG : MartinEquiv F G)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) :
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) := by
  refine onCone_mono ?_ (onCone_and hFG hinc)
  rintro X ⟨hequiv, hnle, hnge⟩
  exact ⟨fun hGX => hnle (hequiv.1.trans hGX), fun hXG => hnge (hXG.trans hequiv.2)⟩

/-! ### The reduction: uniformization suffices -/

/-- **Single-witness reduction, regressive case.**  If a regressive invariant `F`
is Martin-equivalent to *some* uniformly-invariant `G`, then `F` is constant on a
cone.  The whole argument after producing `G` is discharged by `regressive_uniform`. -/
theorem regressive_constant_of_uniform_witness (hTD : TuringDeterminacy fun _ => True)
    (hreg : OnCone (fun X => F X <ₜ X))
    (hGu : UniformlyTuringInvariant G) (hFG : MartinEquiv F G) : ConstantOnCone F :=
  constantOnCone_of_martinEquiv hFG
    (regressive_uniform hTD G hGu (regressive_of_martinEquiv hFG hreg))

/-- **Single-witness reduction, incomparable case.** -/
theorem incomparable_constant_of_uniform_witness (hTD : TuringDeterminacy fun _ => True)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X))
    (hGu : UniformlyTuringInvariant G) (hFG : MartinEquiv F G) : ConstantOnCone F :=
  constantOnCone_of_martinEquiv hFG
    (incomparable_uniform hTD G hGu (incomparable_of_martinEquiv hFG hinc))

/-- **The regressive core, reduced to uniformization.**  If every regressive
invariant function is Martin-equivalent to a uniformly-invariant one (Lutz's
reduction, open on the Turing degrees), then the regressive core of Part 1 holds
in full: every regressive invariant function is constant on a cone.  This isolates
the *entire* open content in the single hypothesis `huniformize`. -/
theorem regressive_core_of_uniformization (hTD : TuringDeterminacy fun _ => True)
    (huniformize : ∀ F, TuringInvariant F → OnCone (fun X => F X <ₜ X) →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    ∀ F, TuringInvariant F → OnCone (fun X => F X <ₜ X) → ConstantOnCone F := by
  intro F hF hreg
  obtain ⟨G, hGu, hFG⟩ := huniformize F hF hreg
  exact regressive_constant_of_uniform_witness hTD hreg hGu hFG

/-- **The incomparable core, reduced to uniformization.** -/
theorem incomparable_core_of_uniformization (hTD : TuringDeterminacy fun _ => True)
    (huniformize : ∀ F, TuringInvariant F → OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    ∀ F, TuringInvariant F → OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) → ConstantOnCone F := by
  intro F hF hinc
  obtain ⟨G, hGu, hFG⟩ := huniformize F hF hinc
  exact incomparable_constant_of_uniform_witness hTD hinc hGu hFG

/-! ### Capstone: full Part 1 from uniformization on a cone -/

/-- **Part 1 of Martin's conjecture from the two-core uniformization hypotheses.**
If every regressive invariant function *and* every incomparable invariant function
is, on a cone, Martin-equivalent to a uniformly-invariant one, then Part 1 holds
for all Turing-invariant functions.  (The above-identity and comparable cases are
already handled by `partI_of_cores`; only the two cores need uniformizing.) -/
theorem partI_of_core_uniformization (hTD : TuringDeterminacy fun _ => True)
    (huniR : ∀ F, TuringInvariant F → OnCone (fun X => F X <ₜ X) →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G)
    (huniI : ∀ F, TuringInvariant F → OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_cores hTD
    (regressive_core_of_uniformization hTD huniR)
    (incomparable_core_of_uniformization hTD huniI)

/-- **Part 1 of Martin's conjecture from uniformization on a cone.**  This is the
sharpest packaging: *the entire remaining content of Part 1 is that every
Turing-invariant function is, on a cone, Martin-equivalent to a uniformly-invariant
one.*  Everything else — the Slaman–Steel / Bard theory for the uniform class
(`partI_uniform`, `regressive_uniform`, `incomparable_uniform`), the cone theorem,
and the reduction of Part 1 to its two cores — is already formalized in this
project and discharged here.  Producing the uniform representative on a cone is
exactly the step Lutz carries out on the *hyperarithmetic* degrees (via ordinal
jump hierarchies) and which is open on the Turing degrees. -/
theorem partI_of_uniformization (hTD : TuringDeterminacy fun _ => True)
    (huni : ∀ F, TuringInvariant F → ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_core_uniformization hTD
    (fun F hF _ => huni F hF) (fun F hF _ => huni F hF)

#print axioms regressive_core_of_uniformization
#print axioms incomparable_core_of_uniformization
#print axioms partI_of_uniformization

end Martin
