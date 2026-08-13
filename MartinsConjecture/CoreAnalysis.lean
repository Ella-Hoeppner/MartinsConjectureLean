/-
Exact analysis of the Part I cores.

Two sharpenings of the reduction in `Reduction.lean`:

* **The incomparable core is an impossibility statement**
  (`incomparable_core_iff_never`): its hypothesis and conclusion are jointly
  contradictory — if `F ≡ₜ C` on a cone *and* `F ⊥ id` on a cone, the point
  `join C B` above both bases satisfies `F (join C B) ≡ₜ C ≤ₜ join C B`,
  contradicting incomparability.  Hence the core asserts precisely that the
  fourth comparability regime never occurs for invariant functions.

* **The reduction is exact** (`partI_iff_cores`): under Turing determinacy,
  the (AD-style, all-invariant-functions) Part I statement is *equivalent*
  to the conjunction of the two cores — nothing is lost in either direction.
  The open content of Part I is exactly the two cores, no more, no less.
-/
import MartinsConjecture.FullReduction

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- Being constant on a cone and incomparable-with-the-identity on a cone
are jointly contradictory. -/
theorem not_constant_and_incomparable (hc : ConstantOnCone F)
    (hinc : OnCone fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) : False := by
  obtain ⟨C, hC⟩ := hc
  obtain ⟨B, hB⟩ := onCone_and hC hinc
  have hX : B ≤ₜ join C B := right_le_join C B
  obtain ⟨hequiv, hbot, -⟩ := hB (join C B) hX
  exact hbot (hequiv.1.trans (left_le_join C B))

/-- **The incomparable core is an impossibility statement**: it is equivalent
to "no invariant function is pointwise incomparable with the identity on a
cone". -/
theorem incomparable_core_iff_never :
    IncomparableImpliesConstant ↔
      ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
        ¬ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) := by
  constructor
  · intro hcore F hF hinc
    exact not_constant_and_incomparable (hcore F hF hinc) hinc
  · intro hnever F hF hinc
    exact absurd hinc (hnever F hF)

/-- **The reduction of Part I is exact**: under Turing determinacy, the
AD-style Part I statement is equivalent to the conjunction of the two open
cores. -/
theorem partI_iff_cores (hTD : TuringDeterminacy fun _ => True) :
    (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
      ConstantOnCone F ∨ AboveIdOnCone F) ↔
    (RegressiveImpliesConstant ∧ IncomparableImpliesConstant) := by
  constructor
  · intro hPartI
    constructor
    · -- Part I ⟹ regressive core
      intro F hF hreg
      rcases hPartI F hF with h | h
      · exact h
      · obtain ⟨B, hB⟩ := onCone_and h hreg
        obtain ⟨habove, -, hnab⟩ := hB B (le.refl B)
        exact absurd habove hnab
    · -- Part I ⟹ incomparable core
      intro F hF hinc
      rcases hPartI F hF with h | h
      · exact h
      · obtain ⟨B, hB⟩ := onCone_and h hinc
        obtain ⟨habove, -, hnab⟩ := hB B (le.refl B)
        exact absurd habove hnab
  · intro ⟨h1, h2⟩
    exact partI_of_cores hTD h1 h2

#print axioms not_constant_and_incomparable
#print axioms incomparable_core_iff_never
#print axioms partI_iff_cores

end Martin
