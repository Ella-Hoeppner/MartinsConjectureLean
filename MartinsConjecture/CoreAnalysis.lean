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

/-! ### Exactness of the Part II reductions -/

/-- The totality reduction is exact. -/
theorem partII_total_iff_core (hTD : TuringDeterminacy fun _ => True) :
    PartII_Borel_Total ↔ ComparisonCore := by
  constructor
  · intro htot F G hF hG hinc
    obtain ⟨B, hB⟩ | ⟨B, hB⟩ := htot F G hF hG
    · obtain ⟨B', hB'⟩ := onCone_and ⟨B, hB⟩ hinc
      obtain ⟨hle, hnle, -⟩ := hB' B' (le.refl B')
      exact hnle hle
    · obtain ⟨B', hB'⟩ := onCone_and ⟨B, hB⟩ hinc
      obtain ⟨hle, -, hnle⟩ := hB' B' (le.refl B')
      exact hnle hle
  · exact partII_total_of_core hTD

/-- The well-foundedness reduction is exact. -/
theorem partII_WF_iff_core : PartII_Borel_WF ↔ DescendingChainCore := by
  constructor
  · intro hWF Fs hreg hchain
    letI : IsIrrefl {F // Regular F} (fun F G => MartinLT F.1 G.1) :=
      ⟨fun F h => h.2 h.1⟩
    letI : IsTrans {F // Regular F} (fun F G => MartinLT F.1 G.1) :=
      ⟨fun F G H h1 h2 => ⟨h1.1.trans h2.1, fun hc => h2.2 (hc.trans h1.1)⟩⟩
    letI : IsStrictOrder {F // Regular F} (fun F G => MartinLT F.1 G.1) := ⟨⟩
    exact (RelEmbedding.natGT (fun n => (⟨Fs n, hreg n⟩ : {F // Regular F}))
      (fun n => hchain n)).not_wellFounded hWF
  · exact partII_WF_of_core

/-- The successor reduction is exact (given the proved half
`martinLT_jump`). -/
theorem partII_succ_iff_core : PartII_Borel_Succ ↔ JumpMinimalityCore := by
  constructor
  · intro hsucc F G hF hG hFG
    exact (hsucc F hF).2 G hG hFG
  · exact partII_succ_of_core

/-- **The full exactness theorem**: under Turing determinacy, Part II of the
Borel Martin conjecture is *equivalent* to the conjunction of its three
cores.  Together with `partI_iff_cores`, the isolation of the conjecture's
open content is lossless in both directions. -/
theorem partII_iff_cores (hTD : TuringDeterminacy fun _ => True) :
    PartII_Borel ↔ (ComparisonCore ∧ DescendingChainCore ∧ JumpMinimalityCore) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(partII_total_iff_core hTD).mp h1, partII_WF_iff_core.mp h2,
      partII_succ_iff_core.mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨partII_total_of_core hTD h1, partII_WF_of_core h2,
      partII_succ_of_core h3⟩

/-- The AD-style full statement of Martin's conjecture: Part I for *all*
Turing-invariant functions, plus Part II. -/
def MartinConjectureAD : Prop :=
  (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    ConstantOnCone F ∨ AboveIdOnCone F) ∧ PartII_Borel

/-- **The final capstone**: under Turing determinacy, the full AD-style
Martin conjecture is *equivalent* to the conjunction of the five isolated
cores.  The formal isolation of the conjecture's open content is complete
and lossless. -/
theorem martinConjectureAD_iff_cores (hTD : TuringDeterminacy fun _ => True) :
    MartinConjectureAD ↔
      (RegressiveImpliesConstant ∧ IncomparableImpliesConstant) ∧
      (ComparisonCore ∧ DescendingChainCore ∧ JumpMinimalityCore) := by
  rw [MartinConjectureAD, partI_iff_cores hTD, partII_iff_cores hTD]

#print axioms not_constant_and_incomparable
#print axioms incomparable_core_iff_never
#print axioms partI_iff_cores
#print axioms partII_total_iff_core
#print axioms partII_WF_iff_core
#print axioms partII_succ_iff_core
#print axioms partII_iff_cores
#print axioms martinConjectureAD_iff_cores

end Martin
