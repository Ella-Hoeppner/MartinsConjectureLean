/-
The boundedness lemma, and the escape theorem for counterexamples.

**Boundedness lemma** (`bounded_implies_constant`): under Turing determinacy,
a Turing-invariant function whose values are bounded by a *fixed* degree on a
cone is constant on a cone.  Proof: there are only countably many `Z`-computable
reals — enumerate them by oracle codes and apply the σ-pigeonhole to the
invariant sets `{X | F X ≡ₜ (n-th Z-computable real)}`.

Consequences:
* Part I of Martin's conjecture holds outright for degree-bounded invariant
  functions (`partI_of_bounded`);
* **the escape theorem** (`counterexample_escapes`): any invariant function
  that is not constant on a cone escapes every fixed degree on a cone;
* the two open cores of Part I (see `Reduction.lean`) need only be proved
  for escaping functions (`regressive_core_iff_escaping`) — a formal
  sharpening of what a counterexample to Martin's conjecture must look like.
-/
import MartinsConjecture.Reduction

open scoped Computability
open OracleCode Cantor

attribute [local instance] Classical.propDecidable

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- The `n`-th `Z`-computable real (junk if machine `n` is not total 0/1). -/
noncomputable def nthComputableIn (Z : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  fun k => decide (1 ∈ eval (toPFun Z) (ofNatCode n) k)

/-- If `W ≤ₜ Z` then `W` literally *is* one of the `nthComputableIn Z`. -/
theorem exists_nthComputableIn {W Z : ℕ → Bool} (h : W ≤ₜ Z) :
    ∃ n, nthComputableIn Z n = W := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  refine ⟨encodeCode c, ?_⟩
  funext k
  rw [nthComputableIn, ofNatCode_encodeCode, hc]
  cases hW : W k <;> simp [toPFun, hW, Part.mem_some_iff]

/-- **The boundedness lemma**: a Turing-invariant function bounded by a fixed
degree on a cone is constant on a cone.  (Countable additivity of Martin
measure: only countably many reals live below `Z`.) -/
theorem bounded_implies_constant (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) {Z : ℕ → Bool}
    (hbd : OnCone fun X => F X ≤ₜ Z) : ConstantOnCone F := by
  obtain ⟨W, hW⟩ := hbd
  set A : ℕ → Set (ℕ → Bool) := fun n => {X | F X ≡ₜ nthComputableIn Z n} with hA
  have hTI : ∀ n, TuringInvariantSet (A n) := by
    intro n X X' hXX'
    constructor
    · intro h
      exact ((hF X X' hXX').symm).trans h
    · intro h
      exact (hF X X' hXX').trans h
  have hcover : cone W ⊆ ⋃ n, A n := by
    intro X hX
    obtain ⟨n, hn⟩ := exists_nthComputableIn (hW X hX)
    exact Set.mem_iUnion.mpr ⟨n, by rw [Set.mem_setOf_eq, hn]; exact equiv.refl _⟩
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover
  exact ⟨nthComputableIn Z n, hn⟩

/-- Part I of Martin's conjecture holds outright for degree-bounded invariant
functions. -/
theorem partI_of_bounded (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) {Z : ℕ → Bool}
    (hbd : OnCone fun X => F X ≤ₜ Z) :
    ConstantOnCone F ∨ AboveIdOnCone F :=
  Or.inl (bounded_implies_constant hTD hF hbd)

/-- **The escape theorem**: an invariant function that is not constant on a
cone escapes every fixed degree on a cone.  Any counterexample to Part I of
Martin's conjecture must have this property. -/
theorem counterexample_escapes (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) :
    ∀ Z : ℕ → Bool, OnCone fun X => ¬ F X ≤ₜ Z := by
  intro Z
  have hTIL : TuringInvariantSet {X | F X ≤ₜ Z} := by
    intro X X' hXX'
    exact ⟨fun h => (hF X X' hXX').2.trans h, fun h => (hF X X' hXX').1.trans h⟩
  rcases cone_theorem _ hTIL (hTD _ trivial hTIL) with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact absurd (bounded_implies_constant hTD hF ⟨Y, fun X hX => hY hX⟩) hnc
  · exact ⟨Y, fun X hX => hY hX⟩

/-- The regressive core need only be proved for *escaping* functions: the
open problem is exactly the case of a regressive invariant function whose
values escape every fixed degree on cones. -/
theorem regressive_core_iff_escaping :
    TuringDeterminacy (fun _ => True) →
    (RegressiveImpliesConstant ↔
      ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
        OnCone (fun X => F X <ₜ X) →
        (∀ Z, OnCone fun X => ¬ F X ≤ₜ Z) → ConstantOnCone F) := by
  intro hTD
  constructor
  · exact fun h F hF hreg _ => h F hF hreg
  · intro h F hF hreg
    by_cases hnc : ConstantOnCone F
    · exact hnc
    · exact h F hF hreg (counterexample_escapes hTD hF hnc)

/-- Likewise for the incomparable core. -/
theorem incomparable_core_iff_escaping :
    TuringDeterminacy (fun _ => True) →
    (IncomparableImpliesConstant ↔
      ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
        OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) →
        (∀ Z, OnCone fun X => ¬ F X ≤ₜ Z) → ConstantOnCone F) := by
  intro hTD
  constructor
  · exact fun h F hF hinc _ => h F hF hinc
  · intro h F hF hinc
    by_cases hnc : ConstantOnCone F
    · exact hnc
    · exact h F hF hinc (counterexample_escapes hTD hF hnc)

#print axioms bounded_implies_constant
#print axioms counterexample_escapes
#print axioms regressive_core_iff_escaping

end Martin
