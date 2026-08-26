/-
**Question 9.3 of the Lutz thesis: Martin's conjecture for 2-uniformly invariant functions.**

Lutz's open-questions chapter (Question 9.3) introduces a natural weakening of uniform
invariance that interpolates between the (solved) uniformly-invariant case and the general
case:

> `f` is **2-uniformly invariant** if there are `u₁, u₂ : ℕ² → ℕ²` such that for all
> `x, y` and `i, j`, if `x ≡ᵀ y` via `(i, j)` then `f(x) ≡ᵀ f(y)` via `u₁(i, j)` **or**
> via `u₂(i, j)`.  Does Martin's conjecture hold for all 2-uniformly invariant functions?

This file records the statement in the repo's vocabulary and the structural facts that are
elementary and sound:

* `TwoUniformlyTuringInvariant` — the Question 9.3 predicate (a *finite disjunction* of
  uniform transformers; `u₂ = u₁` recovers ordinary uniform invariance).
* `TwoUniformlyTuringInvariant.of_uniform` — uniform ⟹ 2-uniform, so the class genuinely
  *contains* the uniform class (the interpolation is non-vacuous).
* `TwoUniformlyTuringInvariant.turingInvariant` — a 2-uniform function is Turing invariant
  (either branch of the disjunction already witnesses `F X ≡ᵀ F Y`).
* `partI_twoUniform_of_uniformize` — **the reduction**: if every 2-uniformly invariant `F`
  is Martin-equivalent to a genuinely uniformly-invariant `G`, then Part 1 holds for all
  2-uniformly invariant functions.  This isolates the entire open content of Question 9.3
  into a single hypothesis, exactly as `incomparable_core_of_uniformization` does for the
  incomparable core.

**Honest status of the gap.**  The hypothesis of `partI_twoUniform_of_uniformize` — "a
finite disjunction of uniform transformers collapses, up to Martin-equivalence, to a single
one" — is a *special case of Steel's Conjecture 9.4* (every invariant function is Martin-
equivalent to a uniform one), restricted to inputs that are already 2-uniform.  Since a
2-uniform function is "one binary choice away" from uniform, this restricted case is a
plausibly-more-tractable target than full Steel: the natural attack is to fix the branch
`{1, 2}` on a pointed perfect tree via the countable-range trick (Lutz Lemma 2.10), after
which `F` is uniform on that tree.  Formalizing that collapse (which needs determinacy in the
Lemma-2.10 form) is left as the concrete next step; it is *not* discharged here, and nothing
below assumes it.
-/
import MartinsConjecture.MartinResults
import MartinsConjecture.RegressiveReduction

open scoped Computability

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **Question 9.3 predicate.**  `F` is *2-uniformly Turing invariant* if index witnesses
for `X ≡ᵀ Y` transform, via one of *two* fixed functions `u₁, u₂`, into index witnesses for
`F X ≡ᵀ F Y`.  Taking `u₂ = u₁` recovers `UniformlyTuringInvariant`. -/
def TwoUniformlyTuringInvariant (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ u₁ u₂ : ℕ × ℕ → ℕ × ℕ, ∀ X Y i j, EquivVia X Y i j →
    EquivVia (F X) (F Y) (u₁ (i, j)).1 (u₁ (i, j)).2 ∨
    EquivVia (F X) (F Y) (u₂ (i, j)).1 (u₂ (i, j)).2

/-- Uniform invariance is the special case `u₂ = u₁`; hence the 2-uniform class contains the
uniform class (the interpolation between uniform and general is non-vacuous). -/
theorem TwoUniformlyTuringInvariant.of_uniform (h : UniformlyTuringInvariant F) :
    TwoUniformlyTuringInvariant F := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, u, fun X Y i j hxy => Or.inl (hu X Y i j hxy)⟩

/-- A 2-uniformly invariant function is Turing invariant: for `X ≡ᵀ Y`, pick index witnesses
`(i, j)`; either disjunct of the 2-uniform condition already gives `F X ≡ᵀ F Y`. -/
theorem TwoUniformlyTuringInvariant.turingInvariant (h : TwoUniformlyTuringInvariant F) :
    TuringInvariant F := by
  obtain ⟨u₁, u₂, hu⟩ := h
  intro X Y hXY
  obtain ⟨i, j, hij⟩ := equiv_iff_exists_equivVia.mp hXY
  rcases hu X Y i j hij with h1 | h2
  · exact h1.equiv
  · exact h2.equiv

/-- **The reduction (Question 9.3 isolated into one hypothesis).**  If every 2-uniformly
invariant function is Martin-equivalent to a genuinely uniformly-invariant one, then Part 1
of Martin's conjecture holds for all 2-uniformly invariant functions.  Proof: transfer the
uniform dichotomy (`partI_uniform_general`, already machine-checked from determinacy) across
`MartinEquiv` (`partI_conclusion_of_martinEquiv`).  This mirrors
`incomparable_core_of_uniformization`; the hypothesis is a sub-case of Steel's Conjecture 9.4. -/
theorem partI_twoUniform_of_uniformize (hTD : TuringDeterminacy fun _ => True)
    (huniformize : ∀ F, TwoUniformlyTuringInvariant F →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    ∀ F, TwoUniformlyTuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F := by
  intro F h2
  obtain ⟨G, hGu, hFG⟩ := huniformize F h2
  exact partI_conclusion_of_martinEquiv hFG (partI_uniform_general hTD G hGu)

#print axioms TwoUniformlyTuringInvariant.of_uniform
#print axioms TwoUniformlyTuringInvariant.turingInvariant
#print axioms partI_twoUniform_of_uniformize

end Martin
