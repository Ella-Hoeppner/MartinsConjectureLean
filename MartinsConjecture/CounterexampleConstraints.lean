/-
**Sharper constraints on a Part-1 counterexample.**

`nonMP_incomparable_cone` (`EscapingDichotomy`) says an escaping non-MP invariant `F`
is incomparable to *each fixed* degree `Z ≥ᵀ W₀` on a (Z-dependent) cone.  The
degrees `≤ᵀ W₁` are **countable**, so countable completeness of the cone filter
(`coneFilter_iInter`) upgrades this to a *single* cone on which `F` is incomparable
to the whole interval `[W₀, W₁]` at once.

This is a genuine strengthening (uniform over a countable interval), and it pins
the shape of a counterexample further: on one cone, `F X` is incomparable to every
fixed degree between `W₀` and `W₁`.
-/
import MartinsConjecture.EscapingDichotomy
import MartinsConjecture.ConeFilter
import MartinsConjecture.BoundedCase

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **Interval incomparability.**  A counterexample `F` (escaping, invariant,
non-measure-preserving) is, for every fixed `W₁`, Turing-incomparable to *every*
degree `Z` with `W₀ ≤ᵀ Z ≤ᵀ W₁` — all on a single cone (the kernel bound `W₀` is
fixed once and for all). -/
theorem nonMP_incomparable_interval (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) (hnmp : ¬ MeasurePreserving F) :
    ∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X) := by
  obtain ⟨W₀, hW₀⟩ := nonMP_incomparable_cone hTD hF hesc hnmp
  refine ⟨W₀, fun W₁ => ?_⟩
  -- countable family indexed by the `W₁`-computable reals
  set f : ℕ → Set (ℕ → Bool) := fun n =>
    {X | W₀ ≤ₜ nthComputableIn W₁ n →
      ¬ F X ≤ₜ nthComputableIn W₁ n ∧ ¬ nthComputableIn W₁ n ≤ₜ F X} with hf
  have hmem : ∀ n, f n ∈ coneFilter := by
    intro n
    by_cases hge : W₀ ≤ₜ nthComputableIn W₁ n
    · -- f n is exactly the incomparability cone for Z = nthComputableIn W₁ n
      have := hW₀ (nthComputableIn W₁ n) hge      -- IncomparableToFixed F Z
      unfold IncomparableToFixed at this
      rw [onCone_iff_mem_coneFilter] at this
      refine Filter.mem_of_superset this (fun X hX => ?_)
      exact fun _ => hX
    · -- vacuous: f n = univ
      exact Filter.univ_mem' (fun _ hZ => absurd hZ hge)
  have hInter : (⋂ n, f n) ∈ coneFilter := coneFilter_iInter hmem
  rw [onCone_iff_mem_coneFilter]
  refine Filter.mem_of_superset hInter (fun X hX Z hW₀Z hZW₁ => ?_)
  obtain ⟨n, hn⟩ := exists_nthComputableIn hZW₁
  have hXn : X ∈ f n := Set.mem_iInter.mp hX n
  rw [hf] at hXn
  simp only [Set.mem_setOf_eq, hn] at hXn
  exact hXn hW₀Z

#print axioms nonMP_incomparable_interval

end Martin
