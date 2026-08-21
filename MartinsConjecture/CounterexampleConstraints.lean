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
import MartinsConjecture.PartIRecast

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

/-- **The complete profile of a Part-1 counterexample.**  Under `MartinPPT` and
determinacy, a Turing-invariant `F` that is neither constant on a cone nor above
the identity on a cone must simultaneously:
1. be **regressive** (`F X <ᵀ X`) on a cone, *or* **incomparable to its argument**
   (`F X ⊥ᵀ X`) on a cone (the comparability trichotomy, minus the excluded
   `≡ᵀ`/`>ᵀ` cases which are above-id); and
2. be **Turing-incomparable to a whole cone of fixed degrees** (`Z ≥ᵀ W₀`), with
   the incomparability uniform over every countable initial interval `[W₀, W₁]`.

This is the sharpest statement of what a hypothetical counterexample looks like;
Part 1 asserts no `F` meets it. -/
theorem counterexample_full_profile (hM : MartinPPT)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    (OnCone (fun X => F X <ₜ X) ∨ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) ∧
    (∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) := by
  refine ⟨?_, nonMP_incomparable_interval hTD hF
    (escaping_of_not_constant hTD hF hnc)
    (fun hmp => hnai ((mp_iff_aboveId_of_martinPPT hM hF).mp hmp))⟩
  rcases comparability_on_cone hTD hF with heq | hgt | hlt | hincomp
  · exact absurd ⟨_, fun X hX => (heq.choose_spec X hX).2⟩ hnai
  · exact absurd ⟨_, fun X hX => (hgt.choose_spec X hX).1⟩ hnai
  · exact Or.inl hlt
  · exact Or.inr hincomp

#print axioms nonMP_incomparable_interval
#print axioms counterexample_full_profile

end Martin
