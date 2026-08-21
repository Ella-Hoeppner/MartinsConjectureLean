/-
**The Martin measure as a `Filter`.**

The sets that contain a Turing cone form a proper, countably-complete filter on
Cantor space — the *cone filter*, the measure underlying the whole subject (on
Turing-invariant sets it is an ultrafilter, by `cone_theorem`).  Packaging it as a
Mathlib `Filter` makes "on a cone" literally "in the cone filter"
(`onCone_iff_mem_coneFilter`) and exposes the countable completeness
(`coneFilter_iInter`) that drives the σ-pigeonhole.
-/
import MartinsConjecture.RegularChain
import MartinsConjecture.MartinMeasure
import Mathlib.Order.Filter.Basic

open scoped Computability
open Cantor

namespace Martin

/-- **The cone filter** (the Martin measure): the sets containing a Turing cone.
A proper filter — closed under supersets (same base) and finite intersection
(join the bases). -/
def coneFilter : Filter (ℕ → Bool) where
  sets := {S | ∃ Y, cone Y ⊆ S}
  univ_sets := ⟨fun _ => false, fun _ _ => trivial⟩
  sets_of_superset := fun ⟨Y, hY⟩ hST => ⟨Y, hY.trans hST⟩
  inter_sets := fun ⟨Y, hY⟩ ⟨Z, hZ⟩ =>
    ⟨Cantor.join Y Z, fun _ hX =>
      ⟨hY ((Cantor.left_le_join Y Z).trans hX), hZ ((Cantor.right_le_join Y Z).trans hX)⟩⟩

@[simp] theorem mem_coneFilter {S : Set (ℕ → Bool)} : S ∈ coneFilter ↔ ∃ Y, cone Y ⊆ S := Iff.rfl

/-- **"On a cone" is exactly "in the cone filter".** -/
theorem onCone_iff_mem_coneFilter {P : (ℕ → Bool) → Prop} :
    OnCone P ↔ {X | P X} ∈ coneFilter := Iff.rfl

/-- The cone filter is proper (a cone is nonempty). -/
instance coneFilter_neBot : coneFilter.NeBot :=
  ⟨by
    intro h
    have hempty : (∅ : Set (ℕ → Bool)) ∈ coneFilter := by rw [h]; exact Filter.mem_bot
    obtain ⟨Y, hY⟩ := hempty
    exact hY (Cantor.le.refl Y)⟩

/-- **Countable completeness of the Martin measure.**  A countable intersection of
cone-filter sets is again in the cone filter (join all the bases via `bigJoin`) —
the engine of the σ-pigeonhole (`exists_onCone_of_cover`). -/
theorem coneFilter_iInter {f : ℕ → Set (ℕ → Bool)} (hf : ∀ n, f n ∈ coneFilter) :
    (⋂ n, f n) ∈ coneFilter := by
  choose Y hY using hf
  exact ⟨bigJoin Y, fun X hX => Set.mem_iInter.mpr fun n => hY n ((le_bigJoin Y n).trans hX)⟩

/-- **The Martin measure is an ultrafilter on the Turing-invariant sets.**  This
is exactly the cone theorem, packaged: a determined invariant set, or its
complement, is in the cone filter. -/
theorem coneFilter_dichotomy {A : Set (ℕ → Bool)} (hTI : TuringInvariantSet A)
    (hDet : GameDetermined A) : A ∈ coneFilter ∨ Aᶜ ∈ coneFilter :=
  cone_theorem A hTI hDet

/-- The ultrafilter dichotomy, threaded through `TuringDeterminacy`. -/
theorem coneFilter_dichotomy_TD {Γ : Set (ℕ → Bool) → Prop} (hTD : TuringDeterminacy Γ)
    {A : Set (ℕ → Bool)} (hΓ : Γ A) (hTI : TuringInvariantSet A) :
    A ∈ coneFilter ∨ Aᶜ ∈ coneFilter :=
  coneFilter_dichotomy hTI (hTD A hΓ hTI)

#print axioms coneFilter
#print axioms onCone_iff_mem_coneFilter
#print axioms coneFilter_iInter
#print axioms coneFilter_dichotomy

end Martin
