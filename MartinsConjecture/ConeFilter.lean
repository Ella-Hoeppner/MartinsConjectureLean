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
import Mathlib.Order.Filter.CountableInter

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

/-- The cone filter is a **countable-intersection filter** (Mathlib's typeclass),
so all of Mathlib's countable-`⋂` API applies to "on a cone". -/
instance coneFilter_countableInter : CountableInterFilter coneFilter :=
  ⟨fun S hSc hS => by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simpa using Filter.univ_mem
    · obtain ⟨f, rfl⟩ := hSc.exists_eq_range hne
      rw [Set.sInter_range]
      exact coneFilter_iInter fun n => hS (f n) ⟨n, rfl⟩⟩

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

/-- **The pushforward of the Martin measure by an invariant function is an
ultrafilter on invariant sets.**  For a Turing-invariant `F`, the "distribution"
`F_*` (the cone filter pushed forward) decides every determined invariant set:
`S` or its complement is in it.  This is the measure-theoretic meaning of an
invariant function having a well-defined *value* modulo the Martin measure (its
class in the cone ultrapower). -/
theorem pushCone_dichotomy {F : (ℕ → Bool) → ℕ → Bool} (hF : TuringInvariant F)
    {S : Set (ℕ → Bool)} (hS : TuringInvariantSet S) (hdet : GameDetermined (F ⁻¹' S)) :
    S ∈ Filter.map F coneFilter ∨ Sᶜ ∈ Filter.map F coneFilter := by
  have hinv : TuringInvariantSet (F ⁻¹' S) :=
    fun X Y hXY => hS (F X) (F Y) (hF X Y hXY)
  rw [Filter.mem_map, Filter.mem_map, Set.preimage_compl]
  exact coneFilter_dichotomy hinv hdet

/-- **The pushforward composes:** `F ↦ Filter.map F coneFilter` is a monoid action
of `((ℕ→Bool)→(ℕ→Bool), ∘)` on the cone filter.  So the iterates of an invariant
`F` give `[Fⁿ] = F_*ⁿ U` — the Martin conjecture is a statement about this action
(`[id]` least in the induced order).  (Immediate from `Filter.map_map`, recorded
here as the structural fact.) -/
theorem pushCone_comp (F G : (ℕ → Bool) → ℕ → Bool) :
    Filter.map (F ∘ G) coneFilter = Filter.map F (Filter.map G coneFilter) :=
  (Filter.map_map).symm

#print axioms coneFilter
#print axioms onCone_iff_mem_coneFilter
#print axioms coneFilter_iInter
#print axioms coneFilter_dichotomy
#print axioms pushCone_dichotomy
#print axioms pushCone_comp

end Martin
