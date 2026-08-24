/-
**Measure-preservation and escaping, functorially, via the Martin-measure filter.**

`ConeFilter.lean` packages the Martin measure as `coneFilter` and frames Part 1 as a
statement about the pushforward action `F ↦ Filter.map F coneFilter` (`pushCone_comp`,
`pushCone_id`, `pushCone_const`): a constant `F` pushes `coneFilter` to a principal
`pure c`, and `id` fixes it.  What that framing left open is where the two large
classes sit in the filter order.  Here they are, cleanly:

* **`MeasurePreserving F ⟺ Filter.map F coneFilter ≤ coneFilter`** — `F` is
  measure-preserving exactly when it pushes the Martin measure *forward to a refinement
  of itself*.  (Recall `f ≤ g` for filters means `f` has *more* sets; so the pushforward
  refines `coneFilter` iff every cone-large set stays cone-large after pulling back
  through `F` — which is exactly "for every `Z`, `Z ≤ᵀ F X` on a cone".)
* **`Escaping F ⟺ ∀ Z, {Y | ¬ Y ≤ᵀ Z} ∈ Filter.map F coneFilter`** — `F` is escaping
  exactly when its pushforward concentrates *off* every principal lower cone.  (This one
  is definitional: `OnCone` is filter membership and `Filter.mem_map` is `Iff.rfl`.)

Together with `partI_iff_escapingMP_of_martinPPT`, this reads Part 1's sole open content
in filter language: given `MartinPPT`, Part 1 says every invariant `F` whose pushforward
avoids all lower cones already pushes `coneFilter` to a refinement of itself — the
pushforward "goes to infinity from below ⟹ goes to infinity from above".
-/
import MartinsConjecture.ConeFilter
import MartinsConjecture.MeasurePreserving
import MartinsConjecture.PartIRecast

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **Measure-preservation is a filter inequality.**  A function is measure-preserving
exactly when it pushes the Martin measure forward to a refinement of itself:
`Filter.map F coneFilter ≤ coneFilter`.  (`←`: apply the hypothesis to each `cone Z`,
which is cone-large; `→`: every cone-large `S` contains some `cone W`, and
measure-preservation at `W` puts `F ⁻¹' S ⊇ F ⁻¹' cone W` into `coneFilter`.) -/
theorem measurePreserving_iff_map_le :
    MeasurePreserving F ↔ Filter.map F coneFilter ≤ coneFilter := by
  rw [Filter.le_def]
  constructor
  · intro hmp S hS
    obtain ⟨W, hW⟩ := hS
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (onCone_iff_mem_coneFilter.mp (hmp W))
      (fun X (hX : W ≤ₜ F X) => hW hX)
  · intro h Z
    have hmem := h (cone Z) ⟨Z, subset_rfl⟩
    rw [Filter.mem_map] at hmem
    exact hmem

/-- **Escaping is a filter-avoidance statement.**  `F` is escaping exactly when its
pushforward of the Martin measure lands in the complement of every principal lower cone
`{Y | Y ≤ᵀ Z}` — i.e. `{Y | ¬ Y ≤ᵀ Z} ∈ Filter.map F coneFilter` for every `Z`.
Definitional: `OnCone` is cone-filter membership and `Filter.mem_map` is `Iff.rfl`. -/
theorem escaping_iff_map_avoids_lowerCone :
    Escaping F ↔ ∀ Z, {Y | ¬ Y ≤ₜ Z} ∈ Filter.map F coneFilter :=
  Iff.rfl

/-- **Constancy is a principal pushforward.**  `F` is constant on a cone exactly when its
pushforward of the Martin measure concentrates on a single Turing-degree class:
`{Y | Y ≡ᵀ C} ∈ Filter.map F coneFilter` for some `C`.  (Definitional, via `Filter.mem_map`
and `MartinEquiv`.)  With `measurePreserving_iff_map_le` this puts all three Part-1 outcomes
in one filter language: *concentrate on a degree class* (constant), or *refine `coneFilter`*
(measure-preserving = above-id, under `MartinPPT`). -/
theorem constantOnCone_iff_map_principal :
    ConstantOnCone F ↔ ∃ C, {Y | Y ≡ₜ C} ∈ Filter.map F coneFilter := by
  unfold ConstantOnCone MartinEquiv
  refine exists_congr fun C => ?_
  rw [Filter.mem_map]
  exact Iff.rfl

/-- **The Part-1 conclusion, in filter language: given `MartinPPT`, an invariant `F` is
above the identity on a cone exactly when it pushes the Martin measure to a refinement of
itself.**  Composing `mp_iff_aboveId_of_martinPPT` (Theorem 3.4, from `MartinPPT`) with the
filter characterization of measure-preservation.  So both non-constant alternatives of
Part 1 — measure-preserving and above-identity — collapse (under `MartinPPT`) to the single
filter inequality `Filter.map F coneFilter ≤ coneFilter`; Part 1 then says every invariant
`F` is either `coneFilter`-constant or pushes `coneFilter` to a refinement of itself. -/
theorem aboveIdOnCone_iff_map_le_of_martinPPT (hM : MartinPPT) (hF : TuringInvariant F) :
    AboveIdOnCone F ↔ Filter.map F coneFilter ≤ coneFilter :=
  (mp_iff_aboveId_of_martinPPT hM hF).symm.trans measurePreserving_iff_map_le

/-- **The pushforward value `[F]` depends only on the Martin-equivalence class of `F`.**
If `F` and `G` agree up to `≡ᵀ` on a cone, then their pushforwards of the Martin measure
decide every Turing-invariant set the same way.  With `pushCone_dichotomy` (each `[F]` is an
ultrafilter on invariant sets), this makes `[·]` a well-defined map from Martin-equivalence
classes to ultrafilters-on-invariant-sets — the foundation of the ultrafilter/Rudin–Keisler
reading of Parts 1–2.  (`S` invariant transports `F X ∈ S ⟺ G X ∈ S` across `F X ≡ᵀ G X`.) -/
theorem pushCone_congr_of_martinEquiv {G : (ℕ → Bool) → ℕ → Bool} (hFG : MartinEquiv F G)
    {S : Set (ℕ → Bool)} (hS : TuringInvariantSet S) :
    S ∈ Filter.map F coneFilter ↔ S ∈ Filter.map G coneFilter := by
  rw [Filter.mem_map, Filter.mem_map]
  constructor
  · intro hF
    obtain ⟨B, hB⟩ := onCone_and hFG hF
    exact ⟨B, fun X hX => (hS (F X) (G X) (hB X hX).1).mp (hB X hX).2⟩
  · intro hG
    obtain ⟨B, hB⟩ := onCone_and hFG hG
    exact ⟨B, fun X hX => (hS (F X) (G X) (hB X hX).1).mpr (hB X hX).2⟩

/-- **Part 1 of Martin's conjecture, entirely in Martin-measure language** (given
`MartinPPT`).  Writing `U := coneFilter` and `[F] := Filter.map F U` (the value of `F` in
the cone ultrapower), Part 1 says: **for every Turing-invariant `F`, its pushforward `[F]`
of the Martin measure is either *principal on a single Turing-degree class* (`F` constant)
or *refines `U`* (`F` above the identity).**  This is the precise, machine-checked form of
the ultrafilter/Rudin–Keisler reading of Part 1 (Lutz–Siskind): every invariant function's
pushforward of the Martin ultrafilter is a principal degree-class or a refinement of the
ultrafilter itself.  (The two clauses are `constantOnCone_iff_map_principal` and
`aboveIdOnCone_iff_map_le_of_martinPPT`.) -/
theorem partI_iff_pushforward_of_martinPPT (hM : MartinPPT) :
    (∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) ↔
      (∀ F, TuringInvariant F →
        (∃ C, {Y | Y ≡ₜ C} ∈ Filter.map F coneFilter) ∨
          Filter.map F coneFilter ≤ coneFilter) :=
  forall_congr' fun F => imp_congr_right fun hF =>
    or_congr constantOnCone_iff_map_principal (aboveIdOnCone_iff_map_le_of_martinPPT hM hF)

#print axioms measurePreserving_iff_map_le
#print axioms escaping_iff_map_avoids_lowerCone
#print axioms constantOnCone_iff_map_principal
#print axioms aboveIdOnCone_iff_map_le_of_martinPPT
#print axioms partI_iff_pushforward_of_martinPPT
#print axioms pushCone_congr_of_martinEquiv

end Martin
