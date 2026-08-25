/-
**The graph function `X ↦ X ⊕ F X`, and why MartinPPT cannot grip a counterexample.**

For any `F`, its *graph function* `graphFn F X = X ⊕ F X` is the canonical **above-the-identity**
invariant function containing `F`: it computes both the argument `X` and the value `F X`, and `F`
is recovered from it by the (computable, uniform) odd-bit projection `oddPart`.  Two consequences,
both making precise the Track-B/B4 finding (`ATTACK.md`, 2026-08-25):

* Every `F` factors through an above-identity function in the Rudin–Keisler order:
  `[F] ≤_RK [graphFn F]` with `graphFn F` above the identity (hence measure-preserving).  So in RK
  every value sits below an above-id value — no discrimination (cf. `pushCone_rkle_id`).
* `graphFn F` being above-id has **cofinal range**, so `MartinPPT` DOES apply to it and yields a
  pointed perfect tree on which `F` is projection-computable.  But this washes out `F`'s content: the
  join `X ⊕ F X` computes any `Z` the argument does, so a counterexample's incomparability is invisible
  in `graphFn F`, and the tree's representatives have low argument-part (the reps→all-`X` gap).  This is
  exactly why the strongest cone-native tool (MartinPPT) does not cross the barrier.
-/
import MartinsConjecture.MeasurePreservingFilter
import MartinsConjecture.MartinGame

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- The **graph function** of `F`: `X ↦ X ⊕ F X`. -/
def graphFn (F : (ℕ → Bool) → ℕ → Bool) (X : ℕ → Bool) : ℕ → Bool := Cantor.join X (F X)

theorem arg_le_graphFn (F : (ℕ → Bool) → ℕ → Bool) (X : ℕ → Bool) : X ≤ₜ graphFn F X :=
  Cantor.left_le_join X (F X)

theorem val_le_graphFn (F : (ℕ → Bool) → ℕ → Bool) (X : ℕ → Bool) : F X ≤ₜ graphFn F X :=
  Cantor.right_le_join X (F X)

/-- **The graph function is above the identity** (unconditionally). -/
theorem graphFn_aboveId (F : (ℕ → Bool) → ℕ → Bool) : AboveIdOnCone (graphFn F) :=
  ⟨fun _ => false, fun X _ => arg_le_graphFn F X⟩

/-- The graph function of an invariant function is invariant. -/
theorem graphFn_invariant (h : TuringInvariant F) : TuringInvariant (graphFn F) := by
  intro X Y hXY
  refine ⟨Cantor.join_le ?_ ?_, Cantor.join_le ?_ ?_⟩
  · exact hXY.1.trans (Cantor.left_le_join Y (F Y))
  · exact (h X Y hXY).1.trans (Cantor.right_le_join Y (F Y))
  · exact hXY.2.trans (Cantor.left_le_join X (F X))
  · exact (h X Y hXY).2.trans (Cantor.right_le_join X (F X))

/-- The value is recovered from the graph by the odd-bit projection: `oddPart (X ⊕ F X) = F X`. -/
theorem oddPart_graphFn (F : (ℕ → Bool) → ℕ → Bool) (X : ℕ → Bool) :
    oddPart (graphFn F X) = F X := by
  funext k
  simp only [oddPart, graphFn, Cantor.join]
  rw [if_neg (by omega)]
  congr 1
  omega

/-- **Every value factors through its above-identity graph in the RK order.**  `F = oddPart ∘ graphFn F`
exactly, so `[F] = Filter.map F coneFilter` is the pushforward of `[graphFn F]` by `oddPart`, i.e.
`[F] ≤_RK [graphFn F]`, with `graphFn F` above the identity.  So in the (trivial) RK order every
pushforward lies below an above-id one — reinforcing that RK carries no Part-1 information. -/
theorem graphFn_rkle (F : (ℕ → Bool) → ℕ → Bool) :
    RKle (Filter.map F coneFilter) (Filter.map (graphFn F) coneFilter) := by
  refine ⟨oddPart, ?_⟩
  rw [Filter.map_map]
  congr 1
  funext X
  exact (oddPart_graphFn F X).symm

/-- **`F` is above the identity on a cone iff its graph collapses to `F`.**  `graphFn F ≡_M F` says
`X ⊕ F X ≡ᵀ F X` on a cone, i.e. `F X` already computes `X` — exactly above-identity. -/
theorem aboveId_iff_graphFn_equiv : AboveIdOnCone F ↔ MartinEquiv (graphFn F) F := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun X hX =>
      ⟨Cantor.join_le (hb X hX) (Cantor.le.refl (F X)), Cantor.right_le_join X (F X)⟩⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, fun X hX => (Cantor.left_le_join X (F X)).trans (hb X hX).1⟩

/-- **`F` is regressive on a cone iff its graph collapses to the identity.**  `graphFn F ≡_M id` says
`X ⊕ F X ≡ᵀ X` on a cone, i.e. `X` already computes `F X` — exactly `F X ≤ᵀ X`.  So the graph function
interpolates between `id` (regressive `F`) and `F` (above-id `F`), collapsing to an endpoint in each
Part-1 regime; a counterexample (incomparable) is exactly one whose graph collapses to *neither*. -/
theorem regressive_iff_graphFn_equiv_id :
    OnCone (fun X => F X ≤ₜ X) ↔ MartinEquiv (graphFn F) (fun X => X) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun X hX =>
      ⟨Cantor.join_le (Cantor.le.refl X) (hb X hX), Cantor.left_le_join X (F X)⟩⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, fun X hX => (Cantor.right_le_join X (F X)).trans (hb X hX).1⟩

#print axioms graphFn_aboveId
#print axioms graphFn_invariant
#print axioms graphFn_rkle
#print axioms aboveId_iff_graphFn_equiv
#print axioms regressive_iff_graphFn_equiv_id

end Martin
