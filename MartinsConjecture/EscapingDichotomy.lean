/-
**The obstruction to measure-preservation is incomparability to a fixed degree.**

The open class-specific half of Part 1 is "escaping ⟹ measure-preserving": if an
invariant `F` avoids every fixed degree from below on a cone (`F X ≰ᵀ Z`), does it
reach every fixed degree from above on a cone (`Z ≤ᵀ F X`)?

Here is a clean sharpening.  For a *fixed* `Z`, the cone theorem applied to the
invariant set `{X | Z ≤ᵀ F X}` gives a dichotomy: either `Z ≤ᵀ F X` on a cone
(measure-preservation holds at `Z`), or `Z ≰ᵀ F X` on a cone.  In the second case,
combined with escaping (`F X ≰ᵀ Z` on a cone), `F X` is **incomparable to `Z`** on
a cone.  So:

> the *only* way measure-preservation can fail at `Z` is that `F X` is Turing
> incomparable to `Z` on a cone.

Hence **escaping ⟹ measure-preserving is equivalent to**: an escaping invariant
function is never incomparable to a fixed degree on a cone (equivalently, it is
eventually *comparable* to every fixed degree).  This recasts the open half as an
incomparability-avoidance statement, in the same family as the incomparable core.
-/
import MartinsConjecture.MeasurePreserving

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **The measure-preservation dichotomy at a fixed degree.**  For an escaping
invariant `F` (under determinacy), for every `Z` either `Z ≤ᵀ F X` on a cone or
`F X` is incomparable to `Z` on a cone. -/
theorem mp_at_or_incomparable (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) (Z : ℕ → Bool) :
    OnCone (fun X => Z ≤ₜ F X) ∨
      OnCone (fun X => ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X) := by
  have hTI : TuringInvariantSet {X | Z ≤ₜ F X} := fun X X' hXX' =>
    ⟨fun h => h.trans (hF X X' hXX').1, fun h => h.trans (hF X X' hXX').2⟩
  rcases cone_theorem _ hTI (hTD _ trivial hTI) with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact Or.inl ⟨Y, fun X hX => hY hX⟩
  · obtain ⟨B, hB⟩ := onCone_and (hesc Z) ⟨Y, fun X hX => hY hX⟩
    exact Or.inr ⟨B, hB⟩

/-- The incomparability obstruction: `F` is **incomparable to `Z` on a cone**. -/
def IncomparableToFixed (F : (ℕ → Bool) → ℕ → Bool) (Z : ℕ → Bool) : Prop :=
  OnCone (fun X => ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)

/-- **Measure-preservation of an escaping invariant `F` is exactly the absence of
a fixed incomparable degree.** -/
theorem mp_iff_no_incomparableToFixed (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) :
    MeasurePreserving F ↔ ∀ Z, ¬ IncomparableToFixed F Z := by
  constructor
  · intro hmp Z hinc
    obtain ⟨B, hB⟩ := onCone_and (hmp Z) hinc
    exact (hB B (Cantor.le.refl B)).2.2 (hB B (Cantor.le.refl B)).1
  · intro h Z
    rcases mp_at_or_incomparable hTD hF hesc Z with hle | hinc
    · exact hle
    · exact absurd hinc (h Z)

/-- **The open half, recast.**  "Escaping ⟹ measure-preserving" holds iff no
escaping invariant function is incomparable to a fixed degree on a cone.  A
counterexample to Part 1 would, at some fixed degree `Z`, take values incomparable
to `Z` on a cone. -/
theorem escapingMP_iff_no_fixedIncomparable (hTD : TuringDeterminacy fun _ => True) :
    (∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) ↔
      (∀ F, TuringInvariant F → Escaping F → ∀ Z, ¬ IncomparableToFixed F Z) :=
  ⟨fun h F hF hesc => (mp_iff_no_incomparableToFixed hTD hF hesc).mp (h F hF hesc),
   fun h F hF hesc => (mp_iff_no_incomparableToFixed hTD hF hesc).mpr (h F hF hesc)⟩

#print axioms mp_at_or_incomparable
#print axioms mp_iff_no_incomparableToFixed
#print axioms escapingMP_iff_no_fixedIncomparable

end Martin
