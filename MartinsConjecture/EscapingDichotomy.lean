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

/-! ### The kernel ideal

The degrees `Z` that lie below `F` on a cone form a Turing ideal — downward closed
and closed under join.  Measure-preservation is exactly this ideal being *all*
degrees; so the obstruction to measure-preservation is a *proper* Turing ideal,
`F`'s "kernel". -/

/-- `Z` is **eventually below `F`**: `Z ≤ᵀ F X` on a cone. -/
def BelowF (F : (ℕ → Bool) → ℕ → Bool) (Z : ℕ → Bool) : Prop :=
  OnCone (fun X => Z ≤ₜ F X)

/-- The kernel ideal is **downward closed**. -/
theorem belowF_downward {Z W : ℕ → Bool} (h : BelowF F Z) (hWZ : W ≤ₜ Z) :
    BelowF F W := by
  obtain ⟨Y, hY⟩ := h
  exact ⟨Y, fun X hX => hWZ.trans (hY X hX)⟩

/-- The kernel ideal is **closed under join**. -/
theorem belowF_join {Z W : ℕ → Bool} (hZ : BelowF F Z) (hW : BelowF F W) :
    BelowF F (Cantor.join Z W) := by
  obtain ⟨B, hB⟩ := onCone_and hZ hW
  exact ⟨B, fun X hX => Cantor.join_le (hB X hX).1 (hB X hX).2⟩

/-- **Measure-preservation is exactly the kernel ideal being everything.** -/
theorem mp_iff_belowF_univ : MeasurePreserving F ↔ ∀ Z, BelowF F Z := Iff.rfl

/-- **Measure-preservation is exactly the kernel ideal being cofinal.**  Since the
ideal is downward closed, being *unbounded* already forces it to be everything.
So the obstruction to measure-preservation is a **bounded** kernel: a non-MP
function's values, on cones, lie below no fixed degree (escaping) yet compute only
degrees below some fixed bound. -/
theorem mp_iff_belowF_cofinal :
    MeasurePreserving F ↔ ∀ W, ∃ Z, W ≤ₜ Z ∧ BelowF F Z := by
  constructor
  · exact fun hmp W => ⟨W, Cantor.le.refl W, hmp W⟩
  · intro hcof Z
    obtain ⟨Z', hZZ', hZ'⟩ := hcof Z
    exact belowF_downward hZ' hZZ'

/-- **A counterexample to `escaping ⟹ MP` is incomparable to a whole cone of
degrees.**  If an escaping invariant `F` is not measure-preserving, its kernel is
bounded by some `W₀`, and above `W₀` every fixed degree is Turing-*incomparable*
to `F` on a cone.  This sharpens the escape theorem: not only does `F` avoid every
fixed degree from below, it is incomparable to all sufficiently high ones. -/
theorem nonMP_incomparable_cone (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) (hnmp : ¬ MeasurePreserving F) :
    ∃ W₀, ∀ Z, W₀ ≤ₜ Z → IncomparableToFixed F Z := by
  rw [mp_iff_belowF_cofinal] at hnmp
  push_neg at hnmp
  obtain ⟨W₀, hW₀⟩ := hnmp
  refine ⟨W₀, fun Z hZ => ?_⟩
  rcases mp_at_or_incomparable hTD hF hesc Z with hle | hinc
  · exact absurd hle (hW₀ Z hZ)
  · exact hinc

/-- **The kernel ideal of a non-MP function avoids a cone.**  If `F` is not
measure-preserving, its kernel `{Z | BelowF F Z}` (a downward-closed, join-closed
Turing ideal) contains no degree `≥ᵀ W₀` for some fixed `W₀` — i.e. it is a *proper*
ideal disjoint from `cone W₀`.  (No determinacy needed; pure from
`mp_iff_belowF_cofinal`.) -/
theorem nonMP_kernel_avoids_cone (hnmp : ¬ MeasurePreserving F) :
    ∃ W₀, ∀ Z, W₀ ≤ₜ Z → ¬ BelowF F Z := by
  rw [mp_iff_belowF_cofinal] at hnmp
  push_neg at hnmp
  exact hnmp

/-- **Profile of a counterexample to `escaping ⟹ MP`.**  An escaping invariant
function that fails to be measure-preserving is (i) *not above the identity* on
any cone, and (ii) Turing-incomparable to a whole cone of fixed degrees.  So a
Part-1 counterexample is genuinely "sideways": high enough to avoid every degree
from below, yet never reaching the identity and incomparable to all sufficiently
high fixed degrees. -/
theorem escaping_nonMP_profile (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) (hnmp : ¬ MeasurePreserving F) :
    ¬ AboveIdOnCone F ∧ ∃ W₀, ∀ Z, W₀ ≤ₜ Z → IncomparableToFixed F Z :=
  ⟨fun hai => hnmp (aboveId_measurePreserving hai),
   nonMP_incomparable_cone hTD hF hesc hnmp⟩

#print axioms mp_at_or_incomparable
#print axioms mp_iff_no_incomparableToFixed
#print axioms escapingMP_iff_no_fixedIncomparable
#print axioms belowF_join
#print axioms nonMP_kernel_avoids_cone
#print axioms mp_iff_belowF_cofinal
#print axioms nonMP_incomparable_cone
#print axioms escaping_nonMP_profile

end Martin
