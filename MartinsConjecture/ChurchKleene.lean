/-
**The relativized Church–Kleene ordinal `ω₁^X`, and the engine instantiated.**

`ω₁^X` = the supremum of order types of `X`-computable well-orders of `ℕ`.  This is the
canonical degree-invariant *ordinal* rank, and the one Lutz uses for the regressive case on
the hyperarithmetic degrees.  Here we define it (correctly: guarded by `≤ᵀ X` so non-total
oracle computations, which land in `X′`, are excluded), prove it is **monotone** and
**degree-invariant**, and instantiate the Fodor engine `no_regressive_of_ordinal_rank`:

> no `base`-cone-preserving regressive `F` strictly decreases `ω₁^X`.

Equivalently a regressive counterexample must be **`ω₁`-preserving** — it cannot strictly drop
the Church–Kleene ordinal.  That is *exactly* the case where Lutz's hyperarithmetic argument
would apply on `D_h`, and where the Turing case remains open (the hyp-jump-distance is unbounded
on Turing cones; no `Σ¹₁`-bounding).  See `ATTACK.md`.
-/
import MartinsConjecture.OrdinalUltrapower
import MartinsConjecture.BoundedCase
import Mathlib.SetTheory.Ordinal.Family

open scoped Computability
open Cantor

namespace Martin

/-- The relation on `ℕ` coded by a real `O` (via Cantor pairing). -/
def codedRel (O : ℕ → Bool) : ℕ → ℕ → Prop := fun m k => O (Nat.pair m k) = true

open Classical in
/-- The order type of the relation coded by `O` if it is a well-order, else `0`. -/
noncomputable def wellOrderType (O : ℕ → Bool) : Ordinal :=
  if h : IsWellOrder ℕ (codedRel O) then @Ordinal.type ℕ (codedRel O) h else 0

open Classical in
/-- The `n`-th candidate: the order type contributed by `nthComputableIn X n`, if it is a
genuinely `X`-computable (`≤ᵀ X`) well-order. -/
noncomputable def ckTerm (X : ℕ → Bool) (n : ℕ) : Ordinal :=
  if nthComputableIn X n ≤ₜ X then wellOrderType (nthComputableIn X n) else 0

/-- **The relativized Church–Kleene ordinal `ω₁^X`.**  The sup of order types of the
`X`-computable well-orders of `ℕ`, indexing the reals `≤ᵀ X` by `nthComputableIn X`. -/
noncomputable def churchKleene (X : ℕ → Bool) : Ordinal := ⨆ n : ℕ, ckTerm X n

/-- **`ω₁^X` is monotone in the Turing oracle.**  Every `X`-computable well-order is
`Y`-computable when `X ≤ᵀ Y`. -/
theorem churchKleene_mono {X Y : ℕ → Bool} (hXY : X ≤ₜ Y) :
    churchKleene X ≤ churchKleene Y := by
  apply Ordinal.iSup_le
  intro n
  by_cases h : nthComputableIn X n ≤ₜ X
  · have hX : ckTerm X n = wellOrderType (nthComputableIn X n) := by
      unfold ckTerm; rw [if_pos h]
    have hOY : nthComputableIn X n ≤ₜ Y := h.trans hXY
    obtain ⟨m, hm⟩ := exists_nthComputableIn hOY
    have hmY : nthComputableIn Y m ≤ₜ Y := by rw [hm]; exact hOY
    have hY : ckTerm Y m = wellOrderType (nthComputableIn X n) := by
      unfold ckTerm; rw [if_pos hmY, hm]
    rw [hX, ← hY]
    exact Ordinal.le_iSup _ m
  · have hX : ckTerm X n = 0 := by unfold ckTerm; rw [if_neg h]
    rw [hX]; exact zero_le'

/-- **`ω₁^X` is degree-invariant.** -/
theorem churchKleene_invariant {X Y : ℕ → Bool} (h : X ≡ₜ Y) :
    churchKleene X = churchKleene Y :=
  le_antisymm (churchKleene_mono h.1) (churchKleene_mono h.2)

/-- **No cone-preserving regressive `F` strictly decreases `ω₁^X`** (the engine, instantiated
with the genuine Church–Kleene rank).  A `base`-cone-preserving `F` with `ω₁^{F X} < ω₁^X` for
all `X ≥ᵀ base` is impossible: its iterates would descend the well-founded ordinal ultrapower.
So a regressive counterexample is `ω₁`-preserving. -/
theorem no_omega1_decreasing_conePreserving
    {F : (ℕ → Bool) → ℕ → Bool} {base : ℕ → Bool}
    (hstep : ∀ X, base ≤ₜ X → churchKleene (F X) < churchKleene X ∧ base ≤ₜ F X) : False :=
  no_regressive_of_ordinal_rank hstep

#print axioms churchKleene_mono
#print axioms churchKleene_invariant
#print axioms no_omega1_decreasing_conePreserving

end Martin
