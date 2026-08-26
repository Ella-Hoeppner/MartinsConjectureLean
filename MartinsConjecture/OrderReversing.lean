/-
**A novel angle on Q4 (no injective-incomparable invariant `F`): partition by order-behavior.**

Part 1's sharpest Q4 disproof target is an **injective incomparable** invariant `F` (`F X ⊥ᵀ X` on a
cone, `F` injective on branch-degrees).  On a pointed perfect tree, comparing `F` on `≤ᵀ`-comparable
branches sorts each pair into three behaviors:
* **order-preserving** (`x ≤ᵀ y ⟹ F x ≤ᵀ F y`),
* **order-reversing** (`x ≤ᵀ y ⟹ F y ≤ᵀ F x`),
* **scrambling** (`F x ⊥ᵀ F y`).

Two of the three are *killed*:
* **order-preserving ⟹ constant** — `incomparable_orderPreserving_constant` (already in the repo);
* **order-reversing ⟹ constant** — proved here (`orderReversing_constant`).  This case had **not** been
  excluded before.  The mechanism: if `F` reverses order on `cone(base)` then `F Y ≤ᵀ F base` for *every*
  `Y ≥ base` (take the minimum `X = base`), so `F` is **bounded** by the single degree `F base`, whence
  constant on a cone by `bounded_implies_constant` (only countably many degrees lie below `F base`).

So an injective incomparable `F` (which is non-constant) can be **neither** order-preserving nor
order-reversing on any cone: it must be genuinely **scrambling** (order-*incomparable* values on
`≤ᵀ`-comparable arguments) everywhere.  This reduces the injective-Q4 target to the pure scrambling case.

**Honest status (a partial result, not a reduction).**  What is proved: `orderReversing_constant` is
unconditional and new; and (with the coding hypothesis) `F` is not order-preserving on a cone either.  So a
counterexample is *not* order-reversing (nor OP) on any cone.  **But the clean "scrambling on every cone" does
NOT follow** — that needs "comparability-preserving-on-a-cone ⟹ constant", and I could not prove it: splitting
`F base`-comparability gives a bounded-*above* case (⟹ constant, = the reversing result) *or* an increasing
"always-`U`" case that only yields `F` bounded *below* (survives).  The full trichotomy needs a Ramsey property
for `D_T`-pairs under AD, which is unproved.  **Deeper:** scrambling ⟺ `V = F_*U_M ≡_RK U_M`, `≠ U_M` — *exactly*
the equivalence half (RK-rigidity) — and `F` and its inverse `g` are BOTH scrambling, so every elementary angle
merely restates it.  So there is almost certainly no elementary scrambling obstruction; `orderReversing_constant`
is the genuine (partial) gain of this attack.
-/
import MartinsConjecture.BoundedCase

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- `F` is **order-reversing on `cone(base)`**: on arguments above `base`, `≤ᵀ` is sent to `≥ᵀ`. -/
def OrderReversingOn (F : (ℕ → Bool) → ℕ → Bool) (base : ℕ → Bool) : Prop :=
  ∀ X Y, base ≤ₜ X → base ≤ₜ Y → X ≤ₜ Y → F Y ≤ₜ F X

/-- **Order-reversing ⟹ constant on a cone** (a new obstruction, the order-reversing companion of
`incomparable_orderPreserving_constant`).  If `F` reverses order on `cone(base)`, then taking the
minimum argument `X = base` gives `F Y ≤ᵀ F base` for all `Y ≥ base`; so `F` is bounded by the fixed
degree `F base`, hence constant on a cone (`bounded_implies_constant`). -/
theorem orderReversing_constant (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    {base : ℕ → Bool} (hrev : OrderReversingOn F base) : ConstantOnCone F :=
  bounded_implies_constant hTD hF
    (Z := F base) ⟨base, fun X hX => hrev base X (Cantor.le.refl base) hX hX⟩

/-- **An incomparable `F` is not order-reversing on any cone.**  Order-reversing would make it constant
(`orderReversing_constant`), but an incomparable `F` is non-constant (a constant value `C` would give
`F X ≡ᵀ C ≤ᵀ X` on a high cone, contradicting `¬ F X ≤ᵀ X`).  So — together with the order-preserving
case — a Q4 counterexample must be genuinely *scrambling* on every cone. -/
theorem incomparable_not_orderReversing (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X))
    {base : ℕ → Bool} (hrev : OrderReversingOn F base) : False := by
  obtain ⟨C, ceqBase, hceq⟩ := orderReversing_constant hTD hF hrev
  obtain ⟨incBase, hinc'⟩ := hinc
  set b := Cantor.join C (Cantor.join ceqBase incBase)
  exact (hinc' b ((Cantor.right_le_join _ _).trans (Cantor.right_le_join C _))).1
    (((hceq b ((Cantor.left_le_join _ _).trans (Cantor.right_le_join C _))).1).trans
      (Cantor.left_le_join _ _))

#print axioms orderReversing_constant
#print axioms incomparable_not_orderReversing

end Martin
