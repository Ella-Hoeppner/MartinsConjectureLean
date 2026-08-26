/-
**The STRICT half of the RK-rigidity of `U_M`, reduced to a pointed injective tree.**

Part 1's open core = RK-rigidity of the Martin measure `U_M`, which splits (Lutz–Siskind Thm 5.15) into
a **strict half** (`V ≤_RK U_M ⟹ U_M ≤_RK V`, i.e. `U_M` is RK-minimal) and an **equivalence half**
(`U_M ≤_RK V ≤_RK U_M ⟹ V = U_M`).  In `MeasurePreservingCK.lean` the strict half for a pushforward
`V = F_*U_M` was characterized as **dominated-invertibility** `DominatedInvertible F`
(`∃` invariant `g`, `X ≤ᵀ g(F X)` on a cone), via `strictHalf_iff_dominatedInvertible`.

This file reduces that — exactly as `PointedTree.lean` reduces Theorem 3.4 to `GroszekSlaman` — to a single
named tree-existence statement: **`PointedInjectiveTree F`**, a pointed perfect tree realizing a cone on
which `F` is *effectively injective* (the branch is recovered from its `F`-value plus the tree).  This is the
recursion-theoretic output of **Marks's conjecture** (invariant `F` injective on a pointed perfect tree),
the standard/open construction the strict half rests on.  Everything else — the passage from the tree to the
dominating inverse `g y = y ⊕ code`, hence to `U_M ≤_RK F_*U_M` — is machine-checked here.

The interface is the injectivity analogue of `InvertingTree` (which handled *increasing* `F` by
right-inverting a modulus); here `F` is arbitrary and we use only that its value plus the tree recovers the
branch, so the explicit dominating map is simply "join with the tree code".
-/
import MartinsConjecture.MeasurePreservingCK

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **The output of a Marks-style pointed injective tree** for `F`.  A pointed perfect tree (code `code`,
branches `mem`) that realizes a cone of degrees, on which `F` is *effectively injective*: the branch is
recovered from its `F`-value together with the tree (`recover`, the Lemma-2.1 conclusion applied to `F`).
Its existence is exactly the (open) Marks pointed-perfect-tree construction. -/
structure PointedInjectiveTree (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The tree code — a real every branch computes. -/
  code : ℕ → Bool
  /-- Membership in the branches `[T]`. -/
  mem : (ℕ → Bool) → Prop
  /-- Pointedness: every branch computes the tree. -/
  pointed : ∀ x, mem x → code ≤ₜ x
  /-- The tree realizes a cone: every degree `≥ᵀ code` is a branch's. -/
  realizes : ∀ d, code ≤ₜ d → ∃ x, mem x ∧ x ≡ₜ d
  /-- Effective injectivity: the branch is recovered from its `F`-value and the tree. -/
  recover : ∀ x, mem x → x ≤ₜ Cantor.join (F x) code

/-- **A pointed injective tree yields dominated-invertibility**, with the explicit invariant dominating map
`g y = y ⊕ code`.  For a degree `d ≥ᵀ code`, realize it by a branch `x ≡ᵀ d`; then
`d ≡ᵀ x ≤ᵀ F x ⊕ code ≡ᵀ F d ⊕ code = g (F d)` (recovery + invariance). -/
theorem dominatedInvertible_of_pointedInjectiveTree (hF : TuringInvariant F)
    (Tr : PointedInjectiveTree F) : DominatedInvertible F := by
  refine ⟨fun y => Cantor.join y Tr.code, ?_, Tr.code, fun X hX => ?_⟩
  · -- `g y = y ⊕ code` is Turing-invariant.
    intro X Y hXY
    exact ⟨Cantor.join_le (hXY.1.trans (Cantor.left_le_join Y Tr.code)) (Cantor.right_le_join Y Tr.code),
           Cantor.join_le (hXY.2.trans (Cantor.left_le_join X Tr.code)) (Cantor.right_le_join X Tr.code)⟩
  · -- On the cone above `code`: `X ≤ᵀ g (F X) = F X ⊕ code`.
    obtain ⟨x, hxmem, hxX⟩ := Tr.realizes X hX
    -- `X ≤ᵀ x ≤ᵀ F x ⊕ code ≤ᵀ F X ⊕ code`  (realize, recover, invariance).
    refine hxX.2.trans ((Tr.recover x hxmem).trans ?_)
    exact Cantor.join_le (((hF x X hxX).1).trans (Cantor.left_le_join (F X) Tr.code))
      (Cantor.right_le_join (F X) Tr.code)

/-- **The strict half from a pointed injective tree** (given `MartinPPT`): `Nonempty (PointedInjectiveTree F)`
⟹ `StrictHalfFor F` (`U_M ≤_RK F_*U_M`).  So — mirroring `partI_of_groszekSlaman` — the *entire* open content
of the strict half is the single named existence statement (Marks's construction). -/
theorem strictHalf_of_pointedInjectiveTree (hM : MartinPPT) (hF : TuringInvariant F)
    (Tr : PointedInjectiveTree F) : StrictHalfFor F :=
  (strictHalf_iff_dominatedInvertible hM hF).mpr (dominatedInvertible_of_pointedInjectiveTree hF Tr)

/-- **Soundness / non-vacuity**: the identity admits a pointed injective tree (the full space, `code`
computable), so the interface is not jointly contradictory.  `recover` for `F = id` is `x ≤ᵀ x ⊕ code`. -/
theorem pointedInjectiveTree_id : Nonempty (PointedInjectiveTree (fun x => x)) :=
  ⟨{ code := fun _ => false
     mem := fun _ => True
     pointed := fun x _ => Cantor.le_of_computable (Computable.const false)
     realizes := fun d _ => ⟨d, trivial, Cantor.equiv.refl d⟩
     recover := fun x _ => Cantor.left_le_join x _ }⟩

#print axioms dominatedInvertible_of_pointedInjectiveTree
#print axioms strictHalf_of_pointedInjectiveTree

end Martin
