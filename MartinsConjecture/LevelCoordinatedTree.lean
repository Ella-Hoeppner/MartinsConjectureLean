/-
**The coordinated-tree skeleton at an ABSTRACT level operator — unifying the finite `Bm` and the Borel
`Am` regions.**

`BnBmSkeleton` runs the relativized Slaman–Steel coordinated tree with `F` computed from a *finite* jump
`jump^[k] x`. The structural analysis of the `Am` region (`MARTIN_PART1_STRUCTURAL_AM.md`) shows that a
**Borel** invariant `F` of Baire rank `ρ` satisfies `F X ≤ᵀ X^(ρ)` for a **fixed** ordinal `ρ` (Theorem A) —
so the Borel `Am` region is a coordinated tree at the *fixed transfinite* level `X^(ρ)`, structurally
identical to the finite case with `jump^[k]` replaced by `X^(ρ)`.

This file abstracts the level to an arbitrary **invariant increasing operator** `L` (`X ≤ᵀ L X`), covering
both instances uniformly: `L = jump^[k]` (finite `Bm`) and `L = X^(ρ)` (Borel `Am`, once a transfinite jump
is available). The assembly is verbatim the `BnBmSkeleton` one — step-3's `x ≤ᵀ F x` on a branch contradicts
the incomparability branch-field — so it discharges the incomparable-core case `F X ≤ᵀ L X` for *any* such
level `L`, modulo the (bracketed) level-`L` coordinated tree.

**Honest scope.** Not a solve. It records that the finite `Bm` and Borel `Am` regions are the SAME skeleton
at different fixed levels, and isolates the single open step per level: the level-`L` coordinated tree. For
`L = jump^[k]` this specializes to `bnBm_of_cores`. The genuine ∞-Borel case (ordinal code, `F X ≰ᵀ` any
`X^(ρ)`) is NOT covered — there is no fixed `L`, which is exactly Steel's conjecture territory.
-/
import MartinsConjecture.MartinTree
import MartinsConjecture.IncomparableArithReduction

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- An **invariant increasing level operator**: `X ≤ᵀ L X` (so branches stay on the cone) — e.g.
`L X = jump^[k] X` or `L X = X^(ρ)`. -/
structure LevelOp where
  /-- The operator. -/
  op : (ℕ → Bool) → ℕ → Bool
  /-- Increasing: `X ≤ᵀ op X`. -/
  incr : ∀ X, X ≤ₜ op X

/-- **The coordinated tree at level `L`.**  A pointed perfect tree computing `F` on branches from `L x`
(one code `e`), injective, with `F x ≤ᵀ L x` and `¬ x ≤ᵀ F x` (incomparability, from the tree on the
incomparability cone).  `L = jump^[k]` recovers `BnBmUniformTree`. -/
structure LevelUniformTree (L : LevelOp) (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The underlying pointed perfect tree. -/
  tree : PPT
  /-- The code computing `F` on branches from `L`-of-the-branch. -/
  code : ℕ
  /-- `F x = Φ_e^{L x}` on branches. -/
  computes : ∀ x, tree.mem x → eval (toPFun (L.op x)) (ofNatCode code) = toPFun (F x)
  /-- `F` injective on branches. -/
  injective : ∀ x y, tree.mem x → tree.mem y → F x = F y → x = y
  /-- `F x ≤ᵀ L x` on branches. -/
  regressive_branch : ∀ x, tree.mem x → F x ≤ₜ L.op x
  /-- `¬ x ≤ᵀ F x` on branches — incomparability. -/
  incomparable_branch : ∀ x, tree.mem x → ¬ x ≤ₜ F x

/-- **Step 1 at level `L` (open).**  Every invariant, incomparable, `F X ≤ᵀ L X`, non-constant `F` admits a
level-`L` coordinated tree.  Bracketed. -/
def HasLevelUniformTree (L : LevelOp) : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) →
    OnCone (fun X => F X ≤ₜ L.op X) →
    ¬ ConstantOnCone F → Nonempty (LevelUniformTree L F)

/-- Domination at level `L` (open). -/
def LevelBranchDomination (L : LevelOp) (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : LevelUniformTree L F, ∀ x, T.tree.mem x →
    ∀ g : ℕ → ℕ, (∃ c : ℕ, eval (toPFun x) (ofNatCode c) = fun n => Part.some (g n)) →
      ∃ h : ℕ → ℕ, (∃ c : ℕ, eval (toPFun (F x)) (ofNatCode c) = fun n => Part.some (h n)) ∧
        Dominates h g

/-- Step-3 conclusion: `x ≤ᵀ F x` on branches (a contradiction with `incomparable_branch`). -/
def LevelBranchAboveId (L : LevelOp) (T : LevelUniformTree L F) : Prop :=
  ∀ x, T.tree.mem x → x ≤ₜ F x

/-- Coding at level `L` (open): domination ⟹ `x ≤ᵀ F x`. -/
def LevelBranchCoding (L : LevelOp) (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  LevelBranchDomination L Dominates →
    ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : LevelUniformTree L F, LevelBranchAboveId L T

/-- The step-3 contradiction: `x ≤ᵀ F x` contradicts the branch incomparability `¬ x ≤ᵀ F x`. -/
theorem levelBranchAboveId_absurd (L : LevelOp) (T : LevelUniformTree L F)
    (hcode : LevelBranchAboveId L T) {x : ℕ → Bool} (hx : T.tree.mem x) : False :=
  T.incomparable_branch x hx (hcode x hx)

/-- Every level-`L` coordinated tree realizes a branch. -/
theorem level_tree_has_branch (L : LevelOp) (T : LevelUniformTree L F) : ∃ x, T.tree.mem x :=
  let ⟨x, hxmem, _⟩ := T.tree.realizes T.tree.code (Cantor.le.refl _)
  ⟨x, hxmem⟩

/-- **The assembly at level `L`.**  Incomparable-core case `F X ≤ᵀ L X` reduces to the three level-`L`
Slaman–Steel ingredients: non-constancy yields a tree, coding gives `x ≤ᵀ F x` on a branch, contradicting
incomparability.  For `L = jump^[k]` this is `bnBm_of_cores`; for `L = X^(ρ)` it is the Borel `Am` case. -/
theorem level_of_cores {L : LevelOp} {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasLevelUniformTree L)
    (hdom : LevelBranchDomination L Dominates) (hcoding : LevelBranchCoding L Dominates)
    (G : (ℕ → Bool) → ℕ → Bool) (hG : TuringInvariant G)
    (hinc : OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X))
    (hlev : OnCone (fun X => G X ≤ₜ L.op X)) : ConstantOnCone G := by
  by_contra hnc
  obtain ⟨T⟩ := hTree G hG hinc hlev hnc
  have hcode : LevelBranchAboveId L T := hcoding hdom G T
  obtain ⟨x, hx⟩ := level_tree_has_branch L T
  exact levelBranchAboveId_absurd L T hcode hx

/-- **The finite jump instance** (`L = jump^[k]`): the level operator for the finite `Bm` region.  Confirms
`level_of_cores` specializes to the `BnBmSkeleton` setting. -/
noncomputable def jumpLevel (k : ℕ) : LevelOp where
  op X := Cantor.jump^[k] X
  incr X := by
    induction k with
    | zero => exact Cantor.le.refl X
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (Cantor.le_jump _)

#print axioms level_of_cores
#print axioms jumpLevel

end Martin
