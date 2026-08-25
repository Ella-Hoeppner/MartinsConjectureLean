/-
**The `BnBm` sub-case, structured by the SAME relativized Slaman–Steel skeleton as `AnBm`.**

`BnBm` is the incomparable-core sub-case `F X ≡ₐ X` (both `Bn : ∃k, X ≤ᵀ (F X)^(k)` and
`Bm : ∃k, F X ≤ᵀ X^(k)`), with `F X ⊥ᵀ X`.  It is the single face the four-way map leaves native to
neither of the two known Martin regimes (the arithmetic-preserving Turing-dropping / CBER phenomenon).

**Key observation.**  The `AnBm` assembly in `ArithRegressiveSkeleton` consumes its branch data through
exactly one channel: `arith_strict_branch` turns branch-strictness `X ≰ₐ F X` into `¬ x ≤ᵀ F x`, which
then contradicts step-3's `x ≤ᵀ F x`.  For `BnBm` the *incomparability* `F X ⊥ᵀ X` gives `¬ x ≤ᵀ F x`
**directly** — provided the coordinated tree is based on the incomparability cone (branches `≥ᵀ` its base,
hence still incomparable).  So `BnBm` reduces to a coordinated-tree skeleton *structurally identical* to
`AnBm`'s, differing only in where the branch-field `¬ x ≤ᵀ F x` comes from (incomparability, not
arith-strictness).  This file makes that precise and machine-checks the assembly.

**Honest scope.**  This does NOT solve `BnBm`.  It shows `BnBm` is *skeleton-reducible* to the same three
relativized S-S ingredients as `AnBm`, with its own step-1 bracket (`HasBnBmUniformTree`).  That step-1 —
a tree computing `F` from `x^(k)`, injective, with branches on the incomparability cone, for an `F` with
`F X ≡ₐ X` — is where the genuine Turing-specific CBER difficulty concentrates (arith-preserving injective
uniformization coordinated with the tree).  It is bracketed and left OPEN, a *different* (and plausibly
harder) bracket than `AnBm`'s.  Value: `BnBm` is not structurally exotic — it is the incomparable-core
instance of the same coordinated-tree method — so the open content of the whole `Bm` region
(`AnBm ∪ BnBm`) is uniformly "relativized Slaman–Steel step 1".
-/
import MartinsConjecture.MartinTree
import MartinsConjecture.IncomparableArithReduction
import MartinsConjecture.ArithRegressiveSkeleton

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! ### Step 1: the coordinated tree for `BnBm` (branches on the incomparability cone) -/

/-- **Step 1 for `BnBm`.**  A coordinated pointed perfect tree computing `F` on branches from `x^(k)`,
injective, with `F x ≤ᵀ x^(k)` (the `Bm` half) and — crucially — `¬ x ≤ᵀ F x` on branches (from basing the
tree on the incomparability cone).  Identical to `ArithRegressiveUniformTree` except the last field is raw
incomparability `¬ x ≤ᵀ F x` in place of arith-strictness `X ≰ₐ F X`. -/
structure BnBmUniformTree (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The underlying pointed perfect tree. -/
  tree : PPT
  /-- The fixed jump level `k` (`F X ≤ᵀ X^(k)`). -/
  level : ℕ
  /-- The oracle code computing `F` on branches from their `k`-th jump. -/
  code : ℕ
  /-- A single code computes `F` on every branch from its `k`-th jump: `F x = Φ_e^{x^(k)}`. -/
  computes : ∀ x, tree.mem x →
    eval (toPFun (Cantor.jump^[level] x)) (ofNatCode code) = toPFun (F x)
  /-- `F` is injective on the branches. -/
  injective : ∀ x y, tree.mem x → tree.mem y → F x = F y → x = y
  /-- `F x ≤ᵀ x^(k)` on branches (the `Bm` half). -/
  regressive_branch : ∀ x, tree.mem x → F x ≤ₜ Cantor.jump^[level] x
  /-- `¬ x ≤ᵀ F x` on branches — incomparability, from the tree being based on the incomparability cone. -/
  incomparable_branch : ∀ x, tree.mem x → ¬ x ≤ₜ F x

/-- **The open core, step 1 for `BnBm`.**  Every invariant, incomparable, arithmetically-equivalent
(`Bn ∧ Bm`), non-constant `F` admits a `BnBm` coordinated tree.  The genuine Turing-specific CBER locus;
bracketed and left OPEN.  (A different — plausibly harder — bracket than `AnBm`'s: the code must compute an
arith-*preserving* `F` and the branches must stay on the incomparability cone.) -/
def HasBnBmUniformTree : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) →
    (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (F X))) →
    (∃ k, OnCone (fun X => F X ≤ₜ Cantor.jump^[k] X)) →
    ¬ ConstantOnCone F → Nonempty (BnBmUniformTree F)

/-! ### Steps 2–3: domination and coding (verbatim relativizations, bracketed) -/

/-- A total `g : ℕ → ℕ` is computable from the real `x`. -/
def BnBmFunRelTo (g : ℕ → ℕ) (x : ℕ → Bool) : Prop :=
  ∃ c : ℕ, eval (toPFun x) (ofNatCode c) = fun n => Part.some (g n)

/-- **Step 2 (domination) for `BnBm`.**  On the branches, every `≤ᵀ x` function is dominated by a
`≤ᵀ F x` one (else `x^(k)`, computing `F x = Φ_e^{x^(k)}`, diagonalizes). Bracketed. -/
def BnBmBranchDomination (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : BnBmUniformTree F, ∀ x, T.tree.mem x →
    ∀ g : ℕ → ℕ, BnBmFunRelTo g x → ∃ h : ℕ → ℕ, BnBmFunRelTo h (F x) ∧ Dominates h g

/-- The conclusion of step 3: `x ≤ᵀ F x` on the branches — here a *contradiction* with
`incomparable_branch`. -/
def BnBmBranchAboveId (T : BnBmUniformTree F) : Prop :=
  ∀ x, T.tree.mem x → x ≤ₜ F x

/-- **Step 3 (coding) for `BnBm`.**  Domination (step 2) ⟹ `x ≤ᵀ F x` on branches. Bracketed. -/
def BnBmBranchCoding (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  BnBmBranchDomination Dominates →
    ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : BnBmUniformTree F, BnBmBranchAboveId T

/-! ### The assembly (fully proved) -/

/-- **The step-3 contradiction for `BnBm`.**  Step-3's `x ≤ᵀ F x` on a branch contradicts the branch's
incomparability `¬ x ≤ᵀ F x` — *directly*, with no arithmetic detour. -/
theorem bnBmBranchAboveId_absurd (T : BnBmUniformTree F)
    (hcode : BnBmBranchAboveId T) {x : ℕ → Bool} (hx : T.tree.mem x) : False :=
  T.incomparable_branch x hx (hcode x hx)

/-- Every `BnBm` coordinated tree realizes a branch. -/
theorem bnBm_tree_has_branch (T : BnBmUniformTree F) : ∃ x, T.tree.mem x :=
  let ⟨x, hxmem, _⟩ := T.tree.realizes T.tree.code (Cantor.le.refl _)
  ⟨x, hxmem⟩

/-- Step 2 ⟹ step 3's conclusion, composed. -/
theorem bnBmBranchAboveId_of_domination {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hcoding : BnBmBranchCoding Dominates) (hdom : BnBmBranchDomination Dominates)
    (T : BnBmUniformTree F) : BnBmBranchAboveId T :=
  hcoding hdom F T

/-- **The full assembly: `BnBm` reduces to the three (relativized) S-S ingredients.**  In the non-constant
case, step 1 supplies a coordinated tree; steps 2–3 give `x ≤ᵀ F x` on a branch; that contradicts the
branch's incomparability — so the non-constant case is vacuous and `F` is constant on a cone.  Structurally
identical to `arithRegressive_of_cores`, with incomparability replacing arith-strictness as the source of
the contradiction. -/
theorem bnBm_of_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasBnBmUniformTree)
    (hdom : BnBmBranchDomination Dominates) (hcoding : BnBmBranchCoding Dominates) :
    SubcaseBnBm := by
  intro G hG hinc hBn hBm
  by_contra hnc
  obtain ⟨T⟩ := hTree G hG hinc hBn hBm hnc
  have hcode : BnBmBranchAboveId T := bnBmBranchAboveId_of_domination hcoding hdom T
  obtain ⟨x, hx⟩ := bnBm_tree_has_branch T
  exact bnBmBranchAboveId_absurd T hcode hx

/-- **Consequence: the entire `Bm` region reduces to relativized Slaman–Steel step-1 brackets.**  Combining
`bnBm_of_cores` with `arithBelowHalf_of_cases` and the `AnBm` skeleton (`StrictArithRegressiveConstant`):
the arithmetically-bounded half `ArithBelowHalf` follows from the `AnBm` coordinated tree
(`StrictArithRegressiveConstant`) and the `BnBm` coordinated tree — two step-1 brackets of the same
relativized-S-S method. -/
theorem arithBelowHalf_of_bnBm_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTD : TuringDeterminacy fun _ => True)
    (harith : StrictArithRegressiveConstant)
    (hTree : HasBnBmUniformTree)
    (hdom : BnBmBranchDomination Dominates) (hcoding : BnBmBranchCoding Dominates) :
    ArithBelowHalf :=
  arithBelowHalf_of_cases hTD harith (bnBm_of_cores hTree hdom hcoding)

/-- **The whole `Bm` region reduces to TWO coordinated-tree brackets.**  `ArithBelowHalf`
(the arithmetically-bounded incomparable region `F X ≤ₐ X`) follows from the `AnBm` relativized-S-S
ingredients (`HasArithRegressiveUniformTree` + domination + coding, via `arithRegressive_of_cores`) and the
`BnBm` ones (`HasBnBmUniformTree` + domination + coding, via `bnBm_of_cores`).  Same three-step method,
two step-1 brackets — the `AnBm` tree and the (CBER-harder) `BnBm` tree.  This is the precise sense in which
the open content of the `Bm` region is *uniformly* "relativized Slaman–Steel step 1". -/
theorem arithBelowHalf_of_all_tree_cores {D₁ D₂ : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTD : TuringDeterminacy fun _ => True)
    (hTreeA : HasArithRegressiveUniformTree)
    (hdomA : ArithBranchDomination D₁) (hcodingA : ArithBranchCoding D₁)
    (hTreeB : HasBnBmUniformTree)
    (hdomB : BnBmBranchDomination D₂) (hcodingB : BnBmBranchCoding D₂) :
    ArithBelowHalf :=
  arithBelowHalf_of_cases hTD
    (arithRegressive_of_cores hTreeA hdomA hcodingA)
    (bnBm_of_cores hTreeB hdomB hcodingB)

/-- **Headline capstone: Part 1 ⟸ two coordinated-tree brackets + the `Am` region.**  Assembling the
whole analysis: `RegressiveSlamanSteel` (known) discharges the regressive core; the incomparable core
splits (primary divide) into `ArithBelowHalf` and `ArithEscapingHalf`; `ArithBelowHalf` reduces to the
`AnBm` and `BnBm` relativized-S-S coordinated-tree ingredients (`arithBelowHalf_of_all_tree_cores`); and
`ArithEscapingHalf` (`= Am`) is supplied as the remaining input.  So Part 1 of Martin's conjecture holds
given: the known regressive theorem, *one* relativized-Slaman–Steel coordinated-tree method (in two
instances, `AnBm` and `BnBm`), and the `Am` region.  This is the sharpest machine-checked statement of what
a proof of Part 1 must still supply. -/
theorem partI_of_all_tree_cores_and_escaping {D₁ D₂ : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTD : TuringDeterminacy fun _ => True) (hSS : RegressiveSlamanSteel)
    (hTreeA : HasArithRegressiveUniformTree)
    (hdomA : ArithBranchDomination D₁) (hcodingA : ArithBranchCoding D₁)
    (hTreeB : HasBnBmUniformTree)
    (hdomB : BnBmBranchDomination D₂) (hcodingB : BnBmBranchCoding D₂)
    (hAm : ArithEscapingHalf) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_slamanSteel_incomparable hTD hSS
    ((incomparableConstant_iff_arith_halves hTD).mpr
      ⟨arithBelowHalf_of_all_tree_cores hTD hTreeA hdomA hcodingA hTreeB hdomB hcodingB, hAm⟩)

#print axioms bnBmBranchAboveId_absurd
#print axioms bnBm_of_cores
#print axioms arithBelowHalf_of_bnBm_cores
#print axioms arithBelowHalf_of_all_tree_cores
#print axioms partI_of_all_tree_cores_and_escaping

end Martin
