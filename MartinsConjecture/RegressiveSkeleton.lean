/-
**The Slaman–Steel theorem for the regressive core, as a clean skeleton.**

`Reduction.lean` reduces Part I of Martin's conjecture to two open cores; the
first is the *regressive* case (`RegressiveImpliesConstant`): a Turing-invariant
`F` with `F X ≤ᵀ X` on a cone is constant on a cone.  Slaman–Steel proved this
outright — it is a KNOWN theorem, not an open problem — and this file structures
their proof.

The Slaman–Steel argument, for an invariant, regressive, **non-constant** `F`,
runs in three steps:

1. **Coordinated tree (the crux).**  Determinacy yields a pointed perfect tree
   `T` on which `F` is *computable and injective by a single code*: a numeral `e`
   with `F x = Φ_e^x` for every branch `x`, and `F` injective on branches.  This
   is STRONGER than plain `MartinPPT` — the tree is coordinated with `F`'s code.
   Modelled here as the structure `RegressiveUniformTree` and the existence
   `Prop` `HasRegressiveUniformTree`; **the genuinely-hard open core**.

2. **Domination.**  For a branch `x`, every function `≤ᵀ x` is dominated by a
   function `≤ᵀ F x` (else `x` diagonalizes against `F x = Φ_e^x`).  Bracketed as
   `BranchDomination`.

3. **Coding ⟹ `x ≤ᵀ F x`.**  Code the bits of `x` into the relative growth rates
   of two fast-growing `F(x)`-computable functions; with the domination of step 2
   this gives `x ≤ᵀ F x` on the branches.  Bracketed as `BranchCoding`; its
   conclusion (`BranchAboveId`) is what the assembly consumes.

**What is proved here (sorry-free):**

* `branchEquiv_of_regressive` — on branches, regressive + `BranchAboveId` gives
  `F x ≡ᵀ x`;
* `aboveId_of_branchAboveId` — the tree's `realizes` field lifts "`x ≤ᵀ F x` on
  branches" to `AboveIdOnCone F` (the step-3⟹cone logic);
* `branchCoding_of_domination` — step 2 ⟹ step 3's conclusion is bracketed as an
  implication so the two hard steps compose cleanly;
* `regressiveSlamanSteel_of_cores` — **the full assembly**: the coordinated tree
  (step 1) + `BranchAboveId` (step 3) ⟹ `RegressiveSlamanSteel`;
* `regressiveImpliesConstant_of_regressiveSlamanSteel` — `RegressiveSlamanSteel`
  discharges the open core `RegressiveImpliesConstant` of `Reduction.lean`.

The two hard steps (1 and 2) are isolated as explicit named `Prop`s and marked
open; everything downstream is machine-checked.  No `sorry`, no new axioms.
-/
import MartinsConjecture.MartinTree
import MartinsConjecture.Reduction

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! ### The regressive predicate and the target theorem -/

/-- `F` is **regressive** (below the identity, non-strictly, on a cone): a single
cone on which `F X ≤ᵀ X`.  This is the hypothesis of the regressive core of
`Reduction.lean` weakened from `<ᵀ` to `≤ᵀ`; the strict version implies it. -/
def Regressive (F : (ℕ → Bool) → ℕ → Bool) : Prop := OnCone fun X => F X ≤ₜ X

/-- A strictly-regressive function is regressive. -/
theorem regressive_of_strict (h : OnCone fun X => F X <ₜ X) : Regressive F :=
  onCone_mono (fun _ hX => hX.1) h

/-- Sanity: `Regressive F` is defeq to the hypothesis of `Reduction.RegressiveSlamanSteel`
(`OnCone (fun X => F X ≤ᵀ X)`), so the assembly below concludes exactly that (existing) theorem. -/
theorem regressive_eq_reductionHyp (F : (ℕ → Bool) → ℕ → Bool) :
    Regressive F = OnCone (fun X => F X ≤ₜ X) := rfl

/-! ### Step 1: the coordinated pointed perfect tree (the crux) -/

/-- **Step 1 (the crux).**  A **regressive uniform tree** for `F` bundles a
pointed perfect tree `T` with a single oracle code `e` that computes `F` on every
branch, together with the injectivity of `F` on the branches.  This is the
Slaman–Steel "coordinated tree": it is strictly stronger than `MartinPPT`, which
only supplies a tree inside a cofinal set, *not* one on which `F` is uniformly
computed and injective.

The three data are exactly what steps 2–3 consume:
* `computes` — `F x = Φ_e^x` for branches (a *single* code, Slaman–Steel's
  uniformization coordinated with the tree);
* `injective` — `F` is injective on the branches (needed to recover `x` from
  `F x` and the tree, `PPT.recover`);
* (`tree`/`code` carry the pointed-perfect-tree data and its cone realization). -/
structure RegressiveUniformTree (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The underlying pointed perfect tree. -/
  tree : PPT
  /-- The oracle code that computes `F` on the branches. -/
  code : ℕ
  /-- A single code computes `F` on every branch. -/
  computes : ∀ x, tree.mem x → eval (toPFun x) (ofNatCode code) = toPFun (F x)
  /-- `F` is injective on the branches. -/
  injective : ∀ x y, tree.mem x → tree.mem y → F x = F y → x = y
  /-- The tree lives inside the regressive cone: `F x ≤ᵀ x` on every branch.
  (Slaman–Steel build the coordinated tree above the regressive cone base, so
  every branch witnesses regressivity.) -/
  regressive_branch : ∀ x, tree.mem x → F x ≤ₜ x

/-- **The open core, step 1.**  Every invariant, regressive, non-constant `F`
admits a regressive uniform tree.  This is the determinacy-plus-uniformization
crux of Slaman–Steel; bracketed here as a named hypothesis and left OPEN.  (The
non-constancy is essential: a constant `F` has no injective coordinated tree.) -/
def HasRegressiveUniformTree : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Regressive F →
    ¬ ConstantOnCone F → Nonempty (RegressiveUniformTree F)

/-! ### `F` computable and injective on branches ⟹ branches recover from `F` -/

/-- `F` restricted to the branches is a computable functional (its single code is
`T.code`). -/
theorem compFunctionalOn_of_tree (T : RegressiveUniformTree F) :
    CompFunctionalOn T.tree.mem F :=
  ⟨T.code, T.computes⟩

/-- **`PPT.recover` on a regressive uniform tree.**  Since `F` is computable and
injective on the branches, every branch `x` is computed from `F x` together with
the tree code: `x ≤ᵀ F x ⊕ T.code`. -/
theorem branch_recover (T : RegressiveUniformTree F) {x : ℕ → Bool}
    (hx : T.tree.mem x) : x ≤ₜ Cantor.join (F x) T.tree.code :=
  T.tree.recover F (compFunctionalOn_of_tree T) T.injective x hx

/-! ### Step 2: domination on the branches -/

/-- A total function `g : ℕ → ℕ` is **computable from the real `x`** if a single
oracle code, run with oracle `x`, computes `g` (as a partial function that is
everywhere defined).  This is the "`g ≤ᵀ x`" used in the domination step. -/
def FunRelTo (g : ℕ → ℕ) (x : ℕ → Bool) : Prop :=
  ∃ c : ℕ, eval (toPFun x) (ofNatCode c) = fun n => Part.some (g n)

/-- **Step 2 (domination).**  On the branches of a regressive uniform tree, every
function `≤ᵀ x` is dominated by a function `≤ᵀ F x`.  The Slaman–Steel content:
if some `x`-computable function outgrew every `F x`-computable one, `x` (which
computes `Φ_e^x = F x`) could diagonalize against `F x`, contradicting
`F x = Φ_e^x`.  Bracketed as a named hypothesis; a hard step of the argument.

Concretely: for every `g ≤ᵀ x` there is `h ≤ᵀ F x` eventually dominating `g`.
We phrase domination abstractly through an opaque `Dominates` relation so the
statement does not commit to a particular growth encoding; the coding lemma
(`BranchCoding`) is the only consumer. -/
def BranchDomination (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : RegressiveUniformTree F, ∀ x, T.tree.mem x →
    ∀ g : ℕ → ℕ, FunRelTo g x → ∃ h : ℕ → ℕ, FunRelTo h (F x) ∧ Dominates h g

/-! ### Step 3: coding the bits of `x` into growth rates -/

/-- The conclusion of step 3, packaged for the assembly: **on the branches, the
input reduces to its image**, `x ≤ᵀ F x`.  Everything downstream of the coding
argument depends only on this. -/
def BranchAboveId (T : RegressiveUniformTree F) : Prop :=
  ∀ x, T.tree.mem x → x ≤ₜ F x

/-- **Step 3 (coding), as an implication.**  Given the coordinated tree and the
branch domination of step 2, the coding argument (encode the bits of `x` into the
relative growth rates of two fast-growing `F x`-computable functions) yields
`x ≤ᵀ F x` on the branches.  Bracketed as a named `Prop`: it is exactly "step 2
⟹ step 3's conclusion", so composing it with `BranchDomination` closes the hard
part modulo step 1. -/
def BranchCoding (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  BranchDomination Dominates →
    ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : RegressiveUniformTree F, BranchAboveId T

/-! ### The assembly (fully proved) -/

/-- **Branchwise equivalence.**  On the branches of a regressive uniform tree, the
coding conclusion `x ≤ᵀ F x` and the tree's regressivity `F x ≤ᵀ x` combine to
`F x ≡ᵀ x`. -/
theorem branchEquiv_of_regressive (T : RegressiveUniformTree F)
    (hcode : BranchAboveId T) {x : ℕ → Bool} (hx : T.tree.mem x) : F x ≡ₜ x :=
  ⟨T.regressive_branch x hx, hcode x hx⟩

/-- **Step 3 ⟹ the cone (the step-3⟹cone logic).**  If, on the branches of a
regressive uniform tree, `x ≤ᵀ F x` (the coding conclusion), then `F` is above the
identity on a cone.  This is where `PPT.realizes` does its work: every degree
above the tree code is realized by a branch, and Turing invariance transports the
branchwise `x ≤ᵀ F x` to that degree. -/
theorem aboveId_of_branchAboveId (hF : TuringInvariant F)
    (T : RegressiveUniformTree F) (hcode : BranchAboveId T) : AboveIdOnCone F := by
  refine ⟨T.tree.code, fun d hd => ?_⟩
  -- realize `d` by an equivalent branch `x ≡ᵀ d`
  obtain ⟨x, hxmem, hxd⟩ := T.tree.realizes d hd
  -- coding: on the branch, `x ≤ᵀ F x`
  have hx_Fx : x ≤ₜ F x := hcode x hxmem
  -- transport `x ≤ᵀ F x` across `x ≡ᵀ d` by invariance: `d ≤ᵀ F d`
  exact hxd.2.trans (hx_Fx.trans (hF x d hxd).1)

/-- **Branchwise equivalence lifts to Martin equivalence with the identity.**  On
a cone, `F X ≡ᵀ X`; i.e. `F` is Martin-equivalent to the identity.  (A stronger
statement than `AboveIdOnCone`, using regressivity on the branches too.) -/
theorem martinEquivId_of_branchAboveId (hF : TuringInvariant F)
    (T : RegressiveUniformTree F) (hcode : BranchAboveId T) :
    MartinEquiv F (fun X => X) := by
  refine ⟨T.tree.code, fun d hd => ?_⟩
  obtain ⟨x, hxmem, hxd⟩ := T.tree.realizes d hd
  have hFx_x : F x ≡ₜ x := branchEquiv_of_regressive T hcode hxmem
  -- transport `F x ≡ᵀ x ≡ᵀ d` by invariance to `F d ≡ᵀ d`
  exact ((hF x d hxd).symm.trans hFx_x).trans hxd

/-- **Step 2 ⟹ step 3's conclusion, composed.**  Domination on the branches
(step 2) feeds the coding argument (step 3) to yield `x ≤ᵀ F x` on the branches.
This is precisely the bracketed implication `BranchCoding`. -/
theorem branchAboveId_of_domination {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hcoding : BranchCoding Dominates) (hdom : BranchDomination Dominates)
    (T : RegressiveUniformTree F) : BranchAboveId T :=
  hcoding hdom F T

/-- **The full assembly.**  From the three Slaman–Steel ingredients —
* step 1: every invariant, regressive, non-constant `F` has a coordinated tree
  (`HasRegressiveUniformTree`);
* step 2: domination on the branches (`BranchDomination`);
* step 3: coding turns domination into `x ≤ᵀ F x` on the branches
  (`BranchCoding`) —
the regressive Slaman–Steel dichotomy follows: a regressive invariant `F` is
constant on a cone or above the identity on a cone.  (When non-constant, steps
1–3 place it above the identity; combined with regressivity it is in fact
equivalent to the identity, `martinEquivId_of_branchAboveId`.) -/
theorem regressiveSlamanSteel_of_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasRegressiveUniformTree)
    (hdom : BranchDomination Dominates) (hcoding : BranchCoding Dominates) :
    RegressiveSlamanSteel := by
  intro F hF hreg
  by_cases hnc : ConstantOnCone F
  · exact Or.inl hnc
  · obtain ⟨T⟩ := hTree F hF hreg hnc
    have hcode : BranchAboveId T := branchAboveId_of_domination hcoding hdom T
    exact Or.inr (aboveId_of_branchAboveId hF T hcode)

/-! ### Discharging the open core of `Reduction.lean`

`Reduction.lean` already contains `RegressiveSlamanSteel` (as a named KNOWN theorem/hypothesis),
`regressiveImpliesConstant_of_slamanSteel`, and `partI_of_slamanSteel_incomparable`.  The assembly
`regressiveSlamanSteel_of_cores` above concludes exactly that `Reduction.RegressiveSlamanSteel`
(`Regressive` is defeq to its `OnCone (fun X => F X ≤ᵀ X)` hypothesis, `regressive_eq_reductionHyp`),
so the three S-S ingredients compose with the existing reduction to discharge the regressive core. -/

/-- **The three Slaman–Steel ingredients discharge the regressive open core** of `Reduction.lean`.
Composing the assembly with `regressiveImpliesConstant_of_slamanSteel`: step 1 (coordinated tree) +
step 2 (branch domination) + step 3 (branch coding) prove `RegressiveImpliesConstant` outright.  So a
proof of just steps 1–3 removes the regressive core entirely, leaving (via
`Reduction.partI_of_slamanSteel_incomparable`) the incomparable core as the sole open content of Part I. -/
theorem regressiveImpliesConstant_of_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasRegressiveUniformTree)
    (hdom : BranchDomination Dominates) (hcoding : BranchCoding Dominates) :
    RegressiveImpliesConstant :=
  regressiveImpliesConstant_of_slamanSteel (regressiveSlamanSteel_of_cores hTree hdom hcoding)

#print axioms branchEquiv_of_regressive
#print axioms aboveId_of_branchAboveId
#print axioms martinEquivId_of_branchAboveId
#print axioms regressiveSlamanSteel_of_cores
#print axioms regressiveImpliesConstant_of_cores

end Martin
