/-
**The arithmetic-degrees Slaman–Steel argument, as a clean skeleton.**

`IncomparableArithReduction.lean` reduces one of the four jump-distance sub-cases of the sole open
Part-1 core (`AnBm`) to the *arithmetic-degrees* regressive theorem
`StrictArithRegressiveConstant`: a Turing-invariant `F` with `F X <ₐ X` on a cone — i.e.
`F X ≤ₐ X` (`∃k, F X ≤ᵀ X^(k)`) but `X ≰ₐ F X` (`∀m, X ≰ᵀ (F X)^(m)`) — is constant on a cone.

This file structures the (relativized) Slaman–Steel proof of `StrictArithRegressiveConstant`,
mirroring `RegressiveSkeleton.lean` (the *Turing* version), **relativizing everything to the `k`-th
jump `x^(k)`** and adjusting the step-3 conclusion.

The Slaman–Steel argument, for an invariant `F` with `F X ≤ᵀ X^(k)` (fixed `k`) and `X ≰ₐ F X` that
is **non-constant**, runs in three steps:

1. **Coordinated tree (relative to the `k`-th jump).**  Determinacy yields a pointed perfect tree
   `T` on which `F` is *uniformly computed from the `k`-th jump of the branch by a single code*: a
   numeral `e` with `F x = Φ_e^{x^(k)}` for every branch `x`, and `F` injective on branches.  This is
   STRONGER than plain `MartinPPT` — the tree is coordinated with `F`'s code *at the k-th jump*.
   Modelled as the structure `ArithRegressiveUniformTree` and the existence `Prop`
   `HasArithRegressiveUniformTree`; **the genuinely-hard open core**.

2. **Domination (relative to `x^(k)`).**  For a branch `x`, every function `≤ᵀ x` is dominated by a
   function `≤ᵀ F x` — else `x^(k)` (which computes `F x = Φ_e^{x^(k)}`) diagonalizes against `F x`.
   Bracketed as `ArithBranchDomination`.

3. **Coding ⟹ `x ≤ᵀ F x`.**  The growth-rate coding gives `x ≤ᵀ F x` on the branches.  Bracketed as
   `ArithBranchCoding`; its conclusion (`ArithBranchAboveId`) is `x ≤ᵀ F x` on branches.

**The step-3 twist (the AnBm contradiction).**  Unlike the Turing case — where step 3's `x ≤ᵀ F x`
combines with regressivity to give `F ≡ᵀ id`, placing `F` above the identity — here every branch also
satisfies `X ≰ₐ F X`, i.e. `¬ ∃n, x ≤ᵀ (F x)^(n)`; taking `n = 0` this is `x ≰ᵀ F x`.  So step 3's
`x ≤ᵀ F x` on a branch is a **contradiction**.  Hence the non-constant case is *vacuous*: no
coordinated tree can exist, so `F` is constant on a cone.  This is exactly why the arithmetic-regressive
theorem concludes *constancy* rather than *above-identity*.

**What is proved here (sorry-free):**

* `arith_strict_branch` — on branches, `X ≰ₐ F X` specializes (at `n = 0`) to `x ≰ᵀ F x`;
* `arithBranchAboveId_absurd` — step 3's `x ≤ᵀ F x` on a branch contradicts branch-strictness;
* `arithBranchAboveId_of_domination` — step 2 ⟹ step 3's conclusion, bracketed as an implication so
  the two hard steps compose;
* `arithRegressive_of_cores` — **the full assembly**: the coordinated tree (step 1) + domination
  (step 2) + coding (step 3) ⟹ `StrictArithRegressiveConstant` (the non-constant case is refuted);
* the composition into the three-sub-case reduction and Part 1.

The two hard steps (1 and 2) are isolated as explicit named `Prop`s and marked open; everything
downstream is machine-checked.  No `sorry`, no new axioms.

**Honest assessment of the relativization.**  The relativization to `x^(k)` is *clean at the skeleton
level*: the tree carries `k` and the code computes from `x^(k)`; steps 2–3 are bracketed and their
statements are the verbatim relativizations of the Turing ones.  The one genuine structural difference
is step 3's conclusion, which flips from "above id" to "vacuous by contradiction" — and that flip is
proved here in full.  The recovery machinery (`PPT.recover`, which computes `x` from `F x` and the tree
code *directly from `x`*) does NOT relativize to computing `F x` from `x^(k)`; but — exactly as in the
Turing template — `recover` is not consumed by the assembly (it justifies the bracketed step-3 coding),
so this does not obstruct the skeleton.  See the note at `ArithRegressiveUniformTree`.
-/
import MartinsConjecture.MartinTree
import MartinsConjecture.IncomparableArithReduction

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! ### The strict-arithmetic-regressive predicate and the target theorem

`StrictArithRegressiveConstant` is defined in `IncomparableArithReduction.lean` as

  `∀ F, TuringInvariant F → OnCone (fun X => arithLe (F X) X ∧ ¬ arithLe X (F X)) → ConstantOnCone F`.

We introduce a name for the cone hypothesis (`StrictArithRegressive`) and record that the target is
defeq to consuming exactly it. -/

/-- `F` is **strictly arithmetically regressive** on a cone: `F X ≤ₐ X` but `X ≰ₐ F X`, i.e.
`F X` is arithmetically strictly below `X`. -/
def StrictArithRegressive (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  OnCone (fun X => arithLe (F X) X ∧ ¬ arithLe X (F X))

/-- Sanity: `StrictArithRegressiveConstant` says exactly "invariant + `StrictArithRegressive` ⟹
constant". -/
theorem strictArithRegressiveConstant_eq :
    StrictArithRegressiveConstant =
      ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → StrictArithRegressive F →
        ConstantOnCone F := rfl

/-! ### Step 1: the coordinated pointed perfect tree, relative to the `k`-th jump (the crux) -/

/-- **Step 1 (the crux), relativized to the `k`-th jump.**  An **arithmetic-regressive uniform tree**
for `F` bundles a pointed perfect tree `T`, a fixed jump level `k`, and a single oracle code `e` that
computes `F` on every branch *from the `k`-th jump of the branch*, together with the injectivity of `F`
on the branches and the branch-strictness `X ≰ₐ F X`.  This is the Slaman–Steel "coordinated tree",
relativized: it is strictly stronger than `MartinPPT`, which only supplies a tree inside a cofinal set,
not one on which `F` is uniformly computed from `x^(k)` and injective.

The data are exactly what steps 2–3 consume:
* `level` — the fixed jump level `k` (from the `Bm` hypothesis `F X ≤ᵀ X^(k)`);
* `computes` — `F x = Φ_e^{x^(k)}` for branches (a *single* code, run against the `k`-th jump of the
  branch — the relativized uniformization coordinated with the tree);
* `injective` — `F` is injective on the branches;
* `regressive_branch` — `F x ≤ᵀ x^(k)` on branches (`F X ≤ₐ X`, the `Bm` half);
* `strict_branch` — `X ≰ₐ F X` on branches (the `An` half); this is what flips step 3 to a
  contradiction.

**Note on recovery / relativization.**  In the Turing template the recovery lemma `PPT.recover`
computes `x` from `F x` and the tree code *using `x` as oracle*.  Here `F x` is computed from `x^(k)`,
not from `x`, so `computes` is NOT of the form `CompFunctionalOn T.mem F` and `PPT.recover` does not
apply verbatim.  This does not obstruct the skeleton: `recover` is used only to *justify* the bracketed
step-3 coding (which is opaque here), never by the assembly.  We therefore do not attempt a relativized
`recover`; the injectivity field is kept because the (bracketed) coding argument needs it. -/
structure ArithRegressiveUniformTree (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The underlying pointed perfect tree. -/
  tree : PPT
  /-- The fixed jump level `k` (`F X ≤ᵀ X^(k)`). -/
  level : ℕ
  /-- The oracle code that computes `F` on the branches *from their `k`-th jump*. -/
  code : ℕ
  /-- A single code computes `F` on every branch, run against the `k`-th jump of the branch:
  `F x = Φ_e^{x^(k)}`. -/
  computes : ∀ x, tree.mem x →
    eval (toPFun (Cantor.jump^[level] x)) (ofNatCode code) = toPFun (F x)
  /-- `F` is injective on the branches. -/
  injective : ∀ x y, tree.mem x → tree.mem y → F x = F y → x = y
  /-- The tree lives inside the `Bm` cone: `F x ≤ᵀ x^(k)` on every branch (`F X ≤ₐ X`). -/
  regressive_branch : ∀ x, tree.mem x → F x ≤ₜ Cantor.jump^[level] x
  /-- The tree lives inside the `An` cone: `X ≰ₐ F X` on every branch. -/
  strict_branch : ∀ x, tree.mem x → ¬ arithLe x (F x)

/-- **The open core, step 1.**  Every invariant, strictly-arithmetically-regressive, non-constant `F`
admits an arithmetic-regressive uniform tree.  This is the (relativized) determinacy-plus-uniformization
crux of Slaman–Steel; bracketed here as a named hypothesis and left OPEN.  (The non-constancy is
essential: a constant `F` has no injective coordinated tree.) -/
def HasArithRegressiveUniformTree : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → StrictArithRegressive F →
    ¬ ConstantOnCone F → Nonempty (ArithRegressiveUniformTree F)

/-! ### Consequences of the tree data on branches -/

/-- **Branch strictness at level 0.**  On a branch, `X ≰ₐ F X` (`¬ ∃n, x ≤ᵀ (F x)^(n)`) specializes at
`n = 0` to the raw `x ≰ᵀ F x`.  (`arithLe x (F x)` is `∃n, x ≤ᵀ jump^[n] (F x)`, and `jump^[0]` is the
identity, so `x ≤ᵀ F x` gives `arithLe x (F x)` via `arithLe_of_le`.) -/
theorem arith_strict_branch (T : ArithRegressiveUniformTree F) {x : ℕ → Bool}
    (hx : T.tree.mem x) : ¬ x ≤ₜ F x :=
  fun hle => T.strict_branch x hx (arithLe_of_le hle)

/-! ### Step 2: domination on the branches, relative to `x^(k)` -/

/-- A total function `g : ℕ → ℕ` is **computable from the real `x`** if a single oracle code, run with
oracle `x`, computes `g`.  (Same as the Turing template's `FunRelTo`; the relativization to `x^(k)`
lives in the tree's `computes`, so the domination step itself is phrased with the ambient reals `x` and
`F x`.) -/
def ArithFunRelTo (g : ℕ → ℕ) (x : ℕ → Bool) : Prop :=
  ∃ c : ℕ, eval (toPFun x) (ofNatCode c) = fun n => Part.some (g n)

/-- **Step 2 (domination), relativized to `x^(k)`.**  On the branches of an arithmetic-regressive
uniform tree, every function `≤ᵀ x` is dominated by a function `≤ᵀ F x`.  The Slaman–Steel content,
relativized: if some `x`-computable function outgrew every `F x`-computable one, then `x^(k)` — which
computes `Φ_e^{x^(k)} = F x` — could diagonalize against `F x`, contradicting `F x = Φ_e^{x^(k)}`.
Bracketed as a named hypothesis; a hard step of the argument.

Concretely: for every `g ≤ᵀ x` there is `h ≤ᵀ F x` eventually dominating `g`.  Domination is phrased
through an opaque `Dominates` relation so the statement does not commit to a growth encoding; the coding
lemma (`ArithBranchCoding`) is the only consumer. -/
def ArithBranchDomination (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : ArithRegressiveUniformTree F, ∀ x, T.tree.mem x →
    ∀ g : ℕ → ℕ, ArithFunRelTo g x → ∃ h : ℕ → ℕ, ArithFunRelTo h (F x) ∧ Dominates h g

/-! ### Step 3: coding the bits of `x` into growth rates -/

/-- The conclusion of step 3: **on the branches, the input reduces to its image**, `x ≤ᵀ F x`.  In the
arithmetic case this is a *contradiction* with branch-strictness (`arith_strict_branch`); the assembly
consumes exactly this contradiction. -/
def ArithBranchAboveId (T : ArithRegressiveUniformTree F) : Prop :=
  ∀ x, T.tree.mem x → x ≤ₜ F x

/-- **Step 3 (coding), as an implication.**  Given the coordinated tree (relative to `x^(k)`) and the
branch domination of step 2, the coding argument (encode the bits of `x` into the relative growth rates
of two fast-growing `F x`-computable functions) yields `x ≤ᵀ F x` on the branches.  Bracketed as a
named `Prop`: it is exactly "step 2 ⟹ step 3's conclusion", so composing it with
`ArithBranchDomination` closes the hard part modulo step 1. -/
def ArithBranchCoding (Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ArithBranchDomination Dominates →
    ∀ F : (ℕ → Bool) → ℕ → Bool, ∀ T : ArithRegressiveUniformTree F, ArithBranchAboveId T

/-! ### The assembly (fully proved) -/

/-- **The step-3 contradiction.**  On a branch, step 3's conclusion `x ≤ᵀ F x` contradicts the
branch-strictness `X ≰ₐ F X`.  So *any* branch of an arithmetic-regressive uniform tree witnessing the
coding conclusion is impossible.  This is the arithmetic analogue's key structural difference from the
Turing case: the coding conclusion is not "above id" but an outright contradiction. -/
theorem arithBranchAboveId_absurd (T : ArithRegressiveUniformTree F)
    (hcode : ArithBranchAboveId T) {x : ℕ → Bool} (hx : T.tree.mem x) : False :=
  arith_strict_branch T hx (hcode x hx)

/-- **A tree yields a branch.**  Every pointed perfect tree realizes a branch (namely one equivalent to
its own code, which is above itself).  Used to derive the contradiction from a coordinated tree. -/
theorem tree_has_branch (T : ArithRegressiveUniformTree F) :
    ∃ x, T.tree.mem x :=
  let ⟨x, hxmem, _⟩ := T.tree.realizes T.tree.code (Cantor.le.refl _)
  ⟨x, hxmem⟩

/-- **The coordinated tree + coding refute non-constancy.**  If `F` had an arithmetic-regressive uniform
tree (step 1) whose branches satisfy the coding conclusion (step 3), we could pick a branch and derive
`False` (via `arithBranchAboveId_absurd`).  So no such tree exists — which, since step 1 supplies one
whenever `F` is non-constant, means `F` must be constant on a cone. -/
theorem not_hasTree_of_coding
    (T : ArithRegressiveUniformTree F) (hcode : ArithBranchAboveId T) : False :=
  let ⟨_, hx⟩ := tree_has_branch T
  arithBranchAboveId_absurd T hcode hx

/-- **Step 2 ⟹ step 3's conclusion, composed.**  Domination on the branches (step 2) feeds the coding
argument (step 3) to yield `x ≤ᵀ F x` on the branches.  This is precisely the bracketed implication
`ArithBranchCoding`. -/
theorem arithBranchAboveId_of_domination {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hcoding : ArithBranchCoding Dominates) (hdom : ArithBranchDomination Dominates)
    (T : ArithRegressiveUniformTree F) : ArithBranchAboveId T :=
  hcoding hdom F T

/-- **The full assembly.**  From the three (relativized) Slaman–Steel ingredients —
* step 1: every invariant, strictly-arithmetically-regressive, non-constant `F` has a coordinated tree
  computing `F` from `x^(k)` (`HasArithRegressiveUniformTree`);
* step 2: domination on the branches (`ArithBranchDomination`);
* step 3: coding turns domination into `x ≤ᵀ F x` on the branches (`ArithBranchCoding`) —
the arithmetic-regressive theorem `StrictArithRegressiveConstant` follows.  The mechanism: in the
non-constant case, step 1 supplies a coordinated tree, steps 2–3 give `x ≤ᵀ F x` on a branch, and that
*contradicts* branch-strictness `X ≰ₐ F X` — so the non-constant case is vacuous, forcing constancy. -/
theorem arithRegressive_of_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasArithRegressiveUniformTree)
    (hdom : ArithBranchDomination Dominates) (hcoding : ArithBranchCoding Dominates) :
    StrictArithRegressiveConstant := by
  intro F hF hreg
  by_contra hnc
  -- step 1: non-constancy yields a coordinated tree
  obtain ⟨T⟩ := hTree F hF hreg hnc
  -- steps 2+3: the branches satisfy `x ≤ᵀ F x`
  have hcode : ArithBranchAboveId T := arithBranchAboveId_of_domination hcoding hdom T
  -- contradiction with branch-strictness
  exact not_hasTree_of_coding T hcode

/-! ### Discharging the `AnBm` sub-case and Part 1

`IncomparableArithReduction.lean` already contains `StrictArithRegressiveConstant`,
`incomparable_AnBm_of_strictArithRegressive` (which uses it to close the `AnBm` sub-case),
`incomparableCore_of_three_cases_and_arith`, and `partI_of_three_cases_and_arith`.  The assembly
`arithRegressive_of_cores` above concludes exactly that (existing) `StrictArithRegressiveConstant`, so
the three (relativized) S-S ingredients compose with the existing reduction. -/

/-- **The three (relativized) Slaman–Steel ingredients discharge the `AnBm` sub-case.**  Composing the
assembly with `incomparable_AnBm_of_strictArithRegressive`: steps 1–3 prove `StrictArithRegressiveConstant`,
which subsumes the `AnBm` jump-distance sub-case of the sole open Part-1 core. -/
theorem incomparable_AnBm_of_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTree : HasArithRegressiveUniformTree)
    (hdom : ArithBranchDomination Dominates) (hcoding : ArithBranchCoding Dominates)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : TuringInvariant F)
    (hAn : OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (F X)))
    (hBm : ∃ k, OnCone (fun X => F X ≤ₜ Cantor.jump^[k] X)) : ConstantOnCone F :=
  incomparable_AnBm_of_strictArithRegressive
    (arithRegressive_of_cores hTree hdom hcoding) F hF hAn hBm

/-- **The incomparable core reduces to THREE sub-cases, given the three arithmetic S-S ingredients.**
The `AnBm` sub-case is discharged by `arithRegressive_of_cores`; the remaining `AnAm`, `BnAm`, `BnBm`
sub-cases are the residual open content. -/
theorem incomparableCore_of_three_cases_and_cores {Dominates : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hTD : TuringDeterminacy fun _ => True)
    (hTree : HasArithRegressiveUniformTree)
    (hdom : ArithBranchDomination Dominates) (hcoding : ArithBranchCoding Dominates)
    (hAnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (G X)) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnBm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G) :
    IncomparableConstant :=
  incomparableCore_of_three_cases_and_arith hTD
    (arithRegressive_of_cores hTree hdom hcoding) hAnAm hBnAm hBnBm

#print axioms arith_strict_branch
#print axioms arithBranchAboveId_absurd
#print axioms arithBranchAboveId_of_domination
#print axioms arithRegressive_of_cores
#print axioms incomparable_AnBm_of_cores
#print axioms incomparableCore_of_three_cases_and_cores

end Martin
