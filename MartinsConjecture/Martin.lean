/-
Formal statements of Martin's conjecture.

This file gives formal Lean statements (as named `Prop`s — none are asserted!)
of both parts of Martin's conjecture in the ZFC-well-posed **Borel** version,
plus the uniformly-invariant and order-preserving variants and Lachlan's
theorem.  Definitions follow Patrick Lutz's thesis, *Results on Martin's
Conjecture* (UC Berkeley, 2021):

* Def 1.11 (Turing invariant), Def 1.14/1.15 (Martin order/equivalence),
  Conjecture 1.24 (the conjecture), Defs 1.27–1.28 (uniform invariance:
  `x ≡_T y via (i,j)` iff `Φ_i(x) = y` and `Φ_j(y) = x`),
  Def 1.34 (order preserving), Thm 1.36 (Lutz–Siskind).

The original conjecture is stated in ZF + AD, which contradicts choice and
so MUST NOT be axiomatized in Lean/Mathlib.  Restricted to Borel functions,
each statement is well-posed in ZFC (this is the setting of the modern
partial results).  "Borel" is rendered as `Measurable` with respect to the
product σ-algebra on `ℕ → Bool`, which coincides with the Borel σ-algebra of
the Cantor-space topology (countable product of discrete spaces).

`Prewellordering` is rendered as: the Martin order is total on the class in
question, and its strict part is well-founded (both modulo nothing — the
order is a preorder, so this is the standard "prewellordering" phrasing).

To our knowledge (search of Mathlib, Zulip, and public repositories,
2026-08-13) these statements have not previously been formalized.
-/
import MartinsConjecture.CantorPoints
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Turing-invariant functions and the Martin order -/

/-- A function on Cantor space is **Turing invariant** (degree invariant) if it
maps Turing-equivalent points to Turing-equivalent points [Lutz, Def 1.11]. -/
def TuringInvariant (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ X Y, X ≡ₜ Y → F X ≡ₜ F Y

/-- A function on Cantor space is **order preserving** if it preserves Turing
reducibility [Lutz, Def 1.34]. -/
def OrderPreserving (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ X Y, X ≤ₜ Y → F X ≤ₜ F Y

/-- Sanity: order preserving implies Turing invariant. -/
theorem OrderPreserving.turingInvariant {F} (h : OrderPreserving F) :
    TuringInvariant F := fun X Y hXY => ⟨h X Y hXY.1, h Y X hXY.2⟩

/-- Turing invariance is closed under composition. -/
theorem TuringInvariant.comp {F G} (hF : TuringInvariant F) (hG : TuringInvariant G) :
    TuringInvariant (fun X => F (G X)) :=
  fun X Y hXY => hF (G X) (G Y) (hG X Y hXY)

/-- Order preservation is closed under composition. -/
theorem OrderPreserving.comp {F G} (hF : OrderPreserving F) (hG : OrderPreserving G) :
    OrderPreserving (fun X => F (G X)) :=
  fun X Y hXY => hF (G X) (G Y) (hG X Y hXY)

/-- The identity is order preserving. -/
theorem orderPreserving_id : OrderPreserving (fun X : ℕ → Bool => X) :=
  fun _ _ h => h

/-- The cone above `Y`: all points computing `Y`. -/
def cone (Y : ℕ → Bool) : Set (ℕ → Bool) := {X | Y ≤ₜ X}

/-- A property of points holds **on a cone** if it holds everywhere above some
base point.  ("On a cone" is the notion of largeness in this subject.) -/
def OnCone (P : (ℕ → Bool) → Prop) : Prop := ∃ Y, ∀ X, Y ≤ₜ X → P X

theorem onCone_mono {P Q : (ℕ → Bool) → Prop} (h : ∀ X, P X → Q X)
    (hP : OnCone P) : OnCone Q :=
  hP.imp fun _ hY X hX => h X (hY X hX)

/-- The **Martin order**: `F ≤ₘ G` iff `F X ≤ₜ G X` on a cone [Lutz, Def 1.15]. -/
def MartinLE (F G : (ℕ → Bool) → ℕ → Bool) : Prop := OnCone fun X => F X ≤ₜ G X

/-- **Martin equivalence**: Turing equivalent on a cone [Lutz, Def 1.14]. -/
def MartinEquiv (F G : (ℕ → Bool) → ℕ → Bool) : Prop := OnCone fun X => F X ≡ₜ G X

/-- Strict Martin order. -/
def MartinLT (F G : (ℕ → Bool) → ℕ → Bool) : Prop := MartinLE F G ∧ ¬ MartinLE G F

/-- The Martin order is reflexive. -/
theorem MartinLE.refl (F : (ℕ → Bool) → ℕ → Bool) : MartinLE F F :=
  ⟨fun _ => false, fun X _ => Cantor.le.refl (F X)⟩

/-- Martin equivalence is reflexive. -/
theorem MartinEquiv.refl (F : (ℕ → Bool) → ℕ → Bool) : MartinEquiv F F :=
  ⟨fun _ => false, fun X _ => Cantor.equiv.refl (F X)⟩

/-- Martin equivalence is symmetric. -/
theorem MartinEquiv.symm {F G} (h : MartinEquiv F G) : MartinEquiv G F :=
  h.imp fun _ hY X hX => (hY X hX).symm

/-- Martin equivalence implies both Martin inequalities. -/
theorem MartinEquiv.le {F G} (h : MartinEquiv F G) : MartinLE F G :=
  h.imp fun _ hY X hX => (hY X hX).1

theorem MartinEquiv.ge {F G} (h : MartinEquiv F G) : MartinLE G F :=
  h.imp fun _ hY X hX => (hY X hX).2

/-- `F` is Martin equivalent to a constant function. -/
def ConstantOnCone (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ C, MartinEquiv F (fun _ => C)

/-- `F` is Martin above the identity. -/
def AboveIdOnCone (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  OnCone fun X => X ≤ₜ F X

/-! ### Martin's conjecture, Borel version -/

/-- **Martin's conjecture, Part I, Borel version.**  Every Borel Turing
invariant function on Cantor space is either Martin equivalent to a constant
or Martin above the identity [Lutz, Conjecture 1.24(1), restricted to Borel
functions, where it is a ZFC-well-posed and still-open statement]. -/
def PartI_Borel : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, Measurable F → TuringInvariant F →
    ConstantOnCone F ∨ AboveIdOnCone F

/-- The class quantified over in Part II: Borel, Turing invariant, and Martin
above the identity. -/
def Regular (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  Measurable F ∧ TuringInvariant F ∧ AboveIdOnCone F

/-- Part II, totality half of the prewellordering claim: the Martin order is
total on regular functions. -/
def PartII_Borel_Total : Prop :=
  ∀ F G, Regular F → Regular G → MartinLE F G ∨ MartinLE G F

/-- Part II, well-foundedness half of the prewellordering claim. -/
def PartII_Borel_WF : Prop :=
  WellFounded fun F G : {F // Regular F} => MartinLT F.1 G.1

/-- Part II, successor claim: the jump is the successor operation for the
Martin order on regular functions [Lutz, Conjecture 1.24(2), "the successor
of f in this well order is the jump of f"]. -/
def PartII_Borel_Succ : Prop :=
  ∀ F, Regular F →
    MartinLT F (fun X => Cantor.jump (F X)) ∧
    ∀ G, Regular G → MartinLT F G → MartinLE (fun X => Cantor.jump (F X)) G

/-- **Martin's conjecture, Part II, Borel version**: the Martin order
prewellorders the regular functions, with the jump as successor. -/
def PartII_Borel : Prop :=
  PartII_Borel_Total ∧ PartII_Borel_WF ∧ PartII_Borel_Succ

/-- A fragment of the successor claim that is provable outright: every
function is strictly Martin-below its jump, by pointwise jump strictness.
(The other half of `PartII_Borel_Succ` — that nothing fits strictly between —
is the open part.) -/
theorem martinLT_jump (F : (ℕ → Bool) → ℕ → Bool) :
    MartinLT F (fun X => Cantor.jump (F X)) := by
  constructor
  · exact ⟨fun _ => false, fun X _ => le_jump (F X)⟩
  · rintro ⟨Y, hY⟩
    exact not_jump_le (F Y) (hY Y (le.refl Y))

/-- **Martin's conjecture, Borel version** (both parts). -/
def MartinConjecture_Borel : Prop := PartI_Borel ∧ PartII_Borel

/-! ### Uniform invariance -/

/-- `X ≡ₜ Y` **via** the pair of indices `(i, j)`: machine `i` computes `Y`
from `X` and machine `j` computes `X` from `Y` [Lutz, Def 1.27]. -/
def EquivVia (X Y : ℕ → Bool) (i j : ℕ) : Prop :=
  eval (toPFun X) (ofNatCode i) = toPFun Y ∧ eval (toPFun Y) (ofNatCode j) = toPFun X

/-- Sanity: `EquivVia` witnesses genuine Turing equivalence. -/
theorem EquivVia.equiv {X Y : ℕ → Bool} {i j : ℕ} (h : EquivVia X Y i j) : X ≡ₜ Y :=
  ⟨RecursiveIn.iff_nat.mpr (h.2 ▸ eval_recursiveIn (toPFun Y) (ofNatCode j)),
   RecursiveIn.iff_nat.mpr (h.1 ▸ eval_recursiveIn (toPFun X) (ofNatCode i))⟩

/-- `EquivVia` is symmetric in the point/index pairs. -/
theorem EquivVia.symm {X Y : ℕ → Bool} {i j : ℕ} (h : EquivVia X Y i j) :
    EquivVia Y X j i := ⟨h.2, h.1⟩

/-- `EquivVia` is reflexive, witnessed by the oracle-query code. -/
theorem EquivVia.refl (X : ℕ → Bool) :
    EquivVia X X (encodeCode .oracle) (encodeCode .oracle) := by
  refine ⟨?_, ?_⟩ <;>
    · rw [ofNatCode_encodeCode, eval_oracle]

/-- Sanity (converse): every Turing equivalence has index witnesses — this is
exactly the enumeration theorem `exists_code`. -/
theorem equiv_iff_exists_equivVia {X Y : ℕ → Bool} :
    X ≡ₜ Y ↔ ∃ i j, EquivVia X Y i j := by
  constructor
  · rintro ⟨hXY, hYX⟩
    obtain ⟨cY, hcY⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp hYX)
    obtain ⟨cX, hcX⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp hXY)
    exact ⟨encodeCode cY, encodeCode cX,
      by rw [ofNatCode_encodeCode]; exact hcY,
      by rw [ofNatCode_encodeCode]; exact hcX⟩
  · rintro ⟨i, j, h⟩
    exact h.equiv

/-- `F` is **uniformly Turing invariant** if index witnesses for `X ≡ₜ Y`
can be transformed (by some function `u`, not required to be computable) into
index witnesses for `F X ≡ₜ F Y` [Lutz, Def 1.28]. -/
def UniformlyTuringInvariant (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ u : ℕ × ℕ → ℕ × ℕ, ∀ X Y i j, EquivVia X Y i j →
    EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2

/-- Variant with a computable uniformity function (the stronger hypothesis
used in some classical papers; conventions vary — see the ledger). -/
def ComputablyUniformlyTuringInvariant (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ u : ℕ × ℕ → ℕ × ℕ, Computable u ∧ ∀ X Y i j, EquivVia X Y i j →
    EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2

/-- The computable-uniformity notion is a strengthening of uniformity. -/
theorem ComputablyUniformlyTuringInvariant.toUniformly {F}
    (h : ComputablyUniformlyTuringInvariant F) : UniformlyTuringInvariant F := by
  obtain ⟨u, -, hu⟩ := h
  exact ⟨u, hu⟩

/-- The identity is uniformly invariant (transformer = identity). -/
theorem uniformlyTuringInvariant_id :
    UniformlyTuringInvariant (fun X : ℕ → Bool => X) :=
  ⟨id, fun _ _ _ _ h => h⟩

/-- Every constant function is uniformly invariant (transformer is the
constant oracle-query witness pair). -/
theorem uniformlyTuringInvariant_const (C : ℕ → Bool) :
    UniformlyTuringInvariant (fun _ => C) :=
  ⟨fun _ => (encodeCode .oracle, encodeCode .oracle),
   fun _ _ _ _ _ => EquivVia.refl C⟩

/-- Uniform invariance is closed under composition: the transformer of the
composite is the composite of the transformers. -/
theorem UniformlyTuringInvariant.comp {F G}
    (hF : UniformlyTuringInvariant F) (hG : UniformlyTuringInvariant G) :
    UniformlyTuringInvariant (fun X => F (G X)) := by
  obtain ⟨uF, huF⟩ := hF
  obtain ⟨uG, huG⟩ := hG
  exact ⟨fun p => uF (uG p), fun X Y i j hij => huF (G X) (G Y) _ _ (huG X Y i j hij)⟩

/-- Sanity: uniform invariance implies invariance. -/
theorem UniformlyTuringInvariant.turingInvariant {F}
    (h : UniformlyTuringInvariant F) : TuringInvariant F := by
  obtain ⟨u, hu⟩ := h
  intro X Y hXY
  obtain ⟨i, j, hij⟩ := equiv_iff_exists_equivVia.mp hXY
  exact (hu X Y i j hij).equiv

/-! ### Named variants and special cases -/

/-- **Slaman–Steel (1988)**, Part I for uniformly invariant functions,
Borel version. -/
def PartI_Uniform_Borel : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, Measurable F → UniformlyTuringInvariant F →
    ConstantOnCone F ∨ AboveIdOnCone F

/-- **Lutz–Siskind (2021–24)**, Part I for order-preserving functions, Borel
version — a ZFC theorem (via Borel determinacy). -/
def PartI_OrderPreserving_Borel : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, Measurable F → OrderPreserving F →
    ConstantOnCone F ∨ AboveIdOnCone F

/-- **No uniformly-invariant solution to Post's problem**: no uniformly
invariant `F` is strictly between the identity and the jump on a cone.

Attribution note (checked against Lutz's thesis Ch. 3, 2026-08-13): Lachlan's
*original* 1975 result [Lachlan, "Uniform enumeration operations", JSL 40.3]
is stated for **r.e. operators** `W` with `Wˣ ≥ᵀ X`, as the dichotomy
`Wˣ ≡ᵀ X` on a cone or `Wˣ ≡ᵀ X′` on a cone (see `LachlanLocalStatement`).
The unrestricted version for *arbitrary* uniformly-invariant `F` below is the
strength of **Steel's 1982** "A classification of jump operators" (JSL 47.2),
of which this "no Post solution" form is the standard corollary. -/
def NoUniformPostSolution : Prop :=
  ¬ ∃ F : (ℕ → Bool) → ℕ → Bool, UniformlyTuringInvariant F ∧
      OnCone fun X => X <ₜ F X ∧ F X <ₜ Cantor.jump X

@[deprecated NoUniformPostSolution (since := "session 4: attribution")]
alias LachlanStatement := NoUniformPostSolution

/-- **Lachlan's theorem, local (per-degree) form** [Lutz thesis Cor 3.11;
after Lachlan 1975, Bard]: for an r.e.-operator-like invariant `F` that is
uniformly invariant and above the identity, on each sufficiently-high degree
`F X` is Turing equivalent to `X`, to `X′`, or `F` is constant there.  Stated
here with the "`≥ᵀ 0′` base" replaced by "on a cone" and the r.e.-operator
hypothesis abstracted to `AboveIdOnCone`.  (Not proved — see `ATTACK.md` for
the formalization plan; the core `Thm 3.10` is determinacy-free but needs
r.e.-operator infrastructure and Bard's computable-uniformity lemma.) -/
def LachlanLocalStatement : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, UniformlyTuringInvariant F → AboveIdOnCone F →
    ConstantOnCone F ∨ MartinEquiv F (fun X => X) ∨
      MartinEquiv F (fun X => Cantor.jump X)

/-- Sanity implication: full Part I specializes to the order-preserving case. -/
theorem partI_Borel_implies_orderPreserving :
    PartI_Borel → PartI_OrderPreserving_Borel :=
  fun h F hB hOP => h F hB hOP.turingInvariant

/-- Sanity implication: full Part I specializes to the uniformly invariant
case. -/
theorem partI_Borel_implies_uniform :
    PartI_Borel → PartI_Uniform_Borel :=
  fun h F hB hU => h F hB hU.turingInvariant

#print axioms equiv_iff_exists_equivVia
#print axioms partI_Borel_implies_orderPreserving

end Martin
