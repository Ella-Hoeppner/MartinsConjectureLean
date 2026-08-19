/-
**The measure-preserving framework** for Part 1 of Martin's conjecture
(Lutz–Siskind, *Part 1 of Martin's Conjecture for order-preserving and
measure-preserving functions*, JAMS 2025; arXiv:2305.19646).

Lutz–Siskind restructure Part 1 around the class of **measure-preserving**
functions.  Their central theorem is that a Turing-invariant measure-preserving
function is above the identity on a cone; combined with "non-trivial ⟹
measure-preserving" for a class, this gives Part 1 for that class.

This file formalizes the framework and the parts provable with the cone
theorem + Martin measure infrastructure already in this project:

* `MeasurePreserving`, `measurePreserving_iff_martinAbove` (Prop 1.8);
* `not_measurePreserving_of_constant`, `aboveId_not_constant` — the
  measure-preserving / constant dichotomy at the two ends;
* `aboveId_measurePreserving` — every above-identity function is
  measure-preserving (so the class-specific work is exactly the *converse*);
* `IncreasingModulus`, `measurePreserving_hasModulus` (Lemma 3.3, via choice —
  the on-a-cone statement needs no Borel uniformization), and
  `aboveId_of_modulus_fixed` (the modulus argument once it has a degree fixed
  point);
* `partI_of_measurePreserving` — **the restructuring**: Part 1 follows from
  (a) `MeasurePreservingAboveId` (Lutz–Siskind Thm 3.4, the pointed-perfect-tree
  content, isolated here) and (b) "non-constant ⟹ measure-preserving".
-/
import MartinsConjecture.BoundedCase

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **Definition 1.7 (measure-preserving).**  A function `F` is measure-preserving
if it eventually gets above every degree: for every `a` there is a cone (base `b`)
on which `a ≤ᵀ F X`. -/
def MeasurePreserving (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ a : ℕ → Bool, ∃ b : ℕ → Bool, ∀ X, b ≤ₜ X → a ≤ₜ F X

/-- **Proposition 1.8.**  `F` is measure-preserving iff it is Martin-above every
constant function. -/
theorem measurePreserving_iff_martinAbove :
    MeasurePreserving F ↔ ∀ c : ℕ → Bool, MartinLE (fun _ => c) F :=
  Iff.rfl

/-- A constant function is *not* measure-preserving: it cannot get above its own
jump. -/
theorem not_measurePreserving_of_constant (hc : ConstantOnCone F) :
    ¬ MeasurePreserving F := by
  obtain ⟨c, w, hcw⟩ := hc
  intro hmp
  obtain ⟨b, hb⟩ := hmp (Cantor.jump c)
  have hwX : w ≤ₜ Cantor.join w b := Cantor.left_le_join w b
  have hbX : b ≤ₜ Cantor.join w b := Cantor.right_le_join w b
  exact Cantor.not_jump_le c ((hb _ hbX).trans (hcw _ hwX).1)

/-- Dually, an above-the-identity function is *not* constant on a cone. -/
theorem aboveId_not_constant (hai : AboveIdOnCone F) : ¬ ConstantOnCone F := by
  rintro ⟨c, w2, hcw⟩
  obtain ⟨w1, hw1⟩ := hai
  set X := Cantor.join (Cantor.join w1 w2) (Cantor.jump c) with hXdef
  have hw1X : w1 ≤ₜ X := (Cantor.left_le_join w1 w2).trans (Cantor.left_le_join _ _)
  have hw2X : w2 ≤ₜ X := (Cantor.right_le_join w1 w2).trans (Cantor.left_le_join _ _)
  have hjcX : Cantor.jump c ≤ₜ X := Cantor.right_le_join _ _
  exact Cantor.not_jump_le c (hjcX.trans ((hw1 X hw1X).trans (hcw X hw2X).1))

/-- Every above-the-identity function is measure-preserving.  (So Part 1's real
content — "non-constant ⟹ measure-preserving" — is the *converse* on each
class.) -/
theorem aboveId_measurePreserving (hai : AboveIdOnCone F) : MeasurePreserving F := by
  obtain ⟨w1, hw1⟩ := hai
  intro a
  refine ⟨Cantor.join w1 a, fun X hX => ?_⟩
  exact (Cantor.right_le_join w1 a).trans hX
    |>.trans (hw1 X ((Cantor.left_le_join w1 a).trans hX))

/-- **Definition 3.2 (increasing modulus).**  `g` is an increasing modulus for
`F` if `X ≤ᵀ g X` and whenever `Y ≥ᵀ g X`, `F Y` computes `X`. -/
def IncreasingModulus (F g : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  (∀ X, X ≤ₜ g X) ∧ (∀ X Y, g X ≤ₜ Y → X ≤ₜ F Y)

/-- **Lemma 3.3.**  A measure-preserving function has an increasing modulus.  The
*on-a-cone* form needs no Borel uniformization — choice suffices (`g X = X ⊕ bₓ`
for a cone base `bₓ` witnessing measure-preservation at `a = X`). -/
theorem measurePreserving_hasModulus (hmp : MeasurePreserving F) :
    ∃ g, IncreasingModulus F g := by
  choose b hb using hmp
  refine ⟨fun X => Cantor.join X (b X), fun X => Cantor.left_le_join X (b X), ?_⟩
  intro X Y hXY
  exact hb X Y ((Cantor.right_le_join X (b X)).trans hXY)

/-- If an increasing modulus has a degree fixed point on a cone (`g X ≡ᵀ X`),
then `F` is above the identity there. -/
theorem aboveId_of_modulus_fixed {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : IncreasingModulus F g) (hfix : OnCone (fun X => g X ≤ₜ X)) :
    AboveIdOnCone F := by
  obtain ⟨w, hw⟩ := hfix
  exact ⟨w, fun X hX => hg.2 X X (hw X hX)⟩

/-- **Lutz–Siskind Theorem 3.4** (isolated): a Turing-invariant measure-preserving
function is above the identity on a cone.  The proof (not formalized here) takes
an increasing modulus, inverts it on a *pointed perfect tree* (Cor 2.6), and
codes the branch into `F` (Lemma 2.2 — the Groszek–Slaman pointed coding).  This
`Prop` isolates exactly that content. -/
def MeasurePreservingAboveId : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → MeasurePreserving F → AboveIdOnCone F

/-- **The restructuring of Part 1** (Lutz–Siskind): Part 1 of Martin's conjecture
holds provided (a) measure-preserving functions are above the identity
(`MeasurePreservingAboveId`, their Thm 3.4) and (b) every non-constant invariant
function is measure-preserving (the class-specific content — known for
order-preserving and, via this project, for uniformly-invariant functions). -/
theorem partI_of_measurePreserving (hmpai : MeasurePreservingAboveId)
    (hclass : ∀ F, TuringInvariant F → ¬ ConstantOnCone F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F := by
  intro F hF
  by_cases hc : ConstantOnCone F
  · exact Or.inl hc
  · exact Or.inr (hmpai F hF (hclass F hF hc))

/-- Conversely, the "non-constant ⟹ measure-preserving" hypothesis is *necessary*
for Part 1: if Part 1 holds then every non-constant invariant function is
measure-preserving (being above the identity). -/
theorem measurePreserving_of_partI
    (hpartI : ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) : MeasurePreserving F :=
  aboveId_measurePreserving ((hpartI F hF).resolve_left hnc)

#print axioms not_measurePreserving_of_constant
#print axioms measurePreserving_hasModulus
#print axioms partI_of_measurePreserving

end Martin
