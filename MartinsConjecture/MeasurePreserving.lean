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
import MartinsConjecture.OrderPreservingCase

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! `MeasurePreserving` (Def 1.37) and `MeasurePreservingAboveId` (Lutz–Siskind
Thm 1.39) are already defined in `OrderPreservingCase`.  Here we develop the
*general-function* theory around them: the increasing-modulus machinery and the
exact equivalence of Part 1 with the measure-preserving decomposition. -/

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

/-- Measure-preservation is **upward closed in the Martin order**: if `F ≤ₘ G`
and `F` is measure-preserving, so is `G`. -/
theorem measurePreserving_of_martinLE {G : (ℕ → Bool) → ℕ → Bool}
    (h : MartinLE F G) (hmp : MeasurePreserving F) : MeasurePreserving G := by
  obtain ⟨w1, hw1⟩ := h
  intro a
  obtain ⟨ba, hba⟩ := hmp a
  exact ⟨Cantor.join ba w1, fun X hX =>
    (hba X ((Cantor.left_le_join ba w1).trans hX)).trans
      (hw1 X ((Cantor.right_le_join ba w1).trans hX))⟩

/-- Measure-preserving functions are **closed under composition**. -/
theorem measurePreserving_comp {G : (ℕ → Bool) → ℕ → Bool}
    (hf : MeasurePreserving F) (hg : MeasurePreserving G) :
    MeasurePreserving (fun X => F (G X)) := by
  intro a
  obtain ⟨bf, hbf⟩ := hf a
  obtain ⟨bg, hbg⟩ := hg bf
  exact ⟨bg, fun X hX => hbf (G X) (hbg X hX)⟩

/-- The jump is measure-preserving (a concrete non-trivial witness). -/
theorem jump_measurePreserving : MeasurePreserving (fun X => Cantor.jump X) :=
  aboveId_measurePreserving ⟨fun _ => false, fun X _ => Cantor.le_jump X⟩

/-- **Measure-preserving ⟹ escaping.**  A measure-preserving function escapes
every fixed degree on a cone (its values are not below `Z`): taking `a = Z′`
forces `F X ≥ᵀ Z′ >ᵀ Z`.  The *converse* — escaping ⟹ measure-preserving — is
exactly the open, class-specific content of Part 1 (`counterexample_escapes`
gives escaping from non-constancy; measure-preservation is the gap). -/
theorem measurePreserving_escapes (hmp : MeasurePreserving F) (Z : ℕ → Bool) :
    OnCone (fun X => ¬ F X ≤ₜ Z) := by
  obtain ⟨b, hb⟩ := hmp (Cantor.jump Z)
  exact ⟨b, fun X hX hle => Cantor.not_jump_le Z ((hb X hX).trans hle)⟩

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

/-- **Converse of Lemma 3.3: an increasing modulus forces measure-preservation.**  If `g` is an increasing
modulus for `F`, then for each `Z`, taking `X := Z` in the modulus property gives `Z ≤ᵀ F Y` whenever
`g Z ≤ᵀ Y` — i.e. `F` is above `Z` on the cone above `g Z`.  Hence **`MeasurePreserving F ⟺ F has an increasing
modulus`** (`measurePreserving_iff_hasModulus`).  This is the recursion-theoretic content behind the
2026-08-26 convergence finding: building a Marks pointed *injective* tree needs a computable injective witness,
which exists iff `F` has a modulus iff `F` is measure-preserving — so the combinatorial (Marks) and measure
routes to Part 1 bottom out at the *same* wall. -/
theorem measurePreserving_of_hasModulus {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : IncreasingModulus F g) : MeasurePreserving F :=
  fun Z => ⟨g Z, fun X hX => hg.2 Z X hX⟩

/-- **`F` is measure-preserving iff it has an increasing modulus** (Lutz–Siskind Lemma 3.3 + its converse). -/
theorem measurePreserving_iff_hasModulus :
    MeasurePreserving F ↔ ∃ g, IncreasingModulus F g :=
  ⟨measurePreserving_hasModulus, fun ⟨_, hg⟩ => measurePreserving_of_hasModulus hg⟩

/-- If an increasing modulus has a degree fixed point on a cone (`g X ≡ᵀ X`),
then `F` is above the identity there. -/
theorem aboveId_of_modulus_fixed {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : IncreasingModulus F g) (hfix : OnCone (fun X => g X ≤ₜ X)) :
    AboveIdOnCone F := by
  obtain ⟨w, hw⟩ := hfix
  exact ⟨w, fun X hX => hg.2 X X (hw X hX)⟩

/-- **Isolating what the pointed perfect tree does.**  If an increasing modulus is
*uniformly bounded* — `g X ≤ᵀ X ⊕ W` for a single fixed `W` — then `F` is above
the identity on the cone above `W`, with *no* pointed perfect tree needed.  Thus
the Groszek–Slaman tree in Lutz–Siskind Thm 3.4 is doing exactly one thing:
handling moduli whose base grows *unboundedly* with the input degree. -/
theorem aboveId_of_bounded_modulus {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : IncreasingModulus F g) {W : ℕ → Bool}
    (hbd : ∀ X, g X ≤ₜ Cantor.join X W) : AboveIdOnCone F :=
  ⟨W, fun X hX => hg.2 X X ((hbd X).trans (Cantor.join_le (Cantor.le.refl X) hX))⟩

/-- Consequently, a measure-preserving function whose modulus can be taken
uniformly bounded is above the identity — the tree-free fragment of Thm 3.4. -/
theorem measurePreserving_aboveId_of_boundedModulus (hmp : MeasurePreserving F)
    {g : (ℕ → Bool) → (ℕ → Bool)} (hg : IncreasingModulus F g) {W : ℕ → Bool}
    (hbd : ∀ X, g X ≤ₜ Cantor.join X W) : AboveIdOnCone F :=
  aboveId_of_bounded_modulus hg hbd

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

/-- Conversely, Thm 3.4 (`MeasurePreservingAboveId`) *follows* from Part 1: a
measure-preserving function is non-constant, hence above the identity. -/
theorem measurePreservingAboveId_of_partI
    (hpartI : ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) :
    MeasurePreservingAboveId := by
  intro F hF hmp
  exact (hpartI F hF).resolve_left (fun hc => not_measurePreserving_of_constant hc hmp)

/-- **Part 1 is *equivalent* to the measure-preserving decomposition.**  Part 1 of
Martin's conjecture holds iff both (a) `MeasurePreservingAboveId` (Lutz–Siskind
Thm 3.4) and (b) every non-constant invariant function is measure-preserving.
This pins down exactly the two independent "halves" of Part 1: a *general*
recursion-theoretic fact (Thm 3.4, the pointed coding) and the *class-specific*
content (non-triviality forces cofinal growth). -/
theorem partI_iff_measurePreserving :
    (∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) ↔
      (MeasurePreservingAboveId ∧
        ∀ F, TuringInvariant F → ¬ ConstantOnCone F → MeasurePreserving F) := by
  constructor
  · intro h
    exact ⟨measurePreservingAboveId_of_partI h, fun F hF hnc => measurePreserving_of_partI h hF hnc⟩
  · rintro ⟨h1, h2⟩
    exact partI_of_measurePreserving h1 h2

/-! ### Escaping: the largeness notion that coincides with non-constancy -/

/-- `F` is **escaping** if its values avoid every fixed degree on a cone: for
every `Z`, `F X ≰ᵀ Z` on a cone.  This is *weaker* than measure-preservation
(`F X ≥ᵀ a` on a cone ⟹ `F X ≱ᵀ a′`), and — the point below — coincides with
non-constancy for invariant functions. -/
def Escaping (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ Z : ℕ → Bool, OnCone (fun X => ¬ F X ≤ₜ Z)

/-- Measure-preserving functions are escaping. -/
theorem MeasurePreserving.escaping (hmp : MeasurePreserving F) : Escaping F :=
  measurePreserving_escapes hmp

/-- An escaping function is not constant on a cone (no determinacy needed —
constancy would put `F X ≤ᵀ c` on a cone, contradicting escaping at `Z = c`). -/
theorem not_constant_of_escaping (h : Escaping F) : ¬ ConstantOnCone F := by
  rintro ⟨c, hc⟩
  obtain ⟨b, hb⟩ := onCone_and (h c) hc
  exact (hb b (Cantor.le.refl b)).1 (hb b (Cantor.le.refl b)).2.1

/-- Conversely, a non-constant invariant function is escaping — this is exactly
the escape theorem (`counterexample_escapes`). -/
theorem escaping_of_not_constant (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) : Escaping F :=
  counterexample_escapes hTD hF hnc

/-- **Escaping ⟺ non-constant** for invariant functions.  So the escape theorem
is best read as: non-constancy *is* the largeness property "avoids every fixed
degree on a cone". -/
theorem escaping_iff_not_constant (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) : Escaping F ↔ ¬ ConstantOnCone F :=
  ⟨not_constant_of_escaping, escaping_of_not_constant hTD hF⟩

/-- **The open class-specific half of Part 1, sharpened.**  Given determinacy,
"every non-constant invariant function is measure-preserving" is *equivalent* to
"every escaping invariant function is measure-preserving" (since escaping and
non-constancy coincide).  Combined with `partI_iff_measurePreserving`, the entire
open content of Part 1 is: **Thm 3.4** (measure-preserving ⟹ above id) together
with **escaping ⟹ measure-preserving** — "if `F` avoids every degree from below
on a cone, it reaches every degree from above on a cone". -/
theorem nonconstant_mp_iff_escaping_mp (hTD : TuringDeterminacy fun _ => True) :
    (∀ F, TuringInvariant F → ¬ ConstantOnCone F → MeasurePreserving F) ↔
      (∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :=
  ⟨fun h F hF hesc => h F hF (not_constant_of_escaping hesc),
   fun h F hF hnc => h F hF (escaping_of_not_constant hTD hF hnc)⟩

#print axioms not_measurePreserving_of_constant
#print axioms measurePreserving_hasModulus
#print axioms partI_of_measurePreserving
#print axioms partI_iff_measurePreserving
#print axioms escaping_iff_not_constant
#print axioms nonconstant_mp_iff_escaping_mp

end Martin
