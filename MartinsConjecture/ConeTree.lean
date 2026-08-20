/-
**The determinacy game produces pointed perfect trees (invariant case).**

`MartinPPT'` — every cofinal set contains a pointed perfect tree — is Martin's
Lemma 2.3, the sole remaining determinacy input to the whole measure-preserving
branch of Part 1.  Its general (non-invariant) form is a deep fusion argument.
The **Turing-invariant** case, however, is provable *now* from the machinery
already in the repository:

* `cone_theorem` (`ConeTheorem.lean`) — a determined Turing-invariant set contains
  a cone or is disjoint from one.  Cofinality kills the second alternative, so an
  invariant cofinal determined set **contains a cone** `cone Y ⊆ A`.
* A cone is itself a pointed perfect tree: the reals whose even bits spell `Y`
  (`{join Y Z}`) all compute `Y` (pointed), realize every degree above `Y`
  (Prop 1.10), and lie in `cone Y ⊆ A`.  The labelling `z ↦ join Y z` is a
  `PerfectEmbedding` (`PerfectEmbedding.lean`), so `realizes` comes for free.

So the determinacy game *does* build pointed perfect trees inside invariant sets —
the pointed / realizing / perfect content of Martin's Lemma 2.3, machine-checked.
(The one field not produced here is the effective `recover` for this concrete
tree; in general that is `lemma21`, which requires the tree in the `treeMem`
coding — a separate encoding step.)
-/
import MartinsConjecture.PerfectEmbedding
import MartinsConjecture.ConeTheorem

open scoped Computability
open Cantor

namespace Martin

/-! ### A cone is a pointed perfect tree -/

/-- Branches of the **`Y`-coding tree**: reals whose even bits spell `Y`
(equivalently `join Y Z` for some `Z`). -/
def CodedBranch (Y : ℕ → Bool) : (ℕ → Bool) → Prop := fun x => ∃ Z, x = Cantor.join Y Z

/-- The labelling `z ↦ join Y z` is a degree-preserving perfect embedding of
Cantor space onto the `Y`-coding tree, with code `Y`. -/
def coneEmbedding (Y : ℕ → Bool) : PerfectEmbedding Y (CodedBranch Y) where
  emb := fun z => Cantor.join Y z
  maps_to := fun z => ⟨z, rfl⟩
  forward := fun z => Cantor.join_le (Cantor.right_le_join z Y) (Cantor.left_le_join z Y)
  invert := fun z => (Cantor.right_le_join Y z).trans (Cantor.left_le_join (Cantor.join Y z) Y)

/-- The `Y`-coding tree is **pointed**: every branch computes `Y`. -/
theorem coneEmbedding_pointed (Y : ℕ → Bool) : ∀ x, CodedBranch Y x → Y ≤ₜ x := by
  rintro x ⟨Z, rfl⟩
  exact Cantor.left_le_join Y Z

/-- **Prop 1.10 for the coding tree**: it realizes every degree above `Y`. -/
theorem coneEmbedding_realizes (Y : ℕ → Bool) :
    ∀ d, Y ≤ₜ d → ∃ x, CodedBranch Y x ∧ x ≡ₜ d :=
  realizes_of_perfectEmbedding (coneEmbedding_pointed Y) (coneEmbedding Y)

/-- The coding tree lies inside the cone above `Y`. -/
theorem codedBranch_subset_cone (Y : ℕ → Bool) : ∀ x, CodedBranch Y x → x ∈ cone Y :=
  coneEmbedding_pointed Y

/-! ### From invariant cofinality to a cone -/

/-- A determined Turing-invariant **cofinal** set contains a cone: the
complement-cone alternative of `cone_theorem` contradicts cofinality. -/
theorem cone_of_invariant_cofinal (A : Set (ℕ → Bool))
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hcof : Cofinal (· ∈ A)) (hDet : GameDetermined A) :
    ∃ Y, cone Y ⊆ A := by
  rcases cone_theorem A hTI hDet with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact ⟨Y, hY⟩
  · obtain ⟨x, hYx, hAx⟩ := hcof Y
    exact absurd hAx (hY hYx)

/-! ### Martin's Lemma 2.3 for the invariant case

Putting the two halves together: an invariant cofinal determined set contains a
pointed perfect tree (in the pointed + realizing + perfect sense). -/

/-- **Martin's Lemma 2.3, Turing-invariant case.**  Every Turing-invariant,
cofinal, determined set `A` contains a pointed perfect tree: a family
`CodedBranch Y ⊆ A` that is pointed (every branch computes the code `Y`),
realizes every degree above `Y` (Prop 1.10), and is perfect (carries a
degree-preserving embedding of Cantor space).  Machine-checked from
`cone_theorem`. -/
theorem invariant_cofinal_contains_pointedPerfect (A : Set (ℕ → Bool))
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hcof : Cofinal (· ∈ A)) (hDet : GameDetermined A) :
    ∃ Y : ℕ → Bool,
      (∀ x, CodedBranch Y x → x ∈ A) ∧
      (∀ x, CodedBranch Y x → Y ≤ₜ x) ∧
      (∀ d, Y ≤ₜ d → ∃ x, CodedBranch Y x ∧ x ≡ₜ d) ∧
      Nonempty (PerfectEmbedding Y (CodedBranch Y)) := by
  obtain ⟨Y, hY⟩ := cone_of_invariant_cofinal A hTI hcof hDet
  exact ⟨Y, fun x hx => hY (coneEmbedding_pointed Y x hx),
    coneEmbedding_pointed Y, coneEmbedding_realizes Y, ⟨coneEmbedding Y⟩⟩

/-- The same conclusion phrased against the project's `TuringDeterminacy`
convention: for any determinacy class `Γ` containing `A`, an invariant cofinal
`A` in the class contains a pointed perfect tree.  With `Γ := fun _ => True` this
is the `ZF+AD` statement (determinacy threaded as a hypothesis, never an axiom);
with `Γ := MeasurableSet` it is unconditional modulo Borel determinacy. -/
theorem invariant_cofinal_contains_pointedPerfect_TD {Γ : Set (ℕ → Bool) → Prop}
    (hTD : TuringDeterminacy Γ) (A : Set (ℕ → Bool)) (hΓ : Γ A)
    (hTI : TuringInvariantSet A) (hcof : Cofinal (· ∈ A)) :
    ∃ Y : ℕ → Bool,
      (∀ x, CodedBranch Y x → x ∈ A) ∧
      (∀ x, CodedBranch Y x → Y ≤ₜ x) ∧
      (∀ d, Y ≤ₜ d → ∃ x, CodedBranch Y x ∧ x ≡ₜ d) ∧
      Nonempty (PerfectEmbedding Y (CodedBranch Y)) :=
  invariant_cofinal_contains_pointedPerfect A hTI hcof (hTD A hΓ hTI)

#print axioms invariant_cofinal_contains_pointedPerfect
#print axioms invariant_cofinal_contains_pointedPerfect_TD

end Martin
