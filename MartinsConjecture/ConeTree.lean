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

/-- The embedding is **injective**: distinct `z` give distinct branches (the odd
bits recover `z`).  So the coding tree is genuinely *perfect* — it has a distinct
branch for every point of Cantor space, hence continuum-many, and by
`coneEmbedding_realizes` one of every degree above `Y`. -/
theorem coneEmbedding_injective (Y : ℕ → Bool) :
    Function.Injective (fun z => Cantor.join Y z) := by
  intro z z' h
  funext k
  have hk := congrFun h (2 * k + 1)
  simp only [Cantor.join, if_neg (show ¬ (2 * k + 1) % 2 = 0 by omega)] at hk
  rwa [show (2 * k + 1) / 2 = k by omega] at hk

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

/-! ### Why the general (non-invariant) case is harder

The sets `A n` in Groszek–Slaman are *not* Turing-invariant, so `cone_theorem`
does not apply to them.  Passing to the **invariant hull** (the `≡ᵀ`-closure)
recovers an invariant cofinal set, hence — with determinacy — a pointed perfect
tree; but its branches lie only in the *hull*, i.e. each is Turing-equivalent to
some member of `A`, not necessarily a member of `A`.  Bridging that last gap
uniformly (a degree-preserving *selection* of genuine `A`-members along the tree)
is exactly the extra content of Martin's general Lemma 2.3, and connects to the
uniformization crux (`partI_of_uniformization`). -/

/-- The **invariant hull** of `A`: all reals Turing-equivalent to a member. -/
def invariantHull (A : Set (ℕ → Bool)) : Set (ℕ → Bool) := {x | ∃ y, y ≡ₜ x ∧ y ∈ A}

theorem subset_invariantHull (A : Set (ℕ → Bool)) : A ⊆ invariantHull A :=
  fun x hx => ⟨x, Cantor.equiv.refl x, hx⟩

/-- The invariant hull is Turing-invariant. -/
theorem invariantHull_invariant (A : Set (ℕ → Bool)) :
    TuringInvariantSet (invariantHull A) := by
  intro X Y hXY
  exact ⟨fun ⟨y, hyX, hyA⟩ => ⟨y, hyX.trans hXY, hyA⟩,
    fun ⟨y, hyY, hyA⟩ => ⟨y, hyY.trans hXY.symm, hyA⟩⟩

/-- Cofinality passes to the invariant hull. -/
theorem cofinal_invariantHull (A : Set (ℕ → Bool)) (h : Cofinal (· ∈ A)) :
    Cofinal (· ∈ invariantHull A) := by
  intro z
  obtain ⟨x, hzx, hxA⟩ := h z
  exact ⟨x, hzx, x, Cantor.equiv.refl x, hxA⟩

/-- **The general case, reduced to a selection.**  For *any* cofinal `A` whose
invariant hull is determined, there is a pointed perfect tree (the `Y`-coding
tree) every branch of which is Turing-equivalent to a member of `A`.  What is
still missing for a pointed perfect tree *inside* `A` is a uniform, degree-
preserving choice of those `A`-members — the content of Martin's general
Lemma 2.3 beyond the cone theorem. -/
theorem cofinal_codingTree_equiv_mem (A : Set (ℕ → Bool))
    (hcof : Cofinal (· ∈ A)) (hDet : GameDetermined (invariantHull A)) :
    ∃ Y : ℕ → Bool,
      (∀ d, Y ≤ₜ d → ∃ x, CodedBranch Y x ∧ x ≡ₜ d) ∧
      (∀ x, CodedBranch Y x → ∃ a, a ≡ₜ x ∧ a ∈ A) := by
  obtain ⟨Y, hY⟩ := cone_of_invariant_cofinal (invariantHull A)
    (invariantHull_invariant A) (cofinal_invariantHull A hcof) hDet
  exact ⟨Y, coneEmbedding_realizes Y,
    fun x hx => hY (coneEmbedding_pointed Y x hx)⟩

#print axioms invariant_cofinal_contains_pointedPerfect
#print axioms invariant_cofinal_contains_pointedPerfect_TD
#print axioms cofinal_codingTree_equiv_mem

end Martin
