/-
**Martin's perfect-set dichotomy for the Turing cone.**

`MartinPPT` (Lemma 2.3: every cofinal set contains a pointed perfect tree) is a
consequence of a more fundamental determinacy statement — the *perfect-set
property relativized to the Turing cone filter*:

> Every set of reals either contains a pointed perfect tree, or its complement
> contains a cone.

This `MartinDichotomy` is the honest determinacy input.  From it `MartinPPT` is
immediate (a cofinal set meets every cone, so the complement-cone alternative is
impossible).  And its **invariant case is a theorem here** — from the cone theorem
(`cone_theorem`) plus the fact that a cone is a pointed perfect tree
(`cone_contains_PPT`).  So the *only* content not yet formalized is the dichotomy
for **non-invariant** sets — precisely Martin's Lemma 2.3 beyond the cone theorem.
-/
import MartinsConjecture.ConeRawPPT

open scoped Computability
open Cantor

namespace Martin

/-- **Martin's perfect-set dichotomy for the Turing cone.**  Every set either
contains a pointed perfect tree or its complement contains a cone.  A consequence
of AD (not provable in ZFC); the invariant case is proved below. -/
def MartinDichotomy : Prop :=
  ∀ A : Set (ℕ → Bool),
    (∃ T : PPT, ∀ x, T.mem x → x ∈ A) ∨ (∃ Y, cone Y ⊆ Aᶜ)

/-- **`MartinPPT` from the dichotomy.**  A cofinal set meets every cone, so the
complement-cone alternative cannot occur; hence it contains a pointed perfect
tree. -/
theorem martinPPT_of_dichotomy (h : MartinDichotomy) : MartinPPT := by
  intro A hcof
  rcases h A with ⟨T, hT⟩ | ⟨Y, hY⟩
  · exact ⟨T, hT⟩
  · obtain ⟨x, hYx, hxA⟩ := hcof Y
    exact absurd hxA (hY hYx)

/-- **The invariant case of the dichotomy is a theorem.**  A Turing-invariant
determined set contains a cone (⟹ a pointed perfect tree, `cone_contains_PPT`) or
its complement contains a cone (`cone_theorem`). -/
theorem perfectDichotomy_invariant (A : Set (ℕ → Bool))
    (hTI : TuringInvariantSet A) (hDet : GameDetermined A) :
    (∃ T : PPT, ∀ x, T.mem x → x ∈ A) ∨ (∃ Y, cone Y ⊆ Aᶜ) := by
  rcases cone_theorem A hTI hDet with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · obtain ⟨T, hT⟩ := cone_contains_PPT Y
    exact Or.inl ⟨T, fun x hx => hY (hT x hx)⟩
  · exact Or.inr ⟨Y, hY⟩

/-! ### Part 1 from the dichotomy -/

/-- **Part 1 of Martin's conjecture from the perfect-set dichotomy.**  Composing
`martinPPT_of_dichotomy` with the whole verified reduction chain: Part 1 follows
from the perfect-set dichotomy (the fundamental determinacy input) together with
the class-specific "escaping ⟹ measure-preserving". -/
theorem partI_of_dichotomy_escaping (h : MartinDichotomy)
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_martinPPT_escaping (martinPPT_of_dichotomy h) hTD hesc

#print axioms martinPPT_of_dichotomy
#print axioms perfectDichotomy_invariant
#print axioms partI_of_dichotomy_escaping

end Martin
