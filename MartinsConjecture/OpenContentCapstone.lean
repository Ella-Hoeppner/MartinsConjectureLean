/-
**The canonical open content `escaping ⟹ MP`, reduced to the arithmetic decomposition.**

`escapingMP_iff_incomparable` (given `MartinPPT` + `RegressiveSlamanSteel`) identifies the definitive open
statement — every escaping invariant function is measure-preserving — with the incomparable core. Composing
with the four-way jump-distance decomposition (`IncomparableArithReduction`), `escaping ⟹ MP` reduces to
the arithmetic-regressive lemma `StrictArithRegressiveConstant` plus three arithmetically-typed sub-cases.
This shows the decomposition applies to the *canonical* formulation of Part 1's open content, not only to
the incomparable-core phrasing.
-/
import MartinsConjecture.IncomparableArithReduction
import MartinsConjecture.CounterexampleConstraints

open scoped Computability
open Cantor

namespace Martin

/-- **`escaping ⟹ MP` reduces to `StrictArithRegressiveConstant` + three jump-distance sub-cases**
(given `MartinPPT` and the known `RegressiveSlamanSteel`). Composing `escapingMP_iff_incomparable` with
`incomparableCore_of_three_cases_and_arith`. -/
theorem escapingMP_of_three_cases_and_arith (hTD : TuringDeterminacy fun _ => True)
    (hM : MartinPPT) (hSS : RegressiveSlamanSteel) (harith : StrictArithRegressiveConstant)
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
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F → MeasurePreserving F :=
  (escapingMP_iff_incomparable hTD hM hSS).mpr
    (incomparableCore_of_three_cases_and_arith hTD harith hAnAm hBnAm hBnBm)

#print axioms escapingMP_of_three_cases_and_arith

end Martin
