/-
**The dominated-inverting witness of an incomparable counterexample must be a jump-type operator.**

Part 1's open core reduces (Lutz–Siskind) to two questions about `DominatedInvertible F`
(`∃` invariant `g`, `X ≤ᵀ g(F X)` on a cone):
* **Q3** — is every non-constant invariant `F` dominated-invertible?
* **Q4** — does `DominatedInvertible F ⟹ MeasurePreserving F`?  (Equivalently: is there a
  dominated-invertible *incomparable* `F`? — the sharp Q4 disproof target.)

This file adds an elementary but sharpening constraint on the *witness* `g` in the Q4 target.  A
witness is **regressive** if `g c ≤ᵀ c` for every `c` (it computes its output *from* its input, never
lifting the degree — the "continuous / below" behaviour).  We show:

* `aboveId_of_regressive_diWitness` — a *regressive* witness forces `F` above the identity on a cone
  (hence measure-preserving): `X ≤ᵀ g(F X) ≤ᵀ F X`.
* `not_regressive_diWitness_of_incomparable` — therefore an *incomparable* `F` admits **no** regressive
  dominated-inverting witness.

So a hypothetical dominated-invertible incomparable `F` (the Q4 counterexample) must be inverted by a
**non-regressive** `g` — one that genuinely *lifts* the degree of `F X` (a jump-type operator),
recovering `X` from information the value `F X` does *not* itself contain.  This matches the intuition
that `X ≤ᵀ (F X)'` while `F X ⊥ᵀ X` is the shape of such a counterexample: the witness must be at least
as strong as a jump.  It also explains why `MP ⟹ DI` uses the *identity* witness (`g = id`, regressive)
and why that route is blocked in the incomparable case — the identity is regressive.
-/
import MartinsConjecture.MeasurePreservingCK

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A regressive dominated-inverting witness forces `F` above the identity.**  If `g c ≤ᵀ c` for all
`c` and `X ≤ᵀ g(F X)` on a cone, then `X ≤ᵀ g(F X) ≤ᵀ F X` on that cone, i.e. `AboveIdOnCone F`. -/
theorem aboveId_of_regressive_diWitness {g : (ℕ → Bool) → ℕ → Bool}
    (hreg : ∀ c, g c ≤ₜ c) (hdi : OnCone (fun X => X ≤ₜ g (F X))) : AboveIdOnCone F := by
  obtain ⟨base, hbase⟩ := hdi
  exact ⟨base, fun X hX => (hbase X hX).trans (hreg (F X))⟩

/-- **An incomparable `F` has no regressive dominated-inverting witness.**  A regressive witness would
put `F` above the identity (`aboveId_of_regressive_diWitness`), contradicting `¬ X ≤ᵀ F X`.  Hence the
witness of a dominated-invertible incomparable counterexample must be **non-regressive** (jump-type). -/
theorem not_regressive_diWitness_of_incomparable {g : (ℕ → Bool) → ℕ → Bool}
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hreg : ∀ c, g c ≤ₜ c) :
    ¬ OnCone (fun X => X ≤ₜ g (F X)) := by
  intro hdi
  obtain ⟨b1, hb1⟩ := hinc
  obtain ⟨b2, hb2⟩ := aboveId_of_regressive_diWitness hreg hdi
  exact (hb1 (Cantor.join b1 b2) (Cantor.left_le_join _ _)).2
    (hb2 (Cantor.join b1 b2) (Cantor.right_le_join _ _))

/-- **The witness of a dominated-invertible incomparable `F` is non-regressive** (packaged with
`DominatedInvertible`).  Extracting the witness `g` from `DominatedInvertible F`, there is a degree `c`
with `g c ≰ᵀ c` — `g` genuinely lifts some degree (a jump-type operator, not a mere reprocessing of its
input).  So a Q4 counterexample inverts `F` by strictly *raising* degrees. -/
theorem diWitness_nonRegressive_of_incomparable
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hDI : DominatedInvertible F) :
    ∃ g, TuringInvariant g ∧ OnCone (fun X => X ≤ₜ g (F X)) ∧ ∃ c, ¬ g c ≤ₜ c := by
  obtain ⟨g, hg_inv, hg_cone⟩ := hDI
  refine ⟨g, hg_inv, hg_cone, ?_⟩
  by_contra hall
  push_neg at hall
  exact not_regressive_diWitness_of_incomparable hinc hall hg_cone

#print axioms aboveId_of_regressive_diWitness
#print axioms not_regressive_diWitness_of_incomparable
#print axioms diWitness_nonRegressive_of_incomparable

end Martin
