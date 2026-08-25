/-
**The `BnAm` sub-case leaks into Part 2 (transfinite rank).**

Recall the four-way jump-distance decomposition of the incomparable core (`IncomparableArithReduction`).
The `BnAm` sub-case is `X ≤ᵀ (F X)^(k)` (arithmetically increasing, `Bn`) together with `F X ≰ᵀ X^(m)`
for every finite `m` (`An`).  Consider the derived function `G X := jump^[k] (F X)`.  It is Turing-invariant
(`jumpIter_comp_invariant`) and, on the `Bn` cone, *above identity* (`X ≤ᵀ (F X)^(k) = G X`) — so Part 2
of Martin's Conjecture assigns it a rank in the jump hierarchy.

The result below shows that rank cannot be *finite*: if `G ≡ᵀ jump^[j]` on a cone for some finite `j`, then
`F X ≤ᵀ (F X)^(k) ≡ᵀ X^(j)`, i.e. `F X ≤ₐ X`, contradicting `An`.  Hence `BnAm` forces `jump^[k]∘F` to be
a *transfinite*-rank above-identity function — a genuinely Part-2 object.  This is the precise sense in
which `BnAm` is not "native" to the incomparable core: it can only survive by exhibiting the kind of
non-finite-rank increasing function that Part 2 is about (and whose existence, off the uniform class, is
itself open).  Together with `ArithRegressiveSkeleton` (which routes `AnBm` through relativized
Slaman–Steel), this leaves the transfinite residue (`BnBm`/`AnAm`) as the genuine open heart.
-/
import MartinsConjecture.IncomparableArithReduction

open scoped Computability
open Cantor

namespace Martin

/-- `A ≤ᵀ jump^[k] A`: every set is below each of its finite jumps. -/
theorem self_le_jumpIter (A : ℕ → Bool) : ∀ k, A ≤ₜ Cantor.jump^[k] A
  | 0 => Cantor.le.refl A
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact (self_le_jumpIter A k).trans (Cantor.le_jump _)

/-- **`BnAm` forces infinite Part-2 rank.**  Under the `An` hypothesis (`F X ≰ᵀ X^(m)` for all finite
`m`, on a cone), the invariant above-identity function `X ↦ jump^[k] (F X)` is `≡ᵀ` *no* finite jump
`jump^[j]` on any cone: such an equivalence would give `F X ≤ᵀ (F X)^(k) ≡ᵀ X^(j)`, contradicting `An`
at `m = j`.  So the `BnAm` sub-case leaks into Part 2 — it requires a transfinite-rank increasing
function. -/
theorem bnAm_jumpComp_not_finite_jump {F : (ℕ → Bool) → ℕ → Bool} (k : ℕ)
    (hAn : OnCone (fun X => ∀ m, ¬ F X ≤ₜ Cantor.jump^[m] X)) :
    ¬ ∃ j, OnCone (fun X => Cantor.jump^[k] (F X) ≡ₜ Cantor.jump^[j] X) := by
  rintro ⟨j, hEq⟩
  obtain ⟨B, hB⟩ := onCone_and hAn hEq
  have hBB := hB B (Cantor.le.refl B)
  exact hBB.1 j ((self_le_jumpIter (F B) k).trans hBB.2.1)

#print axioms self_le_jumpIter
#print axioms bnAm_jumpComp_not_finite_jump

end Martin
