/-
r.e. operators (enumeration operators presented by a machine index) and Post's
bound, toward Lachlan's theorem (Bard–Lutz, Lutz thesis Cor. 3.11).

An r.e. operator `W` is presented by an index `e` via
`n ∈ Wˣ ⟺ Φ_e^X(n)↓`.  The `Σ₁`-in-`X` content gives immediately:

* `OracleCode.reReal_le_jump` — **`Wˣ ≤ᵀ X′`** for every r.e. operator (the
  easy half of Lachlan's local dichotomy: an r.e. operator never exceeds the
  jump).

This is `domain_recursiveIn_jump` (Post's theorem, `Σ₁` direction) applied to
the universal functional, packaged at the level of Cantor points.
-/
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.PostDomain

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- The **r.e. operator** with index `e`, as a real (its characteristic
function): `Wˣ n = 1 ⟺ Φ_e^X(n)↓`. -/
noncomputable def reReal (e : ℕ) (X : ℕ → Bool) : ℕ → Bool :=
  fun n => decide (eval (toPFun X) (ofNatCode e) n).Dom

/-- **Every r.e. operator is Turing-below the jump** (Post's theorem, `Σ₁`
direction, for operators): `Wˣ ≤ᵀ X′`.  This is the determinacy-free easy half
of Lachlan's local dichotomy (Lutz Cor. 3.11): an r.e. operator can never
compute more than the jump. -/
theorem reReal_le_jump (e : ℕ) (X : ℕ → Bool) : reReal e X ≤ₜ Cantor.jump X := by
  rw [Cantor.le_iff_bitg, Cantor.toPFun_jump]
  have hrec : Nat.RecursiveIn {toPFun X} (eval (toPFun X) (ofNatCode e)) :=
    eval_recursiveIn (toPFun X) (ofNatCode e)
  refine (domain_recursiveIn_jump hrec).of_eq fun n => ?_
  have hbit : bitg (reReal e X) n
      = (if (eval (toPFun X) (ofNatCode e) n).Dom then 1 else 0) := by
    simp only [bitg, reReal]
    by_cases hD : (eval (toPFun X) (ofNatCode e) n).Dom <;> simp [hD]
  rw [hbit]

/-- The value of an r.e. operator at `X` is *itself* an r.e. operator over `Y`,
via a **computable** index, whenever `Y` computes `X` (`Φ_j^Y = X`):
`Wˣ = W'ʸ` where `W'` has index `trE j · e`.  This is the operator-level form of
computable composition (`eval_trE_comp`) — the mechanism by which
uniform-invariance arguments (Lachlan, Bard) transport `Wˣ` between different
representatives of a Turing degree. -/
theorem reReal_eq_of_reduces {e j : ℕ} {X Y : ℕ → Bool}
    (hj : eval (toPFun Y) (ofNatCode j) = toPFun X) :
    reReal e X = reReal (trE (ofNatCode j) e) Y := by
  funext n
  simp only [reReal]
  rw [eval_trE_comp hj e]

end OracleCode

#print axioms OracleCode.reReal_le_jump
#print axioms OracleCode.reReal_eq_of_reduces
