/-
Toward the continuous case of Lachlan's local dichotomy (Lutz Cor. 3.11).

The **extension-halting predicate** `extHaltsFrom σ e n` — "does machine `e` halt
on `n` under some finite extension of the prefix `σ`?" — is `0′`-decidable
(`OracleCode.extHaltsFrom_recursiveIn_jump`), by bridging to the `ExtHalting`
search functional.  Its negation is the `Π₁` "no extension halts" test that
Lachlan's continuous case consults to decide `n ∈ Wˣ` from `X ⊕ 0′`.
-/
import MartinsConjecture.OperatorLocal
import MartinsConjecture.ExtHalting

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- `n ∈ W^{σ⌢τ}` for some finite extension `τ` of `σ`: the extension-halting
predicate for the operator with index `e`. -/
def extHaltsFrom (σ : List ℕ) (e n : ℕ) : Prop :=
  ∃ τ : List ℕ, haltsOn (σ ++ τ) e n

/-- `∃ w, ehTest p w = 0` is exactly extension-halting for the prefix decoded
from `p`. -/
theorem exists_ehTest_iff (p : ℕ) :
    (∃ w, ehTest p w = 0) ↔
      extHaltsFrom ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(Encodable.decode (α := List ℕ) (Nat.unpair w).1).getD [], (Nat.unpair w).2, ?_⟩
    by_contra hns
    rw [ehTest, if_neg hns] at hw
    exact one_ne_zero hw
  · rintro ⟨τ, s, hs⟩
    refine ⟨Nat.pair (Encodable.encode τ) s, ?_⟩
    rw [ehTest]
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    rw [if_pos hs]

/-- **The extension-halting problem is `0′`-decidable** (operator form): as a
function of `p = ⟪encode σ, ⟪e, n⟫⟫`, whether `n ∈ W^{σ⌢τ}` for some `τ` is
recursive in the jump of the empty oracle. -/
theorem extHaltsFrom_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((if extHaltsFrom
        ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2
        then 1 else 0 : ℕ) : Part ℕ)) := by
  refine extHalting_recursiveIn_jump.of_eq fun p => ?_
  rw [exists_ehTest_iff p]

end OracleCode

#print axioms OracleCode.extHaltsFrom_recursiveIn_jump
