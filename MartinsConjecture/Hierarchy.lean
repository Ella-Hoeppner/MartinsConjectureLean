/-
The jump hierarchy: `0 <ᵀ 0′ <ᵀ 0″ <ᵀ ⋯`.

Iterating the jump produces a strictly increasing ω-chain of Turing degrees.
Consequences packaged as Mathlib-typeclass facts about `TuringDegree`:
there are infinitely many Turing degrees (`Infinite TuringDegree`) and no
maximal one (`NoMaxOrder TuringDegree`).
-/
import MartinsConjecture.JumpInvariance

open scoped Computability
open OracleCode

namespace Cantor

theorem lt.trans {X Y Z : ℕ → Bool} (h1 : X <ₜ Y) (h2 : Y <ₜ Z) : X <ₜ Z :=
  ⟨h1.1.trans h2.1, fun h => h2.2 (h.trans h1.1)⟩

/-- The finite iterates of the jump form a strictly increasing chain. -/
theorem jumpIter_lt_succ (X : ℕ → Bool) (n : ℕ) :
    Cantor.jump^[n] X <ₜ Cantor.jump^[n + 1] X := by
  rw [Function.iterate_succ_apply']
  exact lt_jump _

end Cantor

namespace TuringDegree

/-- Degree-level jump iterates are strictly monotone: `d < d′ < d″ < ⋯`. -/
theorem strictMono_jump_iterate (d : TuringDegree) :
    StrictMono fun n => TuringDegree.jump^[n] d :=
  strictMono_nat_of_lt_succ fun n => by
    rw [Function.iterate_succ_apply']
    exact lt_jump _

/-- There are infinitely many Turing degrees. -/
instance : Infinite TuringDegree :=
  Infinite.of_injective _ (strictMono_jump_iterate (Quot.mk _ fun _ => Part.some 0)).injective

/-- No Turing degree is maximal: the jump always goes strictly up. -/
instance : NoMaxOrder TuringDegree :=
  ⟨fun d => ⟨TuringDegree.jump d, TuringDegree.lt_jump d⟩⟩

end TuringDegree

#print axioms TuringDegree.strictMono_jump_iterate
