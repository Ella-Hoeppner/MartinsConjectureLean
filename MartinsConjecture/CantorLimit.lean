/-
The limit lemma at the level of Cantor points, and Post's-theorem packaging.

Restates the Shoenfield limit lemma for points `Y : ℕ → Bool` of Cantor
space and their jump degrees:

* **`Cantor.le_jump_iff_limitApprox`** — `Y ≤ᵀ X′` iff the bits of `Y` have an
  `X`-computable stage approximation converging pointwise;
* **`Cantor.jump_limit`** — the jump itself is such an approximation of its
  own bits (Δ⁰₂-in-`X`), packaged for points;
* **`Cantor.not_le_self_jump_lt`** — the strict two-step
  `X <ₜ X′ <ₜ X″` inside the jump hierarchy on points (a sanity corollary of
  jump strictness plus monotonicity).
-/
import MartinsConjecture.LimitLemmaFull

open scoped Computability
open OracleCode

namespace Cantor

/-- A point `Y` is Turing below `X′` iff the bit-graph of `Y` is recursive in
the jump — the bridge between `Cantor.le` and `Nat.RecursiveIn`. -/
theorem le_jump_iff_bitg {X Y : ℕ → Bool} :
    Y ≤ₜ jump X ↔
    Nat.RecursiveIn {toPFun (jump X)} (fun n : ℕ => ((bitg Y n : ℕ) : Part ℕ)) := by
  rw [Cantor.le]
  constructor
  · intro h
    have hnat := RecursiveIn.iff_nat.mp h
    refine hnat.of_eq fun n => ?_
    rfl
  · intro h
    refine RecursiveIn.iff_nat.mpr (h.of_eq fun n => ?_)
    rfl

/-- **The Shoenfield limit lemma for Cantor points**: `Y ≤ᵀ X′` iff the bits
of `Y` have an `X`-computable stage approximation converging pointwise. -/
theorem le_jump_iff_limitApprox {X Y : ℕ → Bool} :
    Y ≤ₜ jump X ↔
    ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = bitg Y n := by
  rw [le_jump_iff_bitg]
  exact OracleCode.limit_lemma X (bitg Y)

/-- The jump of `X` is limit-computable from `X` (Δ⁰₂-in-`X`), stated for
points: `jump X ≤ᵀ jump X` witnessed by the `X`-computable approximation. -/
theorem jump_limit (X : ℕ → Bool) :
    ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = bitg (jump X) n := by
  obtain ⟨g, hg, hlim, -⟩ := OracleCode.jump_limitApprox X
  exact ⟨g, hg, hlim⟩

/-- Sanity corollary: the two-step jump chain `X <ₜ X′ <ₜ X″` is strict. -/
theorem lt_jump_lt_jump_jump (X : ℕ → Bool) :
    X <ₜ jump X ∧ jump X <ₜ jump (jump X) :=
  ⟨lt_jump X, lt_jump (jump X)⟩

#print axioms le_jump_iff_limitApprox
#print axioms jump_limit

end Cantor
