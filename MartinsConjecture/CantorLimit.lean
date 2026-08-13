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

/-- **Capstone: the double jump is not `X`-limit-computable.**  Combining the
limit lemma with jump strictness: `X″` has no `X`-computable stage
approximation converging pointwise — which is exactly why the jump hierarchy
is proper (there is genuine content strictly above `X′`). -/
theorem jump_jump_not_limitApprox (X : ℕ → Bool) :
    ¬ ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = bitg (jump (jump X)) n := by
  intro h
  -- an X-approximation of `X″`'s bits would make `X″ ≤ᵀ X′`, contradicting strictness.
  have hle : jump (jump X) ≤ₜ jump X := le_jump_iff_limitApprox.mpr h
  exact not_jump_le (jump X) hle

/-! ### Jump and join -/

/-- The jump is monotone under the join. -/
theorem jump_le_jump_join_left (X Y : ℕ → Bool) : jump X ≤ₜ jump (join X Y) :=
  jump_mono (left_le_join X Y)

theorem jump_le_jump_join_right (X Y : ℕ → Bool) : jump Y ≤ₜ jump (join X Y) :=
  jump_mono (right_le_join X Y)

/-- The join of the jumps is below the jump of the join (`X′ ⊕ Y′ ≤ᵀ (X ⊕ Y)′`).
The reverse inequality also holds classically but needs a separate argument. -/
theorem join_jump_le_jump_join (X Y : ℕ → Bool) :
    join (jump X) (jump Y) ≤ₜ jump (join X Y) :=
  join_le (jump_le_jump_join_left X Y) (jump_le_jump_join_right X Y)

#print axioms le_jump_iff_limitApprox
#print axioms jump_limit
#print axioms jump_jump_not_limitApprox
#print axioms join_jump_le_jump_join

end Cantor

namespace Martin

/-- The jump is uniformly Turing invariant (from the computable version). -/
theorem uniformlyTuringInvariant_jump : UniformlyTuringInvariant Cantor.jump :=
  computablyUniformlyTuringInvariant_jump.toUniformly

/-- Every finite jump iterate is uniformly Turing invariant — so the whole
Martin-order chain `id <ₘ (·′) <ₘ (·″) <ₘ ⋯` consists of uniformly invariant
functions (the class Steel's theorem prewellorders). -/
theorem uniformlyTuringInvariant_jumpIterate :
    ∀ n, UniformlyTuringInvariant (fun X => Cantor.jump^[n] X)
  | 0 => uniformlyTuringInvariant_id
  | n + 1 => by
      have h := uniformlyTuringInvariant_jump.comp (uniformlyTuringInvariant_jumpIterate n)
      have heq : (fun X => Cantor.jump^[n + 1] X)
          = (fun X => Cantor.jump (Cantor.jump^[n] X)) := by
        funext X; rw [Function.iterate_succ_apply']
      rw [heq]; exact h

end Martin
