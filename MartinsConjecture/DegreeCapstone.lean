/-
A capstone tying together two headline results: the effective Kleene–Post
intermediate degree and the Friedberg jump-inversion range characterization.

Since the jump's range is exactly the cone above `0′` (`jump_range_iff`) and the
effective Kleene–Post construction produces a degree `A` strictly between `∅` and
`0′` (`exists_intermediate_degree`), that `A` is **not a jump**: the jump operator
is far from surjective — it entirely misses the intermediate degrees.
-/
import MartinsConjecture.EffectiveKP
import MartinsConjecture.JumpInversion

open scoped Computability
open OracleCode Cantor

/-- **A non-jump strictly below `0′`.**  There is a Turing degree `A` with
`∅ <ᵀ A <ᵀ 0′` that is not the jump of any degree.  Hence the jump operator is
not surjective onto the degrees `≥ᵀ 0′`-and-below-`0′` in a strong sense: the
intermediate degrees (of which `A` is one) are never jumps. -/
theorem exists_intermediate_non_jump :
    ∃ A : ℕ → Bool,
      ¬ (A ≤ₜ (fun _ => false)) ∧ A ≤ₜ Cantor.jump (fun _ => false)
      ∧ ¬ ∃ B : ℕ → Bool, Cantor.jump B ≡ₜ A := by
  obtain ⟨A, hnc, hle, hnge⟩ := KleenePostJump.exists_intermediate_degree
  refine ⟨A, hnc, hle, ?_⟩
  intro h
  exact hnge ((OracleCode.jump_range_iff A).mp h)

#print axioms exists_intermediate_non_jump
