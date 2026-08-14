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

/-- **Strict jump inversion.**  Every degree `≥ᵀ 0′` is the jump of a degree
*strictly* below it.  (From `jump_inversion` — which gives `A ≤ᵀ C` with
`A′ ≡ᵀ C` — plus strictness: if `A ≡ᵀ C` then `C′ ≡ᵀ A′ ≡ᵀ C`, forcing
`C′ ≤ᵀ C`, contradicting `C <ᵀ C′`.) -/
theorem jump_inversion_strict (C : ℕ → Bool)
    (hC : Cantor.jump (fun _ : ℕ => false) ≤ₜ C) :
    ∃ A : ℕ → Bool, A <ₜ C ∧ Cantor.jump A ≡ₜ C := by
  obtain ⟨A, hAle, hAjump⟩ := OracleCode.jump_inversion C hC
  refine ⟨A, ⟨hAle, ?_⟩, hAjump⟩
  intro hCA
  have hjeq : Cantor.jump A ≡ₜ Cantor.jump C :=
    ⟨Cantor.jump_mono hAle, Cantor.jump_mono hCA⟩
  exact Cantor.not_jump_le C (hjeq.2.trans hAjump.1)

#print axioms jump_inversion_strict
