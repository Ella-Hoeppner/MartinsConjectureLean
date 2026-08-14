/-
The Friedberg jump-inversion theorem: every degree `≥ᵀ 0′` is a jump.

`∀ C, 0′ ≤ᵀ C → ∃ A, A′ ≡ᵀ C`.

Construction (finite extension, relative to `C`): build `A = ⋃ σ_e` where at
stage `e` we consult the extension-halting oracle (`0′`-decidable, hence
`C`-decidable) "does `Φ_e` halt on `e` under some extension of `σ_e`?"; if so we
append the least such extension (forcing `e ∈ A′`), otherwise nothing; then we
append one bit of `C`.  Then `A ≤ᵀ C`, `A′ ≤ᵀ C` (the jump is read off the
`C`-computable decisions), and `C ≤ᵀ A′` (decode by reconstructing the
construction from `A′`, using `A ≤ᵀ A′`).
-/
import MartinsConjecture.ContinuousCase

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- A `0/1` extension decoded from a `List Bool` code. -/
def boolExt (v : ℕ) : List ℕ :=
  ((Encodable.decode (α := List Bool) v).getD []).map (fun b => if b then 1 else 0)

theorem boolExt_le (v : ℕ) : ∀ x ∈ boolExt v, x ≤ 1 := by
  intro x hx
  rw [boolExt, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  cases b <;> simp

/-- The existence of a `0/1` halting extension witness for `σ`, machine `e`,
input `e`, phrased over encoded pairs `w = ⟪encode(τ : List Bool), s⟫`. -/
def jExists (σ : List ℕ) (e : ℕ) : Prop :=
  ∃ w, (evaln (Nat.unpair w).2
    (σ ++ boolExt (Nat.unpair w).1)
    (ofNatCode e) e).isSome = true

/-- The least `0/1` halting-extension for `σ` at stage `e` (empty if none). -/
noncomputable def jtau (σ : List ℕ) (e : ℕ) : List ℕ :=
  if h : jExists σ e then boolExt (Nat.unpair (Nat.find h)).1 else []

theorem jtau_le (σ : List ℕ) (e : ℕ) : ∀ x ∈ jtau σ e, x ≤ 1 := by
  rw [jtau]
  split
  · exact boolExt_le _
  · simp

/-- The stage-`e` string of the construction (relative to `C`). -/
noncomputable def jstr (C : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | e + 1 =>
    (if jExists (jstr C e) e then jstr C e ++ jtau (jstr C e) e else jstr C e)
      ++ [if C e then 1 else 0]

/-- The real produced by the construction: the `n`-th bit is read from stage
`n+1` (which is long enough). -/
noncomputable def jReal (C : ℕ → Bool) : ℕ → Bool :=
  fun n => (jstr C (n + 1)).getD n 0 = 1

/-! ### Length and prefix facts -/

/-- Each stage appends at least one bit. -/
theorem jstr_succ_prefix (C : ℕ → Bool) (e : ℕ) : jstr C e <+: jstr C (e + 1) := by
  rw [jstr]
  by_cases h : jExists (jstr C e) e
  · simp only [if_pos h]
    exact (List.prefix_append _ _).trans (List.prefix_append _ _)
  · simp only [if_neg h]
    exact List.prefix_append _ _

theorem jstr_mono (C : ℕ → Bool) {e e' : ℕ} (h : e ≤ e') : jstr C e <+: jstr C e' := by
  induction e' with
  | zero => rw [Nat.le_zero.mp h]
  | succ e' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h1 | h1
    · exact (ih (Nat.lt_succ_iff.mp h1)).trans (jstr_succ_prefix C e')
    · rw [h1]

theorem jstr_len_ge (C : ℕ → Bool) : ∀ e, e ≤ (jstr C e).length
  | 0 => Nat.zero_le _
  | e + 1 => by
    have h := jstr_len_ge C e
    have : (jstr C e).length < (jstr C (e + 1)).length := by
      rw [jstr]
      by_cases hh : jExists (jstr C e) e <;> simp [hh]
    omega

/-- All bits of the construction are `0/1`. -/
theorem jstr_bits_le (C : ℕ → Bool) : ∀ e, ∀ x ∈ jstr C e, x ≤ 1
  | 0 => by simp [jstr]
  | e + 1 => by
    rw [jstr]
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hh : jExists (jstr C e) e
      · rw [if_pos hh, List.mem_append] at hx
        rcases hx with hx | hx
        · exact jstr_bits_le C e x hx
        · exact jtau_le _ _ x hx
      · rw [if_neg hh] at hx
        exact jstr_bits_le C e x hx
    · rw [List.mem_singleton] at hx
      subst hx; split <;> simp

end OracleCode

#print axioms OracleCode.jstr_mono
#print axioms OracleCode.jstr_bits_le
