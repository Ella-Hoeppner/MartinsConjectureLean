/-
**König's lemma for binary trees.**

A prefix-closed set of finite binary strings with arbitrarily long members has an
infinite branch.  This is the compactness ingredient of Lutz–Siskind's Lemma 2.1
(effective injectivity on perfect trees): the search for the branch through a node
terminates precisely because the "wrong" nodes fail König's hypothesis.

Self-contained and purely combinatorial.
-/
import Mathlib.Data.List.Infix
import Mathlib.Tactic

open Classical

namespace Konig

/-- `σ` has arbitrarily long extensions in `S`. -/
def HasInf (S : List Bool → Prop) (σ : List Bool) : Prop :=
  ∀ m, ∃ τ, S τ ∧ σ <+: τ ∧ m ≤ τ.length

/-- If `σ` has arbitrarily long extensions, so does one of its two children. -/
theorem hasInf_step {S : List Bool → Prop} {σ : List Bool} (h : HasInf S σ) :
    HasInf S (σ ++ [true]) ∨ HasInf S (σ ++ [false]) := by
  unfold HasInf at h ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨⟨mt, hmt⟩, mf, hmf⟩ := hc
  obtain ⟨τ, hτS, ht', hτlen⟩ := h (mt + mf + σ.length + 1)
  obtain ⟨t, rfl⟩ := ht'
  have htne : t ≠ [] := by
    intro he; subst he; simp only [List.append_nil] at hτlen; omega
  obtain ⟨b, t', rfl⟩ := List.exists_cons_of_ne_nil htne
  have hpre : σ ++ [b] <+: σ ++ b :: t' := ⟨t', by simp⟩
  cases b with
  | true => exact absurd (hmt (σ ++ true :: t') hτS hpre) (by omega)
  | false => exact absurd (hmf (σ ++ false :: t') hτS hpre) (by omega)

/-- The branch chosen greedily: at each node go to a child that still has
arbitrarily long extensions (defaulting to `false`). -/
noncomputable def path (S : List Bool → Prop) : ℕ → List Bool
  | 0 => []
  | k + 1 => if HasInf S (path S k ++ [true]) then path S k ++ [true] else path S k ++ [false]

theorem path_succ (S : List Bool → Prop) (k : ℕ) :
    path S (k + 1) =
      (if HasInf S (path S k ++ [true]) then path S k ++ [true] else path S k ++ [false]) := rfl

/-- The greedy path keeps `HasInf` invariant. -/
theorem hasInf_path {S : List Bool → Prop} (h0 : HasInf S []) : ∀ k, HasInf S (path S k)
  | 0 => h0
  | k + 1 => by
      rw [path_succ]
      split_ifs with hc
      · exact hc
      · rcases hasInf_step (hasInf_path h0 k) with ht | hf
        · exact absurd ht hc
        · exact hf

theorem path_length (S : List Bool → Prop) : ∀ k, (path S k).length = k
  | 0 => rfl
  | k + 1 => by rw [path_succ]; split <;> simp [path_length S k]

/-- The `k`-th bit of the branch is the choice made at stage `k`. -/
noncomputable def branch (S : List Bool → Prop) (k : ℕ) : Bool :=
  decide (HasInf S (path S k ++ [true]))

theorem path_succ_eq_branch (S : List Bool → Prop) (k : ℕ) :
    path S (k + 1) = path S k ++ [branch S k] := by
  rw [path_succ, branch]
  by_cases hc : HasInf S (path S k ++ [true]) <;> simp [hc]

/-- The first `n` bits of the branch are exactly `path S n`. -/
theorem take_branch (S : List Bool → Prop) : ∀ n, (List.range n).map (branch S) = path S n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        take_branch S n, path_succ_eq_branch]

/-- Prefix-closure iterated: if `σ` is a prefix of a member of `S` and `S` is
closed under dropping the last element, then `σ ∈ S`. -/
theorem mem_of_prefix {S : List Bool → Prop} (hclosed : ∀ σ b, S (σ ++ [b]) → S σ) :
    ∀ τ, S τ → ∀ σ, σ <+: τ → S σ := by
  intro τ hτ σ hσ
  obtain ⟨t, rfl⟩ := hσ
  induction t using List.reverseRecOn with
  | nil => simpa using hτ
  | append_singleton t b ih =>
      apply ih
      rw [← List.append_assoc] at hτ
      exact hclosed _ _ hτ

/-- **König's lemma.**  A prefix-closed set of binary strings with arbitrarily
long members has an infinite branch: some `y : ℕ → Bool` has all its finite
prefixes in `S`. -/
theorem exists_branch {S : List Bool → Prop}
    (hclosed : ∀ σ b, S (σ ++ [b]) → S σ) (h0 : HasInf S []) :
    ∃ y : ℕ → Bool, ∀ n, S ((List.range n).map y) := by
  refine ⟨branch S, fun n => ?_⟩
  rw [take_branch S n]
  obtain ⟨τ, hτS, hτpre, _⟩ := hasInf_path h0 n 0
  exact mem_of_prefix hclosed τ hτS _ hτpre

end Konig
