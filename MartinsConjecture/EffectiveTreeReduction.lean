/-
**The effective reduction for Lutz–Siskind's Lemma 2.1.**

`EffectiveTree.lean` proved the *algorithm* (`search_computes`): for a computable
injective functional `g` (code `e`) on the branches of a tree `T`, there is, for
each `n`, a level `m ≥ n` at which every consistent length-`m` node reveals `x↾n`.

Here that search is turned into an actual **Turing reduction** `x ≤ᵀ g x ⊕ T`, by
implementing it as an oracle computation: enumerate the length-`m` nodes, decide
tree-membership and consistency from the oracle, `rfind` the good level, read off
`x↾n`.

This file builds the primitive-recursive scaffolding first (node enumeration).
-/
import MartinsConjecture.EffectiveTree

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- All binary strings of length `m`. -/
def allBoolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allBoolLists m).flatMap (fun l => [false :: l, true :: l])

theorem allBoolLists_length : ∀ (m : ℕ), ∀ l ∈ allBoolLists m, l.length = m := by
  intro m
  induction m with
  | zero => intro l hl; simp only [allBoolLists, List.mem_singleton] at hl; simp [hl]
  | succ m ih =>
      intro l hl
      simp only [allBoolLists, List.mem_flatMap] at hl
      obtain ⟨l', hl'mem, hl'⟩ := hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl <;> simp [ih l' hl'mem]

theorem allBoolLists_complete : ∀ (l : List Bool), l ∈ allBoolLists l.length := by
  intro l
  induction l with
  | nil => simp [allBoolLists]
  | cons b l ih =>
      simp only [List.length_cons, allBoolLists, List.mem_flatMap]
      exact ⟨l, ih, by cases b <;> simp⟩

/-- The number whose little-endian bits are `σ` — a bounded, length-injective code
for a binary string (used to index tree membership in the oracle at a *bounded*
position, so a finite oracle prefix suffices). -/
def natOfBoolList : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * natOfBoolList l

theorem natOfBoolList_lt : ∀ σ : List Bool, natOfBoolList σ < 2 ^ σ.length
  | [] => by simp [natOfBoolList]
  | b :: l => by
      have := natOfBoolList_lt l
      simp only [natOfBoolList, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

theorem natOfBoolList_inj : ∀ {σ σ' : List Bool}, σ.length = σ'.length →
    natOfBoolList σ = natOfBoolList σ' → σ = σ'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, heq => by
      simp only [natOfBoolList] at heq
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hb : b = b' := by cases b <;> cases b' <;> simp_all <;> omega
      have hl : natOfBoolList l = natOfBoolList l' := by cases b <;> cases b' <;> simp_all <;> omega
      rw [hb, natOfBoolList_inj hlen hl]

end Martin
