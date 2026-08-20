/-
**The `Y`-coding tree in the `treeMem` coding.**

`ConeTree.lean` built the pointed / realizing / perfect content of the cone tree
abstractly (`CodedBranch Y = {join Y Z}`).  To obtain a genuine `RawPPT` — and
hence, via `RawPPT.toPPT`/`lemma21`, the effective `recover` field — the tree must
be presented in the `treeMem` coding used by `lemma21`: a characteristic real
`codeReal Y` whose branches are exactly the even-`Y` reals.

This file supplies the *combinatorial* reflection (`treeMem_codeReal`,
`closed_codeReal`, `isBranch_codeReal`), reducing a full invariant `RawPPT` to the
single recursion-theoretic fact `codeReal Y ≡ᵀ Y`.
-/
import MartinsConjecture.RawPPT
import MartinsConjecture.ConeTree

open scoped Computability
open Cantor
open Classical

namespace Martin

/-- `σ`'s even positions spell the prefix of `Y`. -/
def EvenMatch (Y : ℕ → Bool) (σ : List Bool) : Prop :=
  ∀ k, 2 * k < σ.length → σ.getD (2 * k) false = Y k

/-- Characteristic real of the even-`Y` coding tree: at position `treePos σ` it
records whether `σ`'s even positions match `Y`.  (Off the range of `treePos` the
value is irrelevant, since `treeMem` only reads `treePos` positions.) -/
noncomputable def codeReal (Y : ℕ → Bool) (p : ℕ) : Bool :=
  if (∀ σ : List Bool, treePos σ = p → EvenMatch Y σ) then true else false

/-- Membership in the coding tree is exactly the even-match predicate. -/
theorem treeMem_codeReal (Y : ℕ → Bool) (σ : List Bool) :
    treeMem (codeReal Y) σ ↔ EvenMatch Y σ := by
  unfold treeMem codeReal
  by_cases hall : ∀ σ' : List Bool, treePos σ' = treePos σ → EvenMatch Y σ'
  · rw [if_pos hall]
    exact ⟨fun _ => hall σ rfl, fun _ => rfl⟩
  · rw [if_neg hall]
    refine ⟨fun h => absurd h Bool.false_ne_true, fun hEM => absurd (fun σ' hσ' => ?_) hall⟩
    have : σ' = σ := treePos_inj hσ'
    subst this; exact hEM

/-- The coding tree is downward closed. -/
theorem closed_codeReal (Y : ℕ → Bool) :
    ∀ σ b, treeMem (codeReal Y) (σ ++ [b]) → treeMem (codeReal Y) σ := by
  intro σ b h
  rw [treeMem_codeReal] at h ⊢
  intro k hk
  have hk' : 2 * k < (σ ++ [b]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hval := h k hk'
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk] at hval
  rw [List.getD_eq_getElem?_getD]
  exact hval

/-- A real is a branch of the coding tree iff its even bits spell `Y` — i.e. iff
it is `join Y Z` for some `Z` (`CodedBranch Y`). -/
theorem isBranch_codeReal (Y : ℕ → Bool) (x : ℕ → Bool) :
    IsBranch (treeMem (codeReal Y)) x ↔ CodedBranch Y x := by
  simp only [IsBranch, treeMem_codeReal]
  constructor
  · intro h
    -- every even bit of `x` equals the corresponding bit of `Y`
    have heven : ∀ k, x (2 * k) = Y k := by
      intro k
      have hmatch := h (2 * k + 1) k (by
        simp only [List.length_map, List.length_range]; omega)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega), Option.map_some, Option.getD_some] at hmatch
    refine ⟨fun k => x (2 * k + 1), ?_⟩
    funext n
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [Cantor.join, if_pos (by omega), show (k + k) / 2 = k by omega,
        show k + k = 2 * k by omega]
      exact heven k
    · rw [Cantor.join, if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
  · rintro ⟨Z, rfl⟩ n k hk
    simp only [List.length_map, List.length_range] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some, Cantor.join,
      if_pos (by omega), show 2 * k / 2 = k by omega]

#print axioms treeMem_codeReal
#print axioms isBranch_codeReal

end Martin
