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

/-! ### The invariant `RawPPT`, modulo `codeReal Y ≡ᵀ Y`

The three reflection lemmas reduce a genuine invariant `RawPPT` — and hence, via
`RawPPT.toPPT`/`lemma21`, a full `PPT` carrying the effective `recover` field — to
the single recursion-theoretic fact that the coding real is Turing-equivalent to
`Y`.  That fact is a pure computability statement (`codeReal Y` reads finitely
many bits of `Y`, and `Y` is read back off the tree prefix by prefix); it is the
one piece still to be discharged by an explicit reduction. -/

/-- Given `codeReal Y ≡ᵀ Y`, the even-`Y` coding tree is a genuine `RawPPT`. -/
noncomputable def coneRawPPT (Y : ℕ → Bool) (hequiv : codeReal Y ≡ₜ Y) : RawPPT where
  code := codeReal Y
  closed := closed_codeReal Y
  pointed := by
    intro x hx
    rw [isBranch_codeReal] at hx
    obtain ⟨Z, rfl⟩ := hx
    exact hequiv.1.trans (Cantor.left_le_join Y Z)
  realizes := by
    intro d hd
    have hYd : Y ≤ₜ d := hequiv.2.trans hd
    refine ⟨Cantor.join Y d, ?_, ?_⟩
    · rw [isBranch_codeReal]; exact ⟨d, rfl⟩
    · exact ⟨Cantor.join_le hYd (Cantor.le.refl d), Cantor.right_le_join Y d⟩

/-- **Full invariant Martin Lemma 2.3, modulo `codeReal · ≡ᵀ ·`.**  If the coding
real is Turing-equivalent to its parameter (a pure computability fact), then every
Turing-invariant cofinal determined set contains a *full* pointed perfect tree — a
`PPT` with the effective `recover` field supplied by `lemma21` — whose branches
lie in the set. -/
theorem invariant_cofinal_contains_PPT
    (hcode : ∀ Y : ℕ → Bool, codeReal Y ≡ₜ Y)
    (A : Set (ℕ → Bool)) (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hcof : Cofinal (· ∈ A)) (hDet : GameDetermined A) :
    ∃ T : PPT, ∀ x, T.mem x → x ∈ A := by
  obtain ⟨Y, hY⟩ := cone_of_invariant_cofinal A hTI hcof hDet
  refine ⟨(coneRawPPT Y (hcode Y)).toPPT, fun x hx => ?_⟩
  -- `T.mem` unfolds to `IsBranch (treeMem (codeReal Y))`, i.e. `CodedBranch Y`
  have : CodedBranch Y x := (isBranch_codeReal Y x).mp hx
  exact hY (coneEmbedding_pointed Y x this)

#print axioms treeMem_codeReal
#print axioms isBranch_codeReal
#print axioms invariant_cofinal_contains_PPT

end Martin
