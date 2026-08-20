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

/-- Boolean even-match test, over the positions of `σ`. -/
def evenMatchB (Y : ℕ → Bool) (σ : List Bool) : Bool :=
  (List.range σ.length).all (fun i => !(i % 2 == 0) || (σ.getD i false == Y (i / 2)))

theorem evenMatchB_iff (Y : ℕ → Bool) (σ : List Bool) :
    evenMatchB Y σ = true ↔ EvenMatch Y σ := by
  unfold evenMatchB EvenMatch
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    have := h (2 * k) (by simp only [List.mem_range]; omega)
    simp only [Nat.mul_mod_right, beq_self_eq_true, Bool.not_true, Bool.false_or,
      beq_iff_eq] at this
    rwa [show 2 * k / 2 = k by omega] at this
  · intro h i hi
    simp only [List.mem_range] at hi
    rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hget : (σ.getD (k + k) false == Y ((k + k) / 2)) = true := by
        rw [beq_iff_eq, show (k + k) / 2 = k by omega, show k + k = 2 * k by omega]
        exact h k (by omega)
      simp only [hget, Bool.or_true]
    · rw [show (2 * k + 1) % 2 = 1 by omega]; rfl

/-- Characteristic real of the even-`Y` coding tree: at `treePos σ` it records
whether `σ`'s even positions match `Y`, found by a bounded search over the finite
strings.  Constructive (so its computability from `Y` is reachable); off the range
of `treePos` it is `false`, which is irrelevant since `treeMem` reads only
`treePos` positions. -/
def codeReal (Y : ℕ → Bool) (p : ℕ) : Bool :=
  (List.range (p + 1)).any (fun L =>
    (allBoolLists L).any (fun σ => (treePos σ == p) && evenMatchB Y σ))

/-- The search evaluates the even-match test at the (unique) string coded by
`treePos σ`. -/
theorem codeReal_treePos (Y : ℕ → Bool) (σ : List Bool) :
    codeReal Y (treePos σ) = evenMatchB Y σ := by
  unfold codeReal
  have hlen : σ.length < treePos σ + 1 := by
    have := Nat.lt_two_pow_self (n := σ.length)
    unfold treePos; omega
  cases hem : evenMatchB Y σ with
  | true =>
    rw [List.any_eq_true]
    exact ⟨σ.length, by simp only [List.mem_range]; omega, by
      rw [List.any_eq_true]
      exact ⟨σ, allBoolLists_complete σ, by simp [hem]⟩⟩
  | false =>
    rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨L, _, hL⟩
    rw [List.any_eq_true] at hL
    obtain ⟨σ', _, hσ'⟩ := hL
    simp only [Bool.and_eq_true, beq_iff_eq] at hσ'
    obtain ⟨hpos, hev⟩ := hσ'
    have : σ' = σ := treePos_inj hpos
    subst this; rw [hem] at hev; exact Bool.false_ne_true hev

/-- Membership in the coding tree is exactly the even-match predicate. -/
theorem treeMem_codeReal (Y : ℕ → Bool) (σ : List Bool) :
    treeMem (codeReal Y) σ ↔ EvenMatch Y σ := by
  unfold treeMem
  rw [codeReal_treePos, evenMatchB_iff]

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
