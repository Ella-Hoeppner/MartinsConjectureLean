/-
Discharging `HasCodingFamily`: the coding-real construction for Lachlan's
discontinuous case.

Given the discontinuity data at a marker `n₀` (no prefix of `X` halts the
operator `e` at `n₀`, but every prefix has a `0/1` extension that does), we
build, for each machine index `c`, a real `Y_c ≡ᵀ X` such that
`n₀ ∈ W^{Y_c} ⟺ Φ_c^X(c)↓` — so the operator at `n₀` reads off the jump of `X`.

The construction (`yc`) *inserts* the least `0/1` marker-witness at the halting
stage of `Φ_c^X(c)`: `Y_c = X` until that computation halts (which never happens
if it diverges), then the witness `w`, then the tail of `X` shifted right by
`|w|`.  This preserves `Y_c ≡ᵀ X` (the shift is invertible, and `Φ_c`'s use lies
below the halting stage, where `Y_c = X`) while forcing the marker into `W^{Y_c}`
exactly when `Φ_c^X(c)` converges.

This file develops the halting-stage machinery and the coding real; the two
Turing reductions as explicit s-m-n codes (building on `univCode`) assemble it
into `HasCodingFamily`.
-/
import MartinsConjecture.DiscontinuousCase
import MartinsConjecture.UniversalCode

open scoped Computability
open OracleCode Cantor

namespace OracleCode
namespace Coding

attribute [local instance] Classical.propDecidable

/-- The oracle bit of a Boolean. -/
def bbit (b : Bool) : ℕ := bif b then 1 else 0

@[simp] theorem bbit_eq (b : Bool) : bbit b = bitg (fun _ => b) 0 := by
  cases b <;> rfl

theorem bitg_eq_bbit (Y : ℕ → Bool) (m : ℕ) : bitg Y m = bbit (Y m) := rfl

/-- `Φ_c^X(c)` halts within `m` steps (bounded simulation with the length-`m`
prefix of `X`'s graph). -/
def haltedB (X : ℕ → Bool) (c m : ℕ) : Bool :=
  (evaln m (graphOf (bitg X) m) (ofNatCode c) c).isSome

theorem haltedB_mono (X : ℕ → Bool) (c : ℕ) {m m' : ℕ} (h : m ≤ m')
    (hm : haltedB X c m = true) : haltedB X c m' = true := by
  rw [haltedB] at hm ⊢
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  rw [evaln_mono h (graphOf_prefix h) hv]; rfl

/-- `Φ_c^X(c)` converges. -/
def conv (X : ℕ → Bool) (c : ℕ) : Prop := ∃ m, haltedB X c m = true

instance (X : ℕ → Bool) (c : ℕ) : DecidablePred (fun m => haltedB X c m = true) :=
  fun _ => decEq _ _

/-- Convergence of the bounded simulation matches convergence of `Φ_c^X(c)`,
i.e. `c ∈ X′`. -/
theorem conv_iff_jump (X : ℕ → Bool) (c : ℕ) :
    conv X c ↔ Cantor.jump X c = true := by
  rw [Cantor.jump]
  simp only [decide_eq_true_eq]
  rw [jumpP, mem_reReal_iff_haltsOn_prefix]
  constructor
  · rintro ⟨m, hm⟩
    rw [haltedB] at hm
    exact ⟨m, m, hm⟩
  · rintro ⟨ℓ, s, hs⟩
    refine ⟨max ℓ s, ?_⟩
    rw [haltedB]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [evaln_mono (le_max_right ℓ s) (graphOf_prefix (le_max_left ℓ s)) hv]; rfl

open Classical in
/-- The halting stage of `Φ_c^X(c)` (`0` if it diverges — unused there). -/
noncomputable def hStage (X : ℕ → Bool) (c : ℕ) : ℕ :=
  if h : conv X c then Nat.find h else 0

theorem haltedB_hStage (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    haltedB X c (hStage X c) = true := by
  rw [hStage, dif_pos h]; exact Nat.find_spec h

theorem not_haltedB_lt_hStage (X : ℕ → Bool) (c : ℕ) (h : conv X c) {m : ℕ}
    (hm : m < hStage X c) : haltedB X c m = false := by
  rw [hStage, dif_pos h] at hm
  have := Nat.find_min h hm
  simpa using this

theorem haltedB_iff_ge_hStage (X : ℕ → Bool) (c : ℕ) (h : conv X c) (m : ℕ) :
    haltedB X c m = true ↔ hStage X c ≤ m := by
  constructor
  · intro hm
    by_contra hlt
    push_neg at hlt
    rw [not_haltedB_lt_hStage X c h hlt] at hm
    exact Bool.noConfusion hm
  · intro hle
    exact haltedB_mono X c hle (haltedB_hStage X c h)

/-! ### The marker witness and the coding real -/

/-- Whether the `⟨witness, step⟩` pair `p` shows `X↾t ⌢ (decode p.1)` halts the
operator at the marker within `p.2` steps.  Decidable, hence its least witness
is found by a genuine `μ`-search (unlike "least `k` with `haltsOn`", which is
only `Σ₁`). -/
def witPair (e n₀ : ℕ) (X : ℕ → Bool) (t p : ℕ) : Bool :=
  (evaln (Nat.unpair p).2 (graphOf (bitg X) t
    ++ ((Encodable.decode (α := List Bool) (Nat.unpair p).1).getD []).map bbit)
    (ofNatCode e) n₀).isSome

open Classical in
/-- Encoding of the least witnessing pair for the marker at stage `t`. -/
noncomputable def witEnc (e n₀ : ℕ) (X : ℕ → Bool) (t : ℕ) : ℕ :=
  if h : ∃ p, witPair e n₀ X t p = true then Nat.find h else 0

/-- The marker-witnessing `0/1` extension of `X↾t` from the least witnessing pair. -/
noncomputable def wit (e n₀ : ℕ) (X : ℕ → Bool) (t : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) (Nat.unpair (witEnc e n₀ X t)).1).getD []

theorem wit_spec (e n₀ : ℕ) (X : ℕ → Bool) (t : ℕ)
    (h : ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    haltsOn (graphOf (bitg X) t ++ (wit e n₀ X t).map bbit) e n₀ := by
  have hp : ∃ p, witPair e n₀ X t p = true := by
    obtain ⟨w, s, hs⟩ := h
    refine ⟨Nat.pair (Encodable.encode w) s, ?_⟩
    simp only [witPair, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    exact hs
  have hwe : witEnc e n₀ X t = Nat.find hp := dif_pos hp
  have hspec := Nat.find_spec hp
  rw [witPair] at hspec
  refine ⟨(Nat.unpair (witEnc e n₀ X t)).2, ?_⟩
  rw [hwe, wit, hwe]
  exact hspec

open Classical in
/-- The coding real `Y_c`: copy `X` until `Φ_c^X(c)` halts (stage `t`), then
insert the least marker witness `w`, then the tail of `X` shifted right by `|w|`. -/
noncomputable def yc (e n₀ : ℕ) (X : ℕ → Bool) (c m : ℕ) : Bool :=
  bif haltedB X c m then
    (if m < hStage X c + (wit e n₀ X (hStage X c)).length
     then (wit e n₀ X (hStage X c)).getD (m - hStage X c) false
     else X (m - (wit e n₀ X (hStage X c)).length))
  else X m

/-- Below the halting stage, `Y_c` copies `X`. -/
theorem yc_eq_lt (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) {j : ℕ}
    (hj : j < hStage X c) : yc e n₀ X c j = X j := by
  rw [yc, not_haltedB_lt_hStage X c h hj]; rfl

/-- On the witness segment, `Y_c` reads off the witness. -/
theorem yc_eq_wit (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) {i : ℕ}
    (hi : i < (wit e n₀ X (hStage X c)).length) :
    yc e n₀ X c (hStage X c + i) = (wit e n₀ X (hStage X c)).getD i false := by
  have hh : haltedB X c (hStage X c + i) = true :=
    haltedB_mono X c (Nat.le_add_right _ _) (haltedB_hStage X c h)
  rw [yc, hh]
  simp only [cond_true, Nat.add_sub_cancel_left]
  rw [if_pos (by omega)]

/-- If `Φ_c^X(c)` diverges, `Y_c = X`. -/
theorem yc_eq_of_not_conv (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : ¬ conv X c) (m : ℕ) :
    yc e n₀ X c m = X m := by
  have : haltedB X c m = false := by
    by_contra hm
    rw [Bool.not_eq_false] at hm
    exact h ⟨m, hm⟩
  rw [yc, this]; rfl

/-- **The graph agreement**: at length `t + |w|`, the graph of `Y_c` is exactly
`X↾t ⌢ w`. -/
theorem graphOf_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    graphOf (bitg (yc e n₀ X c)) (hStage X c + (wit e n₀ X (hStage X c)).length)
      = graphOf (bitg X) (hStage X c) ++ (wit e n₀ X (hStage X c)).map bbit := by
  set t := hStage X c with ht
  set w := wit e n₀ X t with hw
  apply List.ext_getElem
  · simp only [graphOf, List.length_map, List.length_range, List.length_append]
  · intro j hj1 hj2
    simp only [graphOf, List.length_map, List.length_range] at hj1
    simp only [graphOf]
    rcases lt_or_ge j t with hjt | hjt
    · -- first segment: copies X
      rw [List.getElem_map, List.getElem_range, List.getElem_append_left
          (by simp only [List.length_map, List.length_range]; exact hjt),
        List.getElem_map, List.getElem_range, bitg_eq_bbit, bitg_eq_bbit,
        yc_eq_lt e n₀ X c h hjt]
    · -- witness segment
      have hji : j - t < w.length := by omega
      rw [List.getElem_map, List.getElem_range, List.getElem_append_right
          (by simp only [List.length_map, List.length_range]; exact hjt)]
      simp only [List.length_map, List.length_range]
      rw [List.getElem_map, bitg_eq_bbit]
      have hje : j = t + (j - t) := by omega
      have hyc : yc e n₀ X c j = w.getD (j - t) false := by
        conv_lhs => rw [hje]
        exact yc_eq_wit e n₀ X c h hji
      rw [hyc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hji, Option.getD_some]

/-- **The marker property.**  Under the discontinuity data — no prefix of `X`
halts the operator at `n₀` (`hnp`), and every prefix has a `0/1` marker-witnessing
extension (`hd`) — the operator at `n₀` over `Y_c` is true exactly when
`Φ_c^X(c)` converges, i.e. `c ∈ X′`. -/
theorem marker_property (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ)
    (hnp : ∀ ℓ, ¬ haltsOn (graphOf (bitg X) ℓ) e n₀)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    reReal e (yc e n₀ X c) n₀ = true ↔ Cantor.jump X c = true := by
  rw [← conv_iff_jump]
  constructor
  · -- if the operator fires, `Φ_c^X(c)` must converge (else `Y_c = X`, contradicting `hnp`)
    intro hre
    by_contra hnc
    rw [reReal_eq_true_iff] at hre
    obtain ⟨ℓ, hℓ⟩ := hre
    apply hnp ℓ
    have : bitg (yc e n₀ X c) = bitg X := by
      funext m; rw [bitg_eq_bbit, bitg_eq_bbit, yc_eq_of_not_conv e n₀ X c hnc m]
    rwa [this] at hℓ
  · -- if `Φ_c^X(c)` converges, the spliced witness fires the operator
    intro hconv
    rw [reReal_eq_true_iff]
    refine ⟨hStage X c + (wit e n₀ X (hStage X c)).length, ?_⟩
    rw [graphOf_yc e n₀ X c hconv]
    exact wit_spec e n₀ X (hStage X c) (hd (hStage X c))

end Coding
end OracleCode
