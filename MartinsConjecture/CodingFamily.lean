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

/-! ### Forward reduction groundwork: the halted bit is `X`-recursive -/

/-- `haltedB X c m` equals the `isSome` of the universal decoder on the packed
input, so it is recursive in `X` (bounded simulation via the oracle's own graph). -/
theorem haltedB_eq_uEvalnD (X : ℕ → Bool) (c m : ℕ) :
    haltedB X c m
      = (uEvalnD (Nat.pair (Nat.pair (Nat.pair c c) m)
          (Encodable.encode (graphOf (bitg X) m)))).isSome := by
  rw [haltedB, uEvalnD_graph]
  simp only [Nat.unpair_pair]

/-- The halted bit `⟨c,m⟩ ↦ [Φ_c^X(c) halts within m steps]` is recursive in `X`. -/
theorem haltedBit_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X}
      (fun q => ((bif haltedB X (Nat.unpair q).1 (Nat.unpair q).2 then 1 else 0 : ℕ) : Part ℕ)) := by
  have hg : Nat.RecursiveIn {toPFun X} (fun q => graphEnc X (Nat.unpair q).2) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))).of_eq
      fun q => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun X}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> graphEnc X (Nat.unpair q).2) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec fun w =>
      (bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair w).1).1
        (Nat.unpair (Nat.unpair w).1).1) (Nat.unpair (Nat.unpair w).1).2)
        (Nat.unpair w).2)).isSome then 1 else 0 : ℕ) := by
    refine Primrec.nat_iff.mp (Primrec.cond
      (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_))
      (Primrec.const 1) (Primrec.const 0))
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp Primrec.unpair)
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun q => ?_
  rw [show graphEnc X (Nat.unpair q).2
      = Part.some (Encodable.encode (graphOf (bitg X) (Nat.unpair q).2)) from rfl]
  simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]
  rw [← haltedB_eq_uEvalnD]

#print axioms haltedBit_recursiveIn

/-- The **complemented** halted bit (`0` when halted), for the `hStage` search. -/
theorem notHaltedBit_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X}
      (fun q => ((bif haltedB X (Nat.unpair q).1 (Nat.unpair q).2 then 0 else 1 : ℕ) : Part ℕ)) := by
  have hg : Nat.RecursiveIn {toPFun X} (fun q => graphEnc X (Nat.unpair q).2) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))).of_eq
      fun q => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun X}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> graphEnc X (Nat.unpair q).2) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec fun w =>
      (bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair w).1).1
        (Nat.unpair (Nat.unpair w).1).1) (Nat.unpair (Nat.unpair w).1).2)
        (Nat.unpair w).2)).isSome then 0 else 1 : ℕ) := by
    refine Primrec.nat_iff.mp (Primrec.cond
      (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_))
      (Primrec.const 0) (Primrec.const 1))
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp Primrec.unpair)
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun q => ?_
  rw [show graphEnc X (Nat.unpair q).2
      = Part.some (Encodable.encode (graphOf (bitg X) (Nat.unpair q).2)) from rfl]
  simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]
  rw [← haltedB_eq_uEvalnD]

/-- The `hStage` search: `μ m'. haltedB X c m'`, recursive in `X`. -/
theorem hStageSearch_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X} (fun c => Nat.rfind fun m' =>
      (fun x => x = 0) <$> ((bif haltedB X c m' then 0 else 1 : ℕ) : Part ℕ)) :=
  (Nat.RecursiveIn.rfind (notHaltedBit_recursiveIn X)).of_eq fun c => by
    simp only [Nat.unpair_pair]

/-- When `Φ_c^X(c)` converges, the search returns the halting stage `hStage X c`.
Stated in the `Part.some (decide …)` form the search takes after `simp`. -/
theorem hStageSearch_eq (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    (Nat.rfind fun m' => (Part.some (decide ((bif haltedB X c m' then 0 else 1) = 0)) : Part Bool))
      = Part.some (hStage X c) := by
  refine Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩)
  · rw [Part.mem_some_iff, haltedB_hStage X c h]; rfl
  · rw [Part.mem_some_iff, not_haltedB_lt_hStage X c h hm]; rfl

#print axioms hStageSearch_eq

/-! ### The witness μ-search is `X`-recursive -/

/-- Encode the oracle table `X↾t ⌢ (decoded witness of p)` from `encode (X↾t)` and `p`. -/
def encTable (g p : ℕ) : ℕ :=
  Encodable.encode ((Encodable.decode (α := List ℕ) g).getD []
    ++ ((Encodable.decode (α := List Bool) (Nat.unpair p).1).getD []).map bbit)

theorem bbit_prim : Primrec bbit :=
  Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)

theorem encTable_prim : Primrec₂ encTable :=
  Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const ([] : List ℕ)))
    ((Primrec.list_map (Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
        (Primrec.const ([] : List Bool))) (bbit_prim.comp Primrec.snd).to₂)))

theorem witPair_eq_uEvalnD (e n₀ : ℕ) (X : ℕ → Bool) (t p : ℕ) :
    witPair e n₀ X t p
      = (uEvalnD (Nat.pair (Nat.pair (Nat.pair e n₀) (Nat.unpair p).2)
          (encTable (Encodable.encode (graphOf (bitg X) t)) p))).isSome := by
  rw [witPair, uEvalnD, encTable]
  simp [Nat.unpair_pair, Encodable.encodek]

/-- The witness-pair test `⟨t,p⟩ ↦ [pair p witnesses at stage t]` (`0` when it does),
recursive in `X`. -/
theorem witPairVal_recursiveIn (e n₀ : ℕ) (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X}
      (fun w => ((bif witPair e n₀ X (Nat.unpair w).1 (Nat.unpair w).2 then 0 else 1 : ℕ)
        : Part ℕ)) := by
  have hg : Nat.RecursiveIn {toPFun X} (fun w => graphEnc X (Nat.unpair w).1) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun w => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun X} (fun w : ℕ => ((w : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun X}
      (fun w => Nat.pair <$> ((w : ℕ) : Part ℕ) <*> graphEnc X (Nat.unpair w).1) :=
    Nat.RecursiveIn.pair hid hg
  -- primrec test on ⟨w, g⟩: g = encode (graphOf X t)
  have htest : Nat.Primrec fun z =>
      (bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair e n₀)
        (Nat.unpair (Nat.unpair (Nat.unpair z).1).2).2)
        (encTable (Nat.unpair z).2 (Nat.unpair (Nat.unpair z).1).2))).isSome
      then 0 else 1 : ℕ) := by
    refine Primrec.nat_iff.mp (Primrec.cond
      (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_)) (Primrec.const 0) (Primrec.const 1))
    refine Primrec₂.natPair.comp (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.const e) (Primrec.const n₀))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))) ?_
    exact encTable_prim.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun w => ?_
  rw [show graphEnc X (Nat.unpair w).1
      = Part.some (Encodable.encode (graphOf (bitg X) (Nat.unpair w).1)) from rfl]
  simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]
  rw [← witPair_eq_uEvalnD]

/-- The witness search, recursive in `X`. -/
theorem witEncSearch_recursiveIn (e n₀ : ℕ) (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X} (fun t => Nat.rfind fun p =>
      (fun x => x = 0) <$> ((bif witPair e n₀ X t p then 0 else 1 : ℕ) : Part ℕ)) :=
  (Nat.RecursiveIn.rfind (witPairVal_recursiveIn e n₀ X)).of_eq fun t => by
    simp only [Nat.unpair_pair]

/-- When a `0/1` witness exists at stage `t`, the search returns `witEnc e n₀ X t`. -/
theorem witEncSearch_eq (e n₀ : ℕ) (X : ℕ → Bool) (t : ℕ)
    (h : ∃ p, witPair e n₀ X t p = true) :
    (Nat.rfind fun p => (Part.some (decide ((bif witPair e n₀ X t p then 0 else 1) = 0)) : Part Bool))
      = Part.some (witEnc e n₀ X t) := by
  have hwe : witEnc e n₀ X t = Nat.find h := dif_pos h
  refine Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩)
  · rw [Part.mem_some_iff, hwe, Nat.find_spec h]; rfl
  · rw [Part.mem_some_iff]
    rw [hwe] at hm
    have hf := Nat.find_min h hm
    rw [Bool.not_eq_true] at hf
    rw [hf]; rfl

#print axioms witEncSearch_eq

/-! ### The shift value and the assembled forward reduction -/

/-- The decoded witness list packed in `z = ⟨m, ⟨t, we⟩⟩`. -/
def zWit (z : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) (Nat.unpair (Nat.unpair (Nat.unpair z).2).2).1).getD []

/-- The `X`-query index for the shifted tail: `m - |w|`. -/
def shiftIdx (z : ℕ) : ℕ := (Nat.unpair z).1 - (zWit z).length

/-- Given the query value `v = bitg X (m - |w|)` (in `zv = ⟨z, v⟩`), select the
witness bit or the shifted tail bit. -/
def shiftSelect (zv : ℕ) : ℕ :=
  if (Nat.unpair (Nat.unpair zv).1).1
      < (Nat.unpair (Nat.unpair (Nat.unpair zv).1).2).1 + (zWit (Nat.unpair zv).1).length
  then bbit ((zWit (Nat.unpair zv).1).getD
      ((Nat.unpair (Nat.unpair zv).1).1 - (Nat.unpair (Nat.unpair (Nat.unpair zv).1).2).1) false)
  else (Nat.unpair zv).2

theorem zWit_prim : Primrec zWit :=
  Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const ([] : List Bool))

theorem shiftIdx_prim : Primrec shiftIdx :=
  Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.list_length.comp zWit_prim)

theorem shiftSelect_prim : Primrec shiftSelect := by
  have hm : Primrec fun zv => (Nat.unpair (Nat.unpair zv).1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have ht : Primrec fun zv => (Nat.unpair (Nat.unpair (Nat.unpair zv).1).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  have hw : Primrec fun zv => zWit (Nat.unpair zv).1 :=
    zWit_prim.comp (Primrec.fst.comp Primrec.unpair)
  refine Primrec.ite (Primrec.nat_lt.comp hm (Primrec.nat_add.comp ht
    (Primrec.list_length.comp hw))) ?_ (Primrec.snd.comp Primrec.unpair)
  exact bbit_prim.comp ((Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hw (Primrec.nat_sub.comp hm ht)) (Primrec.const false)).of_eq
    fun _ => (List.getD_eq_getElem?_getD ..).symm)

/-- The shift value is recursive in `X`: compute the shifted-tail query, then select. -/
theorem shiftVal_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X} (fun z => ((shiftSelect (Nat.pair z (bitg X (shiftIdx z))) : ℕ)
      : Part ℕ)) := by
  have hquery : Nat.RecursiveIn {toPFun X}
      (fun z => Nat.pair <$> ((z : ℕ) : Part ℕ)
        <*> (((shiftIdx z : ℕ) : Part ℕ) >>= toPFun X)) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn)
      (Nat.RecursiveIn.comp (.oracle _ rfl) (Primrec.nat_iff.mp shiftIdx_prim).recursiveIn)
  refine (Nat.RecursiveIn.comp (Primrec.nat_iff.mp shiftSelect_prim).recursiveIn hquery).of_eq
    fun z => ?_
  rw [show (((shiftIdx z : ℕ) : Part ℕ) >>= toPFun X) = Part.some (bitg X (shiftIdx z)) from by
    rw [Part.coe_some]; exact (Part.bind_some _ _).trans (toPFun_eq_bitg X _)]
  simp only [Seq.seq, Part.map_eq_map, Part.coe_some, Part.map_some, Part.bind_eq_bind,
    Part.bind_some]

#print axioms shiftVal_recursiveIn

/-- Repack `⟨⟨q,t⟩,we⟩ ↦ ⟨m, ⟨t, we⟩⟩` (extract `m` from `q`) for the shift value. -/
def repackFn (Z : ℕ) : ℕ :=
  Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair Z).1).1).2
    (Nat.pair (Nat.unpair (Nat.unpair Z).1).2 (Nat.unpair Z).2)

theorem repackFn_prim : Primrec repackFn :=
  Primrec₂.natPair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

/-- The splice value at `q = ⟨c,m⟩`, recursive in `X`: run both searches, then shift. -/
theorem spl_recursiveIn (e n₀ : ℕ) (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X} (fun q =>
      (Nat.rfind fun m' => (fun x => x = 0) <$>
          ((bif haltedB X (Nat.unpair q).1 m' then 0 else 1 : ℕ) : Part ℕ)) >>= fun t =>
      (Nat.rfind fun p => (fun x => x = 0) <$>
          ((bif witPair e n₀ X t p then 0 else 1 : ℕ) : Part ℕ)) >>= fun we =>
      ((shiftSelect (Nat.pair (repackFn (Nat.pair (Nat.pair q t) we))
        (bitg X (shiftIdx (repackFn (Nat.pair (Nat.pair q t) we))))) : ℕ) : Part ℕ)) := by
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hT : Nat.RecursiveIn {toPFun X} (fun q => (Nat.rfind fun m' => (fun x => x = 0) <$>
      ((bif haltedB X (Nat.unpair q).1 m' then 0 else 1 : ℕ) : Part ℕ))) :=
    (Nat.RecursiveIn.comp (hStageSearch_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun q => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hWE : Nat.RecursiveIn {toPFun X} (fun qt => (Nat.rfind fun p => (fun x => x = 0) <$>
      ((bif witPair e n₀ X (Nat.unpair qt).2 p then 0 else 1 : ℕ) : Part ℕ))) :=
    (Nat.RecursiveIn.comp (witEncSearch_recursiveIn e n₀ X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))).of_eq
      fun qt => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hstep1 : Nat.RecursiveIn {toPFun X}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> _) := Nat.RecursiveIn.pair hid hT
  have hstep2 : Nat.RecursiveIn {toPFun X}
      (fun qt => Nat.pair <$> ((qt : ℕ) : Part ℕ) <*> _) := Nat.RecursiveIn.pair hid hWE
  have hrepack : Nat.RecursiveIn {toPFun X}
      (fun Z => ((repackFn Z : ℕ) : Part ℕ)) := (Primrec.nat_iff.mp repackFn_prim).recursiveIn
  refine ((Nat.RecursiveIn.comp (shiftVal_recursiveIn X)
    (Nat.RecursiveIn.comp hrepack
      (Nat.RecursiveIn.comp hstep2 hstep1)))).of_eq fun q => ?_
  apply Part.ext; intro y
  simp only [Seq.seq, Part.map_eq_map, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
    Part.map_some, Part.mem_bind_iff, Part.mem_map_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨R, ⟨Z, ⟨qt, ⟨t, ht, rfl⟩, we, hwe, rfl⟩, rfl⟩, hy⟩
    rw [Nat.unpair_pair] at hwe
    exact ⟨t, ht, we, hwe, hy⟩
  · rintro ⟨t, ht, we, hwe, hy⟩
    refine ⟨_, ⟨_, ⟨_, ⟨t, ht, rfl⟩, we, ?_, rfl⟩, rfl⟩, hy⟩
    rw [Nat.unpair_pair]; exact hwe

#print axioms spl_recursiveIn

/-- In the halted branch, the computed shift value equals the bit of `Y_c`. -/
theorem shift_eq_yc (e n₀ : ℕ) (X : ℕ → Bool) (q : ℕ) (h : conv X (Nat.unpair q).1)
    (hm : hStage X (Nat.unpair q).1 ≤ (Nat.unpair q).2) :
    shiftSelect (Nat.pair
      (repackFn (Nat.pair (Nat.pair q (hStage X (Nat.unpair q).1))
        (witEnc e n₀ X (hStage X (Nat.unpair q).1))))
      (bitg X (shiftIdx (repackFn (Nat.pair (Nat.pair q (hStage X (Nat.unpair q).1))
        (witEnc e n₀ X (hStage X (Nat.unpair q).1)))))))
      = bitg (yc e n₀ X (Nat.unpair q).1) (Nat.unpair q).2 := by
  have hrp : repackFn (Nat.pair (Nat.pair q (hStage X (Nat.unpair q).1))
      (witEnc e n₀ X (hStage X (Nat.unpair q).1)))
      = Nat.pair (Nat.unpair q).2 (Nat.pair (hStage X (Nat.unpair q).1)
        (witEnc e n₀ X (hStage X (Nat.unpair q).1))) := by
    simp only [repackFn, Nat.unpair_pair]
  rw [hrp]
  have hhalt : haltedB X (Nat.unpair q).1 (Nat.unpair q).2 = true :=
    (haltedB_iff_ge_hStage X _ h _).mpr hm
  simp only [shiftSelect, shiftIdx, zWit, Nat.unpair_pair, bitg_eq_bbit, yc, hhalt, cond_true]
  rw [wit]
  split_ifs <;> rfl

theorem nat_rec_bif_false {α : Sort*} (base : α) (step : ℕ → α → α) :
    Nat.rec (motive := fun _ => α) base step (bif (false : Bool) then 1 else 0) = base := rfl

theorem nat_rec_bif_true {α : Sort*} (base : α) (step : ℕ → α → α) :
    Nat.rec (motive := fun _ => α) base step (bif (true : Bool) then 1 else 0) = step 0 base := rfl

/-- **The forward reduction is `X`-recursive** (uniformly in `c`): the two-argument
map `⟨c,m⟩ ↦ bitg (Y_c) m` is recursive in `X`.  Assembles the halted bit (a lazy
`prec`-selection between the base value `bitg X m` and the splice) with correctness
via `hStageSearch_eq`, `witEncSearch_eq`, and `shift_eq_yc`. -/
theorem ycBit_recursiveIn (e n₀ : ℕ) (X : ℕ → Bool)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    Nat.RecursiveIn {toPFun X}
      (fun q => ((bitg (yc e n₀ X (Nat.unpair q).1) (Nat.unpair q).2 : ℕ) : Part ℕ)) := by
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hbitg : Nat.RecursiveIn {toPFun X} (fun n => ((bitg X n : ℕ) : Part ℕ)) :=
    Cantor.le_iff_bitg.mp (Cantor.le.refl X)
  have cBase : Nat.RecursiveIn {toPFun X} (fun a => ((bitg X (Nat.unpair a).2 : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp hbitg
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))).of_eq
      fun a => by rw [Part.coe_some]; exact Part.bind_some _ _
  have cStep : Nat.RecursiveIn {toPFun X} (fun z =>
      (Nat.rfind fun m' => (fun x => x = 0) <$>
          ((bif haltedB X (Nat.unpair (Nat.unpair z).1).1 m' then 0 else 1 : ℕ) : Part ℕ)) >>= fun t =>
      (Nat.rfind fun p => (fun x => x = 0) <$>
          ((bif witPair e n₀ X t p then 0 else 1 : ℕ) : Part ℕ)) >>= fun we =>
      ((shiftSelect (Nat.pair (repackFn (Nat.pair (Nat.pair (Nat.unpair z).1 t) we))
        (bitg X (shiftIdx (repackFn (Nat.pair (Nat.pair (Nat.unpair z).1 t) we))))) : ℕ)
        : Part ℕ)) :=
    (Nat.RecursiveIn.comp (spl_recursiveIn e n₀ X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.fst.comp Primrec.unpair)))).of_eq
      fun z => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hpair : Nat.RecursiveIn {toPFun X}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ)
        <*> ((bif haltedB X (Nat.unpair q).1 (Nat.unpair q).2 then 1 else 0 : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.pair hid (haltedBit_recursiveIn X)
  refine (Nat.RecursiveIn.comp (Nat.RecursiveIn.prec cBase cStep) hpair).of_eq fun q => ?_
  -- reduce the comp to a case on `haltedB`
  simp only [Seq.seq, Part.map_eq_map, Part.coe_some, Part.map_some, Part.bind_eq_bind,
    Part.bind_some, Nat.unpair_pair]
  by_cases hh : haltedB X (Nat.unpair q).1 (Nat.unpair q).2 = true
  · -- halted: the splice branch, `= bitg (yc)` via the search-eq lemmas
    have hconv : conv X (Nat.unpair q).1 := ⟨_, hh⟩
    have hge : hStage X (Nat.unpair q).1 ≤ (Nat.unpair q).2 :=
      (haltedB_iff_ge_hStage X _ hconv _).mp hh
    have hwp : ∃ p, witPair e n₀ X (hStage X (Nat.unpair q).1) p = true := by
      obtain ⟨s, hs⟩ := wit_spec e n₀ X (hStage X (Nat.unpair q).1) (hd _)
      refine ⟨Nat.pair (Encodable.encode (wit e n₀ X (hStage X (Nat.unpair q).1))) s, ?_⟩
      simp only [witPair, Nat.unpair_pair, Encodable.encodek, Option.getD_some]; exact hs
    rw [hh, nat_rec_bif_true]
    simp only [Part.bind_some, Nat.unpair_pair, hStageSearch_eq X _ hconv,
      witEncSearch_eq e n₀ X _ hwp, shift_eq_yc e n₀ X q hconv hge]
  · -- not halted: base value `bitg X m = bitg (yc) m` (since `Y_c = X` there)
    rw [Bool.not_eq_true] at hh
    by_cases hconv : conv X (Nat.unpair q).1
    · have hlt : (Nat.unpair q).2 < hStage X (Nat.unpair q).1 := by
        by_contra hge; push_neg at hge
        rw [(haltedB_iff_ge_hStage X _ hconv _).mpr hge] at hh; exact Bool.noConfusion hh
      rw [hh, nat_rec_bif_false]
      simp only [bitg_eq_bbit, yc_eq_lt e n₀ X _ hconv hlt]
    · rw [hh, nat_rec_bif_false]
      simp only [bitg_eq_bbit, yc_eq_of_not_conv e n₀ X _ hconv]

#print axioms ycBit_recursiveIn

/-- **The forward s-m-n reduction**: a *computable* index map `r` with
`Φ_{r c}^X = Y_c` for every `c` — the `X ⊢ Y_c` half of `Y_c ≡ᵀ X`, uniformly. -/
theorem yc_forward (e n₀ : ℕ) (X : ℕ → Bool)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    ∃ r : ℕ → ℕ, Computable r ∧
      ∀ c, eval (toPFun X) (ofNatCode (r c)) = toPFun (yc e n₀ X c) := by
  obtain ⟨cY, hcY⟩ := exists_code_of_recursiveIn (ycBit_recursiveIn e n₀ X hd)
  refine ⟨fun c => curryEnc (encodeCode cY) c, ?_, fun c => ?_⟩
  · exact Primrec.to_comp (curryEnc_prim.comp (Primrec.const _) Primrec.id)
  · funext m
    show eval (toPFun X) (ofNatCode (curryEnc (encodeCode cY) c)) m = toPFun (yc e n₀ X c) m
    rw [show curryEnc (encodeCode cY) c = encodeCode (curry cY c) from
        (encodeCode_curry cY c).symm, ofNatCode_encodeCode, eval_curry, hcY]
    simp only [Nat.unpair_pair, toPFun_eq_bitg, Part.coe_some]

#print axioms yc_forward

/-! ### Backward reduction: `X ≤ᵀ Y_c` — `Y_c` recovers `X` by un-shifting -/

/-- `Y_c` and `X` have identical graph prefixes up to the halting stage. -/
theorem graphOf_yc_eq_lt (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) {k : ℕ}
    (hk : k ≤ hStage X c) : graphOf (bitg (yc e n₀ X c)) k = graphOf (bitg X) k := by
  rw [graphOf, graphOf]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [bitg_eq_bbit, bitg_eq_bbit, yc_eq_lt e n₀ X c h (lt_of_lt_of_le hj hk)]

/-- The bounded simulation of `Φ_c` gives the same result over `Y_c` as over `X`
(its use lies below the halting stage, where they agree). -/
theorem haltedB_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) (m : ℕ) :
    haltedB (yc e n₀ X c) c m = haltedB X c m := by
  by_cases hm : m ≤ hStage X c
  · rw [haltedB, haltedB, graphOf_yc_eq_lt e n₀ X c h hm]
  · push_neg at hm
    have hyct : haltedB (yc e n₀ X c) c (hStage X c) = true := by
      rw [haltedB, graphOf_yc_eq_lt e n₀ X c h (le_refl _)]; exact haltedB_hStage X c h
    rw [haltedB_mono (yc e n₀ X c) c (le_of_lt hm) hyct,
      haltedB_mono X c (le_of_lt hm) (haltedB_hStage X c h)]

theorem conv_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) : conv (yc e n₀ X c) c := by
  obtain ⟨m, hm⟩ := h; exact ⟨m, by rw [haltedB_yc e n₀ X c ⟨m, hm⟩]; exact hm⟩

/-- `Y_c` and `X` have the same halting stage. -/
theorem hStage_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    hStage (yc e n₀ X c) c = hStage X c := by
  have hc := conv_yc e n₀ X c h
  refine le_antisymm ?_ ?_
  · rw [hStage, dif_pos hc]; exact Nat.find_le (by rw [haltedB_yc e n₀ X c h]; exact haltedB_hStage X c h)
  · rw [hStage, dif_pos h]; exact Nat.find_le (by rw [← haltedB_yc e n₀ X c h]; exact haltedB_hStage _ _ hc)

theorem witPair_yc (e n₀ : ℕ) (X : ℕ → Bool) (c p : ℕ) (h : conv X c) :
    witPair e n₀ (yc e n₀ X c) (hStage X c) p = witPair e n₀ X (hStage X c) p := by
  rw [witPair, witPair, graphOf_yc_eq_lt e n₀ X c h (le_refl _)]

theorem witEnc_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    witEnc e n₀ (yc e n₀ X c) (hStage X c) = witEnc e n₀ X (hStage X c) := by
  have hp : ∀ p, witPair e n₀ (yc e n₀ X c) (hStage X c) p = witPair e n₀ X (hStage X c) p :=
    fun p => witPair_yc e n₀ X c p h
  simp only [witEnc, hp]

theorem wit_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    wit e n₀ (yc e n₀ X c) (hStage (yc e n₀ X c) c) = wit e n₀ X (hStage X c) := by
  rw [hStage_yc e n₀ X c h, wit, wit, witEnc_yc e n₀ X c h]

end Coding
end OracleCode
