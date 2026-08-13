/-
The jump is order preserving and degree invariant.

This file discharges "gap 1" of the ledger: the `trOracle` code translation of
`Jump.lean` is primitive recursive on encodings (`trE_primrec`, by
course-of-values recursion via `Primrec.nat_strong_rec`), which yields

* `jumpFn_mono : A ≤ᵀ B → jumpFn A ≤ᵀ jumpFn B` (order preservation),
* `jumpFn_congr : A ≡ᵀ B → jumpFn A ≡ᵀ jumpFn B` (degree invariance),

and, on Cantor space, that `Cantor.jump` is an order-preserving — hence
Turing-invariant — function in the sense of the Martin's-conjecture framework
(`Martin.orderPreserving_jump`, `Martin.turingInvariant_jump`).
-/
import MartinsConjecture.CantorPoints
import MartinsConjecture.Martin

open scoped Computability
open OracleCode

/-- Encoding-level version of the `trOracle` translation. -/
def trE (cI : OracleCode) : ℕ → ℕ := fun e => encodeCode (trOracle cI (ofNatCode e))

/-- Course-of-values step function for `trE`: reconstruct the translation of
code number `L.length` from the list `L` of translations of all smaller code
numbers. -/
def trStep (cI : OracleCode) (L : List ℕ) : ℕ :=
  if L.length < 4 then L.length
  else if L.length = 4 then encodeCode cI
  else
    4 * (if (L.length - 5) % 2 = 1 ∧ (L.length - 5) / 2 % 2 = 1 then
          L.getD ((L.length - 5) / 4) 0
        else
          Nat.pair (L.getD (Nat.unpair ((L.length - 5) / 4)).1 0)
            (L.getD (Nat.unpair ((L.length - 5) / 4)).2 0))
      + (L.length - 5) % 2 + 2 * ((L.length - 5) / 2 % 2) + 5

theorem trStep_primrec (cI : OracleCode) : Primrec (trStep cI) := by
  have hlen : Primrec fun L : List ℕ => L.length := Primrec.list_length
  have hk : Primrec fun L : List ℕ => L.length - 5 :=
    Primrec.nat_sub.comp hlen (Primrec.const 5)
  have hm : Primrec fun L : List ℕ => (L.length - 5) / 4 :=
    Primrec.nat_div.comp hk (Primrec.const 4)
  have hgm : Primrec fun L : List ℕ => L.getD ((L.length - 5) / 4) 0 :=
    (Primrec.list_getD 0).comp Primrec.id hm
  have hg1 : Primrec fun L : List ℕ => L.getD (Nat.unpair ((L.length - 5) / 4)).1 0 :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.fst.comp (Primrec.unpair.comp hm))
  have hg2 : Primrec fun L : List ℕ => L.getD (Nat.unpair ((L.length - 5) / 4)).2 0 :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp hm))
  have hb1 : Primrec fun L : List ℕ => (L.length - 5) % 2 :=
    Primrec.nat_mod.comp hk (Primrec.const 2)
  have hb2 : Primrec fun L : List ℕ => (L.length - 5) / 2 % 2 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hk (Primrec.const 2)) (Primrec.const 2)
  have hcond : PrimrecPred fun L : List ℕ =>
      (L.length - 5) % 2 = 1 ∧ (L.length - 5) / 2 % 2 = 1 :=
    PrimrecPred.and (Primrec.eq.comp hb1 (Primrec.const 1))
      (Primrec.eq.comp hb2 (Primrec.const 1))
  have hchild : Primrec fun L : List ℕ =>
      (if (L.length - 5) % 2 = 1 ∧ (L.length - 5) / 2 % 2 = 1 then
        L.getD ((L.length - 5) / 4) 0
      else
        Nat.pair (L.getD (Nat.unpair ((L.length - 5) / 4)).1 0)
          (L.getD (Nat.unpair ((L.length - 5) / 4)).2 0)) :=
    Primrec.ite hcond hgm (Primrec₂.natPair.comp hg1 hg2)
  refine Primrec.ite (Primrec.nat_lt.comp hlen (Primrec.const 4)) hlen
    (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 4))
      (Primrec.const (encodeCode cI)) ?_)
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hchild) hb1)
      (Primrec.nat_mul.comp (Primrec.const 2) hb2))
    (Primrec.const 5)

theorem trStep_spec (cI : OracleCode) (n : ℕ) :
    trStep cI ((List.range n).map (trE cI)) = trE cI n := by
  set L : List ℕ := (List.range n).map (trE cI) with hL
  have hlen : L.length = n := by simp [hL]
  have hget : ∀ j, j < n → L[j]?.getD 0 = trE cI j := by
    intro j hj
    simp [hL, List.getElem?_map, List.getElem?_range, hj]
  rw [trStep, hlen]
  by_cases h4 : n < 4
  · rw [if_pos h4]
    rcases n with _ | _ | _ | _ | n
    · simp [trE, ofNatCode, trOracle, encodeCode]
    · simp [trE, ofNatCode, trOracle, encodeCode]
    · simp [trE, ofNatCode, trOracle, encodeCode]
    · simp [trE, ofNatCode, trOracle, encodeCode]
    · omega
  · rw [if_neg h4]
    by_cases h5 : n = 4
    · subst h5
      rw [if_pos rfl]
      simp [trE, ofNatCode, trOracle]
    · rw [if_neg h5]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hdiv : k.div2.div2 = k / 4 := by
        simp [Nat.div2_val, Nat.div_div_eq_div_mul]
      have hdv : k.div2 = k / 2 := Nat.div2_val k
      have hb1 := Nat.mod_two_of_bodd k
      have hb2 := Nat.mod_two_of_bodd k.div2
      have hmlt : k / 4 < k + 5 := by omega
      have hu1 : (Nat.unpair (k / 4)).1 < k + 5 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
      have hu2 : (Nat.unpair (k / 4)).2 < k + 5 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
      rw [show trE cI (k + 5) = encodeCode (trOracle cI (ofNatCode (k + 5))) from rfl]
      rw [ofNatCode.eq_6]
      cases hbb1 : k.bodd <;> cases hbb2 : k.div2.bodd
      · rw [hbb1] at hb1; rw [hbb2] at hb2
        simp only [Bool.toNat_false] at hb1 hb2
        rw [hdv] at hb2
        simp only [trOracle, encodeCode, hdiv]
        simp [hb1, hb2, hget _ hu1, hget _ hu2, trE]
        try omega
      · rw [hbb1] at hb1; rw [hbb2] at hb2
        simp only [Bool.toNat_false, Bool.toNat_true] at hb1 hb2
        rw [hdv] at hb2
        simp only [trOracle, encodeCode, hdiv]
        simp [hb1, hb2, hget _ hu1, hget _ hu2, trE]
        try omega
      · rw [hbb1] at hb1; rw [hbb2] at hb2
        simp only [Bool.toNat_false, Bool.toNat_true] at hb1 hb2
        rw [hdv] at hb2
        simp only [trOracle, encodeCode, hdiv]
        simp [hb1, hb2, hget _ hu1, hget _ hu2, trE]
        try omega
      · rw [hbb1] at hb1; rw [hbb2] at hb2
        simp only [Bool.toNat_true] at hb1 hb2
        rw [hdv] at hb2
        simp only [trOracle, encodeCode, hdiv]
        simp [hb1, hb2, hget _ hmlt, trE]
        try omega

theorem trE_primrec (cI : OracleCode) : Primrec (trE cI) := by
  have h2 : Primrec₂ fun (_ : Unit) (e : ℕ) => trE cI e :=
    Primrec.nat_strong_rec _
      (((Primrec.option_some.comp ((trStep_primrec cI).comp Primrec.snd)).to₂ :
        Primrec₂ fun (_ : Unit) (L : List ℕ) => some (trStep cI L)))
      fun _ n => congrArg some (trStep_spec cI n)
  exact h2.comp (Primrec.const ()) Primrec.id

/-! ### The jump is order preserving and degree invariant -/

theorem jumpFn_mono {A B : ℕ →. ℕ} (h : A ≤ᵀ B) : jumpFn A ≤ᵀ jumpFn B := by
  obtain ⟨cI, hcI⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  refine RecursiveIn.iff_nat.mpr ?_
  set q : ℕ → ℕ := fun e => compEnc (trE cI e) (constEnc e) with hq
  have hqP : Nat.Primrec q := Primrec.nat_iff.mp
    (compEnc_prim.comp (trE_primrec cI) constEnc_prim)
  have hkey : ∀ e, jumpP A e ↔ jumpP B (q e) := by
    intro e
    have : q e = encodeCode (.comp (trOracle cI (ofNatCode e)) (const e)) := by
      simp [hq, trE, constEnc, encodeCode_comp]
    rw [this]
    exact jumpP_trOracle hcI e
  have h1 : Nat.RecursiveIn {jumpFn B}
      (fun e : ℕ => ((q e : ℕ) : Part ℕ) >>= jumpFn B) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) hqP.recursiveIn
  refine h1.of_eq fun e => ?_
  rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [jumpFn, jumpFn]
  by_cases hj : jumpP A e
  · rw [if_pos ((hkey e).mp hj), if_pos hj]
  · rw [if_neg (fun hc => hj ((hkey e).mpr hc)), if_neg hj]

/-- **The jump is degree invariant.** -/
theorem jumpFn_congr {A B : ℕ →. ℕ} (h : A ≡ᵀ B) : jumpFn A ≡ᵀ jumpFn B :=
  ⟨jumpFn_mono h.1, jumpFn_mono h.2⟩

namespace Cantor

theorem jump_mono {X Y : ℕ → Bool} (h : X ≤ₜ Y) : jump X ≤ₜ jump Y := by
  unfold le
  rw [toPFun_jump, toPFun_jump]
  exact jumpFn_mono h

theorem jump_congr {X Y : ℕ → Bool} (h : X ≡ₜ Y) : jump X ≡ₜ jump Y :=
  ⟨jump_mono h.1, jump_mono h.2⟩

end Cantor

namespace Martin

/-- **The jump is an order-preserving function on Cantor space** — so the
function `X ↦ X′` genuinely belongs to the class of functions Martin's
conjecture speaks about. -/
theorem orderPreserving_jump : OrderPreserving Cantor.jump :=
  fun _ _ h => Cantor.jump_mono h

/-- The jump is Turing invariant. -/
theorem turingInvariant_jump : TuringInvariant Cantor.jump :=
  orderPreserving_jump.turingInvariant

end Martin

/-! ### The jump descends to Turing degrees -/

/-- The Turing jump as an operation on Turing degrees (well-defined by
`jumpFn_congr`). -/
noncomputable def TuringDegree.jump : TuringDegree → TuringDegree :=
  Quot.map jumpFn fun _ _ h => jumpFn_congr h

/-- **Jump strictness at the degree level**: every Turing degree is strictly
below its jump. -/
theorem TuringDegree.lt_jump (d : TuringDegree) : d < TuringDegree.jump d := by
  induction d using Quot.ind with
  | _ A =>
    exact lt_iff_le_not_ge.mpr
      ⟨turingReducible_jumpFn A, fun h => jumpFn_not_turingReducible A h⟩

#print axioms jumpFn_congr
#print axioms Martin.turingInvariant_jump
#print axioms TuringDegree.lt_jump
