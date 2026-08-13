/-
The universal machine, part 2: `evaln` is primitive recursive.

The `n ≤ k` guard makes stage `k` finitely supported, so the whole stage is
a finite table `stageTable L (pair k ec) = (range k).map (evaln k L c)`.
Stage tables satisfy a course-of-values recursion over the index
`N = pair k ec` (`stageStep`, with children looked up in the history —
possible because child indices are smaller: fuel decreases or the code
number decreases).  `Primrec.nat_strong_rec` then yields
`stageTable_prim`, hence **`evaln_prim`**: step-indexed oracle evaluation is
primitive recursive jointly in the fuel, the oracle table, the code, and
the input.
-/
import MartinsConjecture.Evaln

open scoped Computability
open OracleCode

namespace OracleCode

/-- Flattened lookup in a stage table: out-of-range means divergence. -/
def tbl (T : List (Option ℕ)) (x : ℕ) : Option ℕ := (T[x]?).getD none

/-- The true stage table for index `N = pair k ec`. -/
def stageTable (L : List ℕ) (N : ℕ) : List (Option ℕ) :=
  (List.range (Nat.unpair N).1).map
    (evaln (Nat.unpair N).1 L (ofNatCode (Nat.unpair N).2))

theorem evaln_eq_none_of_le {k n : ℕ} {L : List ℕ} {c : OracleCode}
    (h : k ≤ n) : evaln k L c n = none := by
  cases hv : evaln k L c n with
  | none => rfl
  | some v => exact absurd (evaln_bound hv) (by omega)

theorem tbl_stageTable (L : List ℕ) (k ec x : ℕ) :
    tbl (stageTable L (Nat.pair k ec)) x = evaln k L (ofNatCode ec) x := by
  rw [tbl, stageTable]
  simp only [Nat.unpair_pair]
  by_cases hx : x < k
  · rw [List.getElem?_map, List.getElem?_range hx]
    simp
  · rw [List.getElem?_map, List.getElem?_eq_none_iff.mpr (by simp; omega)]
    rw [evaln_eq_none_of_le (by omega)]
    rfl

/-- The per-entry body of the course-of-values step, at fuel `k' + 1`, code
number `ec`, input `n`, with history `H`. -/
def stepEntry (L : List ℕ) (H : List (List (Option ℕ))) (k' ec n : ℕ) : Option ℕ :=
  if ec = 0 then some 0
  else if ec = 1 then some (n + 1)
  else if ec = 2 then some (Nat.unpair n).1
  else if ec = 3 then some (Nat.unpair n).2
  else if ec = 4 then L[n]?
  else
    if (ec - 5) % 2 = 0 then
      if (ec - 5) / 2 % 2 = 0 then
        (tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).1]?).getD []) n).bind
          fun a =>
            (tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).2]?).getD []) n).map
              fun b => Nat.pair a b
      else
        (tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).2]?).getD []) n).bind
          (tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).1]?).getD []))
    else
      if (ec - 5) / 2 % 2 = 0 then
        Nat.casesOn (motive := fun _ => Option ℕ) (Nat.unpair n).2
          (tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).1]?).getD [])
            (Nat.unpair n).1)
          (fun m' =>
            (tbl ((H[Nat.pair k' ec]?).getD [])
                (Nat.pair (Nat.unpair n).1 m')).bind
              fun i =>
                tbl ((H[Nat.pair (k' + 1) (Nat.unpair ((ec - 5) / 4)).2]?).getD [])
                  (Nat.pair (Nat.unpair n).1 (Nat.pair m' i)))
      else
        searchList ((List.range (k' + 1)).map
          fun m' => tbl ((H[Nat.pair (k' + 1) ((ec - 5) / 4)]?).getD [])
            (Nat.pair n m'))

/-- Course-of-values step for stage tables. -/
def stageStep (L : List ℕ) (H : List (List (Option ℕ))) : List (Option ℕ) :=
  Nat.casesOn (motive := fun _ => List (Option ℕ)) (Nat.unpair H.length).1 []
    (fun k' => (List.range (k' + 1)).map fun n =>
      stepEntry L H k' (Nat.unpair H.length).2 n)

/-- Child code numbers are smaller (for the history-lookup bounds). -/
theorem child_lt {ec : ℕ} (h : 5 ≤ ec) :
    (Nat.unpair ((ec - 5) / 4)).1 < ec ∧ (Nat.unpair ((ec - 5) / 4)).2 < ec ∧
      (ec - 5) / 4 < ec := by
  have h1 := Nat.unpair_left_le ((ec - 5) / 4)
  have h2 := Nat.unpair_right_le ((ec - 5) / 4)
  omega

/-- Correctness of the course-of-values step. -/
theorem stageStep_spec (L : List ℕ) (N : ℕ) :
    stageStep L ((List.range N).map (stageTable L)) = stageTable L N := by
  set H := (List.range N).map (stageTable L) with hH
  have hlen : H.length = N := by simp [hH]
  have hget : ∀ M, M < N → (H[M]?).getD [] = stageTable L M := by
    intro M hM
    simp [hH, List.getElem?_map, List.getElem?_range hM]
  rw [stageStep, hlen]
  rcases hk : (Nat.unpair N).1 with _ | k'
  · rw [stageTable, hk]
    rfl
  · rw [stageTable, hk]
    apply List.map_congr_left
    intro n hn
    rw [List.mem_range] at hn
    generalize hec : (Nat.unpair N).2 = ec
    have hN : N = Nat.pair (k' + 1) ec := by
      rw [← hec, ← hk, Nat.pair_unpair]
    by_cases h0 : ec = 0
    · rw [h0, show ofNatCode 0 = .zero from by simp [ofNatCode], evaln, if_pos (by omega)]
      simp [stepEntry]
    · by_cases h1 : ec = 1
      · rw [h1, show ofNatCode 1 = .succ from by simp [ofNatCode], evaln, if_pos (by omega)]
        simp [stepEntry]
      · by_cases h2 : ec = 2
        · rw [h2, show ofNatCode 2 = .left from by simp [ofNatCode], evaln, if_pos (by omega)]
          simp [stepEntry]
        · by_cases h3 : ec = 3
          · rw [h3, show ofNatCode 3 = .right from by simp [ofNatCode], evaln, if_pos (by omega)]
            simp [stepEntry]
          · by_cases h4 : ec = 4
            · rw [h4, show ofNatCode 4 = .oracle from by simp [ofNatCode],
                evaln, if_pos (by omega)]
              simp [stepEntry]
            · have h5 : 5 ≤ ec := by omega
              obtain ⟨d, rfl⟩ : ∃ d, ec = d + 5 := ⟨ec - 5, by omega⟩
              have hdd : d.div2.div2 = d / 4 := by
                simp [Nat.div2_val, Nat.div_div_eq_div_mul]
              have hb1 := Nat.mod_two_of_bodd d
              have hb2 := Nat.mod_two_of_bodd d.div2
              obtain ⟨hc1, hc2, hcm⟩ := child_lt h5
              rw [Nat.add_sub_cancel] at hc1 hc2 hcm
              have hgT1 := hget (Nat.pair (k' + 1) (Nat.unpair (d / 4)).1)
                (by rw [hN]; exact Nat.pair_lt_pair_right _ hc1)
              have hgT2 := hget (Nat.pair (k' + 1) (Nat.unpair (d / 4)).2)
                (by rw [hN]; exact Nat.pair_lt_pair_right _ hc2)
              have hgTm := hget (Nat.pair (k' + 1) (d / 4))
                (by rw [hN]; exact Nat.pair_lt_pair_right _ hcm)
              have hgTp := hget (Nat.pair k' (d + 5))
                (by rw [hN]; exact Nat.pair_lt_pair_left _ (Nat.lt_succ_self k'))
              rw [stepEntry]
              rw [if_neg (show ¬(d + 5 = 0) by omega),
                if_neg (show ¬(d + 5 = 1) by omega),
                if_neg (show ¬(d + 5 = 2) by omega),
                if_neg (show ¬(d + 5 = 3) by omega),
                if_neg (show ¬(d + 5 = 4) by omega)]
              simp only [Nat.add_sub_cancel]
              cases hbb1 : d.bodd <;> cases hbb2 : d.div2.bodd <;>
                rw [hbb1] at hb1 <;> rw [hbb2] at hb2 <;>
                rw [Nat.div2_val] at hb2 <;>
                simp only [Bool.toNat_false, Bool.toNat_true] at hb1 hb2
              · -- pair
                have hofn : ofNatCode (d + 5)
                    = OracleCode.pair (ofNatCode (Nat.unpair (d / 4)).1)
                        (ofNatCode (Nat.unpair (d / 4)).2) := by
                  simp only [ofNatCode.eq_6, hbb1, hbb2, hdd]
                rw [hofn, evaln, if_pos (show n ≤ k' by omega)]
                rw [if_pos hb1, if_pos hb2]
                rw [hgT1, hgT2, tbl_stageTable, tbl_stageTable]
                cases evaln (k' + 1) L (ofNatCode (Nat.unpair (d / 4)).1) n <;>
                  cases evaln (k' + 1) L (ofNatCode (Nat.unpair (d / 4)).2) n <;>
                  rfl
              · -- comp
                have hofn : ofNatCode (d + 5)
                    = OracleCode.comp (ofNatCode (Nat.unpair (d / 4)).1)
                        (ofNatCode (Nat.unpair (d / 4)).2) := by
                  simp only [ofNatCode.eq_6, hbb1, hbb2, hdd]
                rw [hofn, evaln, if_pos (show n ≤ k' by omega)]
                rw [if_pos hb1, if_neg (show ¬(d / 2 % 2 = 0) by omega)]
                simp only [hgT1, hgT2, tbl_stageTable]
                rfl
              · -- prec
                have hofn : ofNatCode (d + 5)
                    = OracleCode.prec (ofNatCode (Nat.unpair (d / 4)).1)
                        (ofNatCode (Nat.unpair (d / 4)).2) := by
                  simp only [ofNatCode.eq_6, hbb1, hbb2, hdd]
                rw [hofn, evaln, if_pos (show n ≤ k' by omega)]
                rw [if_neg (show ¬(d % 2 = 0) by omega), if_pos hb2]
                rcases hm : (Nat.unpair n).2 with _ | m'
                · rw [hgT1, tbl_stageTable]
                  rfl
                · simp only [hgTp, hgT2, tbl_stageTable, hofn]
                  rfl
              · -- rfind
                have hofn : ofNatCode (d + 5)
                    = OracleCode.rfind (ofNatCode (d / 4)) := by
                  simp only [ofNatCode.eq_6, hbb1, hbb2, hdd]
                rw [hofn, evaln, if_pos (show n ≤ k' by omega)]
                rw [if_neg (show ¬(d % 2 = 0) by omega),
                  if_neg (show ¬(d / 2 % 2 = 0) by omega)]
                congr 1
                apply List.map_congr_left
                intro m' _
                rw [hgTm, tbl_stageTable]

/-! ### The primrec stack -/

theorem tbl_prim : Primrec₂ tbl :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const none)).to₂

theorem searchList_prim : Primrec searchList := by
  have hstep : Primrec fun p :
      (List (Option ℕ) × Option ℕ × List (Option ℕ) × Option ℕ) × ℕ =>
      Option.map (· + 1) p.1.2.2.2 :=
    Primrec.option_map
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      ((Primrec.succ.comp Primrec.snd).to₂)
  refine (Primrec.list_rec (Primrec.id (α := List (Option ℕ)))
      (Primrec.const (none : Option ℕ))
      ((Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
        (Primrec.const (none : Option ℕ))
        ((Primrec.nat_casesOn Primrec.snd (Primrec.const (some (0 : ℕ)))
          ((hstep.comp Primrec.fst).to₂)).to₂)).to₂)).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    cases hd with
    | none => rfl
    | some v =>
      cases v with
      | zero => rfl
      | succ w =>
        have hs : searchList (some (w + 1) :: rest) = (searchList rest).map (· + 1) := rfl
        rw [hs]
        exact congrArg (Option.map (· + 1)) ih

section StepEntryPrim

private abbrev Γ : Type := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ

private theorem hL : Primrec fun q : Γ => q.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
private theorem hHH : Primrec fun q : Γ => q.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
private theorem hk' : Primrec fun q : Γ => q.1.2 := Primrec.snd.comp Primrec.fst
private theorem hn : Primrec fun q : Γ => q.2 := Primrec.snd
private theorem hec : Primrec fun q : Γ => (Nat.unpair q.1.1.2.length).2 :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp hHH))
private theorem hm4 : Primrec fun q : Γ =>
    ((Nat.unpair q.1.1.2.length).2 - 5) / 4 :=
  Primrec.nat_div.comp (Primrec.nat_sub.comp hec (Primrec.const 5)) (Primrec.const 4)

private theorem hlook {idx : Γ → ℕ} (hidx : Primrec idx) :
    Primrec fun q : Γ => (q.1.1.2[idx q]?).getD ([] : List (Option ℕ)) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp hHH hidx)
    (Primrec.const ([] : List (Option ℕ)))

private theorem hT1 : Primrec fun q : Γ =>
    (q.1.1.2[Nat.pair (q.1.2 + 1)
      (Nat.unpair (((Nat.unpair q.1.1.2.length).2 - 5) / 4)).1]?).getD
      ([] : List (Option ℕ)) :=
  hlook (Primrec₂.natPair.comp (Primrec.succ.comp hk')
    (Primrec.fst.comp (Primrec.unpair.comp hm4)))

private theorem hT2 : Primrec fun q : Γ =>
    (q.1.1.2[Nat.pair (q.1.2 + 1)
      (Nat.unpair (((Nat.unpair q.1.1.2.length).2 - 5) / 4)).2]?).getD
      ([] : List (Option ℕ)) :=
  hlook (Primrec₂.natPair.comp (Primrec.succ.comp hk')
    (Primrec.snd.comp (Primrec.unpair.comp hm4)))

private theorem hTm : Primrec fun q : Γ =>
    (q.1.1.2[Nat.pair (q.1.2 + 1)
      (((Nat.unpair q.1.1.2.length).2 - 5) / 4)]?).getD
      ([] : List (Option ℕ)) :=
  hlook (Primrec₂.natPair.comp (Primrec.succ.comp hk') hm4)

private theorem hTp : Primrec fun q : Γ =>
    (q.1.1.2[Nat.pair q.1.2 (Nat.unpair q.1.1.2.length).2]?).getD
      ([] : List (Option ℕ)) :=
  hlook (Primrec₂.natPair.comp hk' hec)

/-- The per-entry body is primitive recursive. -/
theorem stepEntry_prim : Primrec fun q : Γ =>
    stepEntry q.1.1.1 q.1.1.2 q.1.2 (Nat.unpair q.1.1.2.length).2 q.2 := by
  have haT : Primrec fun s : Γ × ℕ => (Nat.unpair s.1.2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (hn.comp Primrec.fst))
  refine Primrec.ite (Primrec.eq.comp hec (Primrec.const 0))
    (Primrec.const (some 0)) ?_
  refine Primrec.ite (Primrec.eq.comp hec (Primrec.const 1))
    (Primrec.option_some.comp (Primrec.succ.comp hn)) ?_
  refine Primrec.ite (Primrec.eq.comp hec (Primrec.const 2))
    (Primrec.option_some.comp (Primrec.fst.comp (Primrec.unpair.comp hn))) ?_
  refine Primrec.ite (Primrec.eq.comp hec (Primrec.const 3))
    (Primrec.option_some.comp (Primrec.snd.comp (Primrec.unpair.comp hn))) ?_
  refine Primrec.ite (Primrec.eq.comp hec (Primrec.const 4))
    (Primrec.list_getElem?.comp hL hn) ?_
  refine Primrec.ite
    (Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.nat_sub.comp hec (Primrec.const 5))
        (Primrec.const 2))
      (Primrec.const 0)) ?_ ?_
  · refine Primrec.ite
      (Primrec.eq.comp
        (Primrec.nat_mod.comp
          (Primrec.nat_div.comp (Primrec.nat_sub.comp hec (Primrec.const 5))
            (Primrec.const 2))
          (Primrec.const 2))
        (Primrec.const 0)) ?_ ?_
    · -- pair
      exact Primrec.option_bind (tbl_prim.comp hT1 hn)
        ((Primrec.option_map ((tbl_prim.comp hT2 hn).comp Primrec.fst)
          ((Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)).to₂)
    · -- comp
      exact Primrec.option_bind (tbl_prim.comp hT2 hn)
        ((tbl_prim.comp (hT1.comp Primrec.fst) Primrec.snd).to₂)
  · refine Primrec.ite
      (Primrec.eq.comp
        (Primrec.nat_mod.comp
          (Primrec.nat_div.comp (Primrec.nat_sub.comp hec (Primrec.const 5))
            (Primrec.const 2))
          (Primrec.const 2))
        (Primrec.const 0)) ?_ ?_
    · -- prec
      refine Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp hn))
        (tbl_prim.comp hT1 (Primrec.fst.comp (Primrec.unpair.comp hn))) ?_
      exact (Primrec.option_bind
        (tbl_prim.comp (hTp.comp Primrec.fst)
          (Primrec₂.natPair.comp haT Primrec.snd))
        ((tbl_prim.comp (hT2.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.natPair.comp (haT.comp Primrec.fst)
            (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂)).to₂
    · -- rfind
      exact searchList_prim.comp
        (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hk'))
          ((tbl_prim.comp (hTm.comp Primrec.fst)
            (Primrec₂.natPair.comp (hn.comp Primrec.fst) Primrec.snd)).to₂))

end StepEntryPrim

/-- The course-of-values step is primitive recursive. -/
theorem stageStep_prim : Primrec₂ stageStep := by
  have houter : Primrec fun a : List ℕ × List (List (Option ℕ)) =>
      Nat.casesOn (motive := fun _ => List (Option ℕ)) (Nat.unpair a.2.length).1 []
        (fun k' => (List.range (k' + 1)).map fun n =>
          stepEntry a.1 a.2 k' (Nat.unpair a.2.length).2 n) := by
    refine Primrec.nat_casesOn
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd)))
      (Primrec.const ([] : List (Option ℕ))) ?_
    have hg : Primrec₂ fun (p : (List ℕ × List (List (Option ℕ))) × ℕ) (n : ℕ) =>
        stepEntry p.1.1 p.1.2 p.2 (Nat.unpair p.1.2.length).2 n := stepEntry_prim
    exact (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      hg).to₂
  exact (houter.of_eq fun a => rfl).to₂

/-- **Stage tables are primitive recursive.** -/
theorem stageTable_prim : Primrec₂ stageTable :=
  Primrec.nat_strong_rec _
    ((Primrec.option_some.comp stageStep_prim).to₂ :
      Primrec₂ fun (L : List ℕ) (H : List (List (Option ℕ))) => some (stageStep L H))
    fun L N => congrArg some (stageStep_spec L N)

theorem evaln_eq_tbl (k : ℕ) (L : List ℕ) (c : OracleCode) (n : ℕ) :
    evaln k L c n = tbl (stageTable L (Nat.pair k (encodeCode c))) n := by
  rw [tbl_stageTable, ofNatCode_encodeCode]

theorem encode_eq_encodeCode : (Encodable.encode : OracleCode → ℕ) = encodeCode := rfl

/-- **The universal machine is primitive recursive**: `evaln` is primitive
recursive jointly in fuel, oracle table, code, and input. -/
theorem evaln_prim :
    Primrec fun p : ((ℕ × List ℕ) × OracleCode) × ℕ =>
      evaln p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have henc : Primrec fun p : ((ℕ × List ℕ) × OracleCode) × ℕ => encodeCode p.1.2 := by
    rw [← encode_eq_encodeCode]
    exact Primrec.encode.comp (Primrec.snd.comp Primrec.fst)
  have h := tbl_prim.comp
    (stageTable_prim.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) henc))
    Primrec.snd
  exact h.of_eq fun p => (evaln_eq_tbl _ _ _ _).symm

end OracleCode
