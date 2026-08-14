/-
Toward the continuous case of Lachlan's local dichotomy (Lutz Cor. 3.11).

The **extension-halting predicate** `extHaltsFrom σ e n` — "does machine `e` halt
on `n` under some finite extension of the prefix `σ`?" — is `0′`-decidable
(`OracleCode.extHaltsFrom_recursiveIn_jump`), by bridging to the `ExtHalting`
search functional.  Its negation is the `Π₁` "no extension halts" test that
Lachlan's continuous case consults to decide `n ∈ Wˣ` from `X ⊕ 0′`.
-/
import MartinsConjecture.OperatorLocal
import MartinsConjecture.ExtHalting

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- `n ∈ W^{σ⌢τ}` for some finite extension `τ` of `σ`: the extension-halting
predicate for the operator with index `e`. -/
def extHaltsFrom (σ : List ℕ) (e n : ℕ) : Prop :=
  ∃ τ : List ℕ, haltsOn (σ ++ τ) e n

/-- `∃ w, ehTest p w = 0` is exactly extension-halting for the prefix decoded
from `p`. -/
theorem exists_ehTest_iff (p : ℕ) :
    (∃ w, ehTest p w = 0) ↔
      extHaltsFrom ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(Encodable.decode (α := List ℕ) (Nat.unpair w).1).getD [], (Nat.unpair w).2, ?_⟩
    by_contra hns
    rw [ehTest, if_neg hns] at hw
    exact one_ne_zero hw
  · rintro ⟨τ, s, hs⟩
    refine ⟨Nat.pair (Encodable.encode τ) s, ?_⟩
    rw [ehTest]
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    rw [if_pos hs]

/-- **The extension-halting problem is `0′`-decidable** (operator form): as a
function of `p = ⟪encode σ, ⟪e, n⟫⟫`, whether `n ∈ W^{σ⌢τ}` for some `τ` is
recursive in the jump of the empty oracle. -/
theorem extHaltsFrom_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((if extHaltsFrom
        ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2
        then 1 else 0 : ℕ) : Part ℕ)) := by
  refine extHalting_recursiveIn_jump.of_eq fun p => ?_
  rw [exists_ehTest_iff p]

/-! ### The prefix-halting test is also `0′`-decidable

For the final search we also need the *positive* test — "does the finite prefix
`σ` already halt on `n`?" — decidable in `0′`.  We build it fresh (simpler than
`ehTest`: the oracle table is `σ` itself, with no extension). -/

/-- `p = ⟪encode σ, ⟪e, n⟫⟫`; `hTest p s = 0` iff `evaln s σ (ofNatCode e) n`
halts. -/
def hTest (p s : ℕ) : ℕ :=
  if (evaln s ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
      (ofNatCode (Nat.unpair (Nat.unpair p).2).1)
      (Nat.unpair (Nat.unpair p).2).2).isSome then 0 else 1

theorem hTest_prim : Nat.Primrec (fun v => hTest (Nat.unpair v).1 (Nat.unpair v).2) := by
  refine Primrec.nat_iff.mp ?_
  have hfuel : Primrec fun v : ℕ => (Nat.unpair v).2 := Primrec.snd.comp Primrec.unpair
  have hσ : Primrec fun v : ℕ =>
      (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const ([] : List ℕ))
  have hcode : Primrec fun v : ℕ =>
      ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 :=
    (Primrec.ofNat OracleCode).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
  have hk : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  have hev : Primrec fun v : ℕ =>
      evaln (Nat.unpair v).2
        ((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [])
        (ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 :=
    evaln_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hfuel hσ) hcode) hk)
  have hci : ∀ b : Bool, (cond b (0 : ℕ) 1) = if b then (0 : ℕ) else 1 :=
    fun b => by cases b <;> rfl
  exact (Primrec.cond (Primrec.option_isSome.comp hev)
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => by
    simp only [hTest, Nat.unpair_pair]
    exact hci _

/-- `rfind` predicate for `hTest`. -/
noncomputable def hPred (p : ℕ) : ℕ →. Bool :=
  fun s => (fun m => decide (m = 0)) <$> (Part.some (hTest p s) : Part ℕ)

/-- Search functional: halts on `p` iff the prefix already halts. -/
noncomputable def hFun (p : ℕ) : Part ℕ := Nat.rfind (hPred p)

theorem hFun_partrec : Nat.Partrec hFun := by
  have h1 : Nat.Partrec
      (fun v : ℕ => (Part.some (hTest (Nat.unpair v).1 (Nat.unpair v).2) : Part ℕ)) :=
    Nat.Partrec.of_primrec hTest_prim
  refine (Nat.Partrec.rfind h1).of_eq fun p => ?_
  simp only [Nat.unpair_pair]
  rfl

theorem hPred_dom (p s : ℕ) : (hPred p s).Dom := by
  rw [hPred, Part.map_eq_map, Part.map_some]; trivial

theorem true_mem_hPred (p s : ℕ) : true ∈ hPred p s ↔ hTest p s = 0 := by
  rw [hPred, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    rw [Part.mem_some_iff.mp hx] at hx0
    exact of_decide_eq_true hx0
  · intro h
    exact ⟨hTest p s, Part.mem_some _, by simp [h]⟩

theorem hFun_dom (p : ℕ) : (hFun p).Dom ↔ ∃ s, hTest p s = 0 := by
  rw [hFun, Nat.rfind_dom]
  constructor
  · rintro ⟨s, hs, -⟩
    exact ⟨s, (true_mem_hPred p s).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (true_mem_hPred p s).mpr hs, fun {m} _ => hPred_dom p m⟩

/-- `∃ s, hTest p s = 0` is exactly `haltsOn` for the prefix decoded from `p`. -/
theorem exists_hTest_iff (p : ℕ) :
    (∃ s, hTest p s = 0) ↔
      haltsOn ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2 := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    by_contra hns
    rw [hTest, if_neg hns] at hs
    exact one_ne_zero hs
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [hTest, if_pos hs]

/-- **The prefix-halting test is `0′`-decidable**: whether machine `e` already
halts on `n` using the prefix decoded from `p` is recursive in `jump ∅`. -/
theorem haltsOn_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((if haltsOn
        ((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        (Nat.unpair (Nat.unpair p).2).1 (Nat.unpair (Nat.unpair p).2).2
        then 1 else 0 : ℕ) : Part ℕ)) := by
  have hrec : Nat.RecursiveIn {emptyO} hFun := hFun_partrec.recursiveIn
  refine (domain_recursiveIn_jump hrec).of_eq fun p => ?_
  rw [hFun_dom p, exists_hTest_iff p]

/-! ### The continuous-case reduction

We now show: if the operator `W` (index `e`) is **continuous at `X`** — for every
`n`, some finite prefix decides `n ∈ Wˣ`, i.e.
`haltsOn (X↾ℓ) ∨ ¬ extHaltsFrom (X↾ℓ)` — then `Wˣ ≤ᵀ X ⊕ 0′`.

The reduction, on input `n`: search for the least prefix length `ℓ` that is
*decisive*, then read off the answer.  Both tests are decidable in `0′`
(`haltsOn_recursiveIn_jump`, `extHaltsFrom_recursiveIn_jump`); the prefix itself
is `X`-computable (`graphEnc`).  We work over the two-oracle set
`{toPFun X, jumpFn ∅}` and cut to `join X 0′` at the end via
`Nat.RecursiveIn.subst`. -/

/-- Stage-`ℓ` query at input `n`, packed as `m = ⟪n, ℓ⟫`:
`⟪encode (X↾ℓ), ⟪e, n⟫⟫`. -/
def qEnc (X : ℕ → Bool) (e : ℕ) (m : ℕ) : ℕ :=
  Nat.pair (Encodable.encode (graphOf (bitg X) (Nat.unpair m).2))
    (Nat.pair e (Nat.unpair m).1)

/-- The positive test as a `0/1` value: `1` iff the prefix `X↾ℓ` already halts. -/
noncomputable def hVal (X : ℕ → Bool) (e : ℕ) (m : ℕ) : ℕ :=
  if haltsOn (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1 then 1 else 0

/-- The extension test as a `0/1` value: `1` iff some extension of `X↾ℓ` halts. -/
noncomputable def eVal (X : ℕ → Bool) (e : ℕ) (m : ℕ) : ℕ :=
  if extHaltsFrom (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1 then 1 else 0

/-- Decision value: `0` exactly when stage `ℓ` is decisive. -/
noncomputable def decVal (X : ℕ → Bool) (e : ℕ) (m : ℕ) : ℕ :=
  (1 - hVal X e m) * eVal X e m

theorem decVal_eq_zero_iff (X : ℕ → Bool) (e m : ℕ) :
    decVal X e m = 0 ↔
      haltsOn (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1
      ∨ ¬ extHaltsFrom (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1 := by
  rw [decVal, hVal, eVal]
  by_cases hh : haltsOn (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1 <;>
    by_cases he : extHaltsFrom (graphOf (bitg X) (Nat.unpair m).2) e (Nat.unpair m).1 <;>
    simp [hh, he]

/-- **Correctness kernel.**  At any *decisive* stage `ℓ`, the positive test reads
off the true bit of `Wˣ` at `n`: `[haltsOn (X↾ℓ)] = bitg Wˣ n`.  (If the prefix
halts, `n ∈ Wˣ`; if no extension halts, no prefix of `X` halts either — by
monotonicity and `graphOf` prefixing — so `n ∉ Wˣ`.) -/
theorem decisive_answer (X : ℕ → Bool) (e n ℓ : ℕ)
    (hdec : haltsOn (graphOf (bitg X) ℓ) e n ∨ ¬ extHaltsFrom (graphOf (bitg X) ℓ) e n) :
    (if haltsOn (graphOf (bitg X) ℓ) e n then (1 : ℕ) else 0) = bitg (reReal e X) n := by
  have hiff : haltsOn (graphOf (bitg X) ℓ) e n ↔ reReal e X n = true := by
    rw [reReal_eq_true_iff]
    constructor
    · intro h; exact ⟨ℓ, h⟩
    · rintro ⟨ℓ', hℓ'⟩
      rcases hdec with hh | hne
      · exact hh
      · exfalso
        apply hne
        rcases le_total ℓ' ℓ with hle | hle
        · exact ⟨[], by rw [List.append_nil]; exact haltsOn_mono (graphOf_prefix hle) hℓ'⟩
        · obtain ⟨τ, hτ⟩ := graphOf_prefix hle
          exact ⟨τ, hτ ▸ hℓ'⟩
  by_cases hh : haltsOn (graphOf (bitg X) ℓ) e n
  · rw [if_pos hh, bitg, hiff.mp hh]; rfl
  · rw [if_neg hh, bitg]
    have hf : reReal e X n = false := by
      cases hb : reReal e X n
      · rfl
      · exact absurd (hiff.mpr hb) hh
    rw [hf]; rfl

/-- `true ∈ pf n ℓ` iff the stage is decisive (`decVal = 0`). -/
theorem true_mem_decPred (X : ℕ → Bool) (e n ℓ : ℕ) :
    true ∈ (((fun m => m = 0) <$> ((decVal X e (Nat.pair n ℓ) : ℕ) : Part ℕ)) : Part Bool) ↔
      decVal X e (Nat.pair n ℓ) = 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    rw [Part.mem_some_iff.mp hx] at hx0
    exact of_decide_eq_true hx0
  · intro h
    exact ⟨_, Part.mem_some _, by simp [h]⟩

/-- **The continuous case of Lachlan's local dichotomy** (Lutz Cor. 3.11, the
determinacy-free half).  If the r.e. operator `W` (index `e`) is *continuous at
`X`* — every `n`'s membership `n ∈ Wˣ` is settled by a finite prefix of `X`
(`haltsOn (X↾ℓ) ∨ ¬ extHaltsFrom (X↾ℓ)`) — then `Wˣ ≤ᵀ X ⊕ 0′`. -/
theorem continuous_case (X : ℕ → Bool) (e : ℕ)
    (Hcont : ∀ n, ∃ ℓ, haltsOn (graphOf (bitg X) ℓ) e n
        ∨ ¬ extHaltsFrom (graphOf (bitg X) ℓ) e n) :
    reReal e X ≤ₜ Cantor.join X (Cantor.jump (fun _ : ℕ => false)) := by
  classical
  set C : ℕ → Bool := Cantor.join X (Cantor.jump (fun _ : ℕ => false)) with hCdef
  set O : Set (ℕ →. ℕ) := {Cantor.toPFun X, jumpFn emptyO} with hOdef
  have hsubX : ({Cantor.toPFun X} : Set (ℕ →. ℕ)) ⊆ O := by
    rw [hOdef]; exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  have hsubJ : ({jumpFn emptyO} : Set (ℕ →. ℕ)) ⊆ O := by
    rw [hOdef]; exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- graphEnc, lifted to O, then queried at the stage
  have hgm : Nat.RecursiveIn O (fun m => graphEnc X (Nat.unpair m).2) :=
    (Nat.RecursiveIn.comp
      ((graphEnc_recursiveIn X).subst (fun g hg => Nat.RecursiveIn.oracle g (hsubX hg)))
      ((Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)).recursiveIn)).of_eq fun m => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  -- the query value
  have hqf : Nat.RecursiveIn O (fun m => ((qEnc X e m : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.pair hgm
      ((Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.const e)
        (Primrec.fst.comp Primrec.unpair))).recursiveIn)).of_eq fun m => by
      rw [qEnc, graphEnc]
      simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
        Part.coe_some]
  -- the two 0'-tests, composed with the query
  have hHval : Nat.RecursiveIn O (fun m => ((hVal X e m : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp
      (haltsOn_recursiveIn_jump.subst (fun g hg => Nat.RecursiveIn.oracle g (hsubJ hg)))
      hqf).of_eq fun m => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, qEnc, hVal, Nat.unpair_pair,
        Encodable.encodek, Option.getD_some]
  have hEval : Nat.RecursiveIn O (fun m => ((eVal X e m : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp
      (extHaltsFrom_recursiveIn_jump.subst (fun g hg => Nat.RecursiveIn.oracle g (hsubJ hg)))
      hqf).of_eq fun m => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, qEnc, eVal, Nat.unpair_pair,
        Encodable.encodek, Option.getD_some]
  -- the decision value
  have hcomb : Nat.RecursiveIn O
      (fun p => (((1 - (Nat.unpair p).1) * (Nat.unpair p).2 : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp (Primrec.nat_mul.comp
      (Primrec.nat_sub.comp (Primrec.const 1) (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair))).recursiveIn
  have hDecv : Nat.RecursiveIn O (fun m => ((decVal X e m : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp hcomb (Nat.RecursiveIn.pair hHval hEval)).of_eq fun m => by
      simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
        Nat.unpair_pair, decVal, Part.coe_some]
  -- the search and the answer
  have hSearch := Nat.RecursiveIn.rfind hDecv
  have hAns : Nat.RecursiveIn O
      (fun n => (Nat.pair <$> ((n : ℕ) : Part ℕ) <*>
          Nat.rfind (fun ℓ => (fun m => m = 0) <$> ((decVal X e (Nat.pair n ℓ) : ℕ) : Part ℕ)))
        >>= fun m => ((hVal X e m : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hHval
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hSearch)
  -- cut both oracles down to `join X 0′`
  have hjump_eq : jumpFn emptyO = Cantor.toPFun (Cantor.jump (fun _ : ℕ => false)) := by
    rw [Cantor.toPFun_jump, Cantor.toPFun_const_false]; rfl
  have hAnsC : Nat.RecursiveIn {Cantor.toPFun C} _ := hAns.subst (by
    intro g hg
    rw [hOdef] at hg
    rcases hg with h | h
    · subst h; exact RecursiveIn.iff_nat.mp (left_le_join X (Cantor.jump (fun _ : ℕ => false)))
    · rw [Set.mem_singleton_iff.mp h, hjump_eq]
      exact RecursiveIn.iff_nat.mp (right_le_join X (Cantor.jump (fun _ : ℕ => false))))
  rw [Cantor.le_iff_bitg]
  refine hAnsC.of_eq fun n => ?_
  -- correctness: the search finds a decisive stage, and reads off the right bit
  obtain ⟨ℓ0, hℓ0⟩ := Hcont n
  set S : Part ℕ := Nat.rfind (fun ℓ => (fun m => m = 0) <$>
      ((decVal X e (Nat.pair n ℓ) : ℕ) : Part ℕ)) with hSdef
  have hwit : true ∈ (((fun m => m = 0) <$>
      ((decVal X e (Nat.pair n ℓ0) : ℕ) : Part ℕ)) : Part Bool) :=
    (true_mem_decPred X e n ℓ0).mpr ((decVal_eq_zero_iff X e (Nat.pair n ℓ0)).mpr
      (by simpa using hℓ0))
  have hSdom : S.Dom :=
    Nat.rfind_dom.mpr ⟨ℓ0, hwit, fun {m} _ => by simp⟩
  set ℓ := S.get hSdom with hℓdef
  have hℓmem : ℓ ∈ S := Part.get_mem hSdom
  have hdecisive : decVal X e (Nat.pair n ℓ) = 0 :=
    (true_mem_decPred X e n ℓ).mp (Nat.rfind_spec hℓmem)
  have hdec : haltsOn (graphOf (bitg X) ℓ) e n ∨ ¬ extHaltsFrom (graphOf (bitg X) ℓ) e n := by
    have h := (decVal_eq_zero_iff X e (Nat.pair n ℓ)).mp hdecisive
    simpa using h
  -- substitute the search value and read off
  rw [Part.eq_some_iff.mpr hℓmem]
  simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, hVal, Nat.unpair_pair]
  exact congrArg _ (decisive_answer X e n ℓ hdec)

end OracleCode

#print axioms OracleCode.extHaltsFrom_recursiveIn_jump
#print axioms OracleCode.haltsOn_recursiveIn_jump
#print axioms OracleCode.decisive_answer
#print axioms OracleCode.continuous_case
