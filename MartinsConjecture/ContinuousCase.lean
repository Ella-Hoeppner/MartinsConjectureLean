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

end OracleCode

#print axioms OracleCode.extHaltsFrom_recursiveIn_jump
#print axioms OracleCode.haltsOn_recursiveIn_jump
