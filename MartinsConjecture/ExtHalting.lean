/-
The extension-halting problem is decidable in `0′`.

The recursion-theoretic crux of the finite-extension (Kleene–Post) method:
given a finite oracle prefix `base : List ℕ` and a machine index `e`, the
question

  "does machine `e` halt on input `k` under **some** finite extension of
   `base` (within some number of steps)?"

is Σ₁, hence decidable in `0′` (`extHalting_recursiveIn_jump`).  This is
exactly the oracle a `0′`-computable finite-extension construction consults
at each stage; it is `domain_recursiveIn_jump` (Post's theorem) applied to
the explicit search functional `ehFun`.
-/
import MartinsConjecture.PostDomain

open scoped Computability
open OracleCode

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- The empty oracle. -/
private def emptyO : ℕ →. ℕ := fun _ => Part.some 0

/-- `p = pair (encode base) (pair e k)`; `w = pair (encode ext) fuel`.
`ehTest p w = 0` iff `evaln fuel (base ++ ext) (ofNatCode e) k` halts. -/
private def ehTest (p w : ℕ) : ℕ :=
  if (evaln (Nat.unpair w).2
      (((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD [])
        ++ ((Encodable.decode (α := List ℕ) (Nat.unpair w).1).getD []))
      (ofNatCode (Nat.unpair (Nat.unpair p).2).1)
      (Nat.unpair (Nat.unpair p).2).2).isSome then 0 else 1

private theorem ehTest_prim : Nat.Primrec (fun v => ehTest (Nat.unpair v).1 (Nat.unpair v).2) := by
  refine Primrec.nat_iff.mp ?_
  have hbase : Primrec fun v : ℕ =>
      (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const ([] : List ℕ))
  have hext : Primrec fun v : ℕ =>
      (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).2).1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.const ([] : List ℕ))
  have hfuel : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair v).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hcode : Primrec fun v : ℕ =>
      ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 :=
    (Primrec.ofNat OracleCode).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
  have hk : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  have hev : Primrec fun v : ℕ =>
      evaln (Nat.unpair (Nat.unpair v).2).2
        (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [])
          ++ ((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).2).1).getD []))
        (ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 :=
    evaln_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hfuel
      (Primrec.list_append.comp hbase hext)) hcode) hk)
  have hci : ∀ b : Bool, (cond b (0 : ℕ) 1) = if b then (0 : ℕ) else 1 :=
    fun b => by cases b <;> rfl
  exact (Primrec.cond (Primrec.option_isSome.comp hev)
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => by
    simp only [ehTest, Nat.unpair_pair]
    exact hci _

/-- The rfind predicate: `true` exactly when `ehTest a n = 0`. -/
private def ehPred (a : ℕ) : ℕ →. Bool :=
  fun n => (fun m => decide (m = 0)) <$> (Part.some (ehTest a n) : Part ℕ)

/-- The search functional: halts on `a` iff some extension makes the machine
halt. -/
private noncomputable def ehFun (a : ℕ) : Part ℕ := Nat.rfind (ehPred a)

private theorem ehFun_partrec : Nat.Partrec ehFun := by
  have h1 : Nat.Partrec
      (fun v : ℕ => (Part.some (ehTest (Nat.unpair v).1 (Nat.unpair v).2) : Part ℕ)) :=
    Nat.Partrec.of_primrec ehTest_prim
  refine (Nat.Partrec.rfind h1).of_eq fun a => ?_
  simp only [Nat.unpair_pair]
  rfl

private theorem ehPred_dom (a n : ℕ) : (ehPred a n).Dom := by
  rw [ehPred, Part.map_eq_map, Part.map_some]; trivial

private theorem true_mem_ehPred (a n : ℕ) : true ∈ ehPred a n ↔ ehTest a n = 0 := by
  rw [ehPred, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    rw [Part.mem_some_iff.mp hx] at hx0
    exact of_decide_eq_true hx0
  · intro h
    exact ⟨ehTest a n, Part.mem_some _, by simp [h]⟩

/-- `ehFun a` halts iff some `(ext, fuel)` makes `evaln` converge. -/
private theorem ehFun_dom (a : ℕ) :
    (ehFun a).Dom ↔ ∃ w, ehTest a w = 0 := by
  rw [ehFun, Nat.rfind_dom]
  constructor
  · rintro ⟨w, hw, -⟩
    exact ⟨w, (true_mem_ehPred a w).mp hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (true_mem_ehPred a w).mpr hw, fun {m} _ => ehPred_dom a m⟩

/-- **The extension-halting problem is decidable in `0′`.**  As a function of
`p = ⟪encode base, ⟪e, k⟫⟫`, the answer to "does machine `e` halt on `k`
under some finite extension of `base`?" is recursive in the jump of `∅`. -/
theorem extHalting_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((if (∃ w, ehTest p w = 0) then 1 else 0 : ℕ) : Part ℕ)) := by
  have hrec : Nat.RecursiveIn {emptyO} ehFun := ehFun_partrec.recursiveIn
  have := domain_recursiveIn_jump hrec
  refine this.of_eq fun p => ?_
  have hd := ehFun_dom p
  simp only [hd]

#print axioms extHalting_recursiveIn_jump

end OracleCode
