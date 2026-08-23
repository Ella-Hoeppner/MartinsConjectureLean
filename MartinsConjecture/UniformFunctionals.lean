/-
The "computable monoid of functionals" facts underlying uniform-invariance
arguments (Bard 2019, Lutz thesis Ch. 3), built on the existing
oracle-substitution operator `trOracle`/`trE` (= computable composition of
Turing functionals) and the universal machine.

* `Cantor.le_iff_bitg` — general bridge: `X ≤ᵀ Y` iff the bit-graph of `X` is
  recursive in `Y` (the un-jumped analogue of `le_jump_iff_bitg`).
* `OracleCode.eval_trE_comp` + `trE_primrec` — **computable composition of
  functionals**: if `Φ_j^X = A` then `Φ_i^A = Φ_{trE j·i}^X`, with the index map
  primitive recursive.  This is Bard's `∗`, the linchpin of his computable
  uniformity lemma.
* `Cantor.joinFam_le` — **Bard's Fact 3.1**: a family of reals uniformly
  computable from `A` has join `≤ᵀ A`.
-/
import MartinsConjecture.UniformJoin
import MartinsConjecture.CantorLimit

open scoped Computability
open OracleCode Cantor

namespace Cantor

/-- General bit-graph bridge: `X ≤ᵀ Y` iff the 0/1 bit-graph of `X` is recursive
in `Y`.  (The un-jumped analogue of `Cantor.le_jump_iff_bitg`.) -/
theorem le_iff_bitg {X Y : ℕ → Bool} :
    X ≤ₜ Y ↔ Nat.RecursiveIn {toPFun Y} (fun n : ℕ => ((bitg X n : ℕ) : Part ℕ)) := by
  rw [Cantor.le]
  constructor
  · intro h
    exact (RecursiveIn.iff_nat.mp h).of_eq fun _ => rfl
  · intro h
    exact RecursiveIn.iff_nat.mpr (h.of_eq fun _ => rfl)

end Cantor

namespace OracleCode

/-- **Computable composition of Turing functionals.**  If code `j` computes the
real `A` from oracle `X` (`Φ_j^X = A`), then for every code `i` the translated
code `trE (ofNatCode j) i` runs `Φ_i` with oracle `A` while querying only `X`:
`Φ_i^A = Φ_{trE j·i}^X`.  Together with `trE_primrec` (the index map is primitive
recursive) this is a *computable* composition operation on indices — Bard's `∗`,
and the reason Turing functionals form a computable monoid under composition. -/
theorem eval_trE_comp {X A : ℕ → Bool} {j : ℕ}
    (hj : eval (toPFun X) (ofNatCode j) = toPFun A) (i : ℕ) :
    eval (toPFun X) (ofNatCode (trE (ofNatCode j) i)) = eval (toPFun A) (ofNatCode i) := by
  simp only [trE, ofNatCode_encodeCode]
  exact eval_trOracle hj (ofNatCode i)

end OracleCode

namespace Cantor

/-- The recursive join of a countable family of reals: `joinFam R ⟨n, k⟩ = R n k`. -/
def joinFam (R : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun m => R (Nat.unpair m).1 (Nat.unpair m).2

/-- **Bard's Fact 3.1.**  If a family of reals `R n` is *uniformly* computable
from `A` — via a primitive-recursive index function `t` with `Φ_{t n}^A = R n`
for every `n` — then the join `⨁ₙ R n` is Turing-below `A`. -/
theorem joinFam_le {A : ℕ → Bool} {t : ℕ → ℕ} (ht : Primrec t) {R : ℕ → ℕ → Bool}
    (hR : ∀ n, eval (toPFun A) (ofNatCode (t n)) = toPFun (R n)) :
    joinFam R ≤ₜ A := by
  rw [le_iff_bitg]
  have hbuilder : Primrec (fun m : ℕ => Nat.pair (t (Nat.unpair m).1) (Nat.unpair m).2) :=
    Primrec₂.natPair.comp (ht.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  refine (Nat.RecursiveIn.comp (eval_universal A)
    (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp hbuilder))).of_eq fun m => ?_
  rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  simp only [Nat.unpair_pair]
  rw [hR (Nat.unpair m).1]
  rfl

/-- **Each component of a countable join is Turing-below the join** (the reverse of `joinFam_le`):
`R n ≤ᵀ joinFam R`, since `R n k = joinFam R ⟨n, k⟩` is computed from `joinFam R` by pairing `k` with the
fixed column `n`. -/
theorem component_le_joinFam (R : ℕ → ℕ → Bool) (n : ℕ) : R n ≤ₜ joinFam R := by
  rw [le_iff_bitg]
  refine (Nat.RecursiveIn.comp (le_iff_bitg.mp (Cantor.le.refl (joinFam R)))
    ((Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.const n) Primrec.id)).recursiveIn)).of_eq
    fun k => ?_
  rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  simp only [bitg, joinFam, Nat.unpair_pair, id_eq]

end Cantor

#print axioms Cantor.le_iff_bitg
#print axioms OracleCode.eval_trE_comp
#print axioms Cantor.joinFam_le
#print axioms Cantor.component_le_joinFam
