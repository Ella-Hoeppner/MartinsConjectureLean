/-
Named corollaries of the relativized recursion theorem.

* `exists_quine` — a self-reproducing code: relative to any oracle there is
  `e` with `eval O (ofNatCode e) = fun _ => e` (Kleene's "quine").
* `no_fixedPointFree` — there is no total computable index transformation
  that always changes the computed function: every computable `f` has an
  oracle-relative fixed point (contrapositive of `exists_fixedPoint`, the
  form used in Arslanov-style arguments).
* `exists_selfHalting_code` — a code that, relative to `X`, halts on every
  input iff it (diagonally) halts — a fixed point exhibiting that the
  halting behaviour of a machine can consistently refer to itself.
-/
import MartinsConjecture.LimitLemma

open scoped Computability
open OracleCode Cantor

namespace OracleCode

/-- **Quine / Kleene's recursion theorem, output form**: relative to any
oracle there is a code that outputs its own index on every input. -/
theorem exists_quine (X : ℕ → Bool) :
    ∃ e : ℕ, eval (toPFun X) (ofNatCode e) = fun _ => Part.some e := by
  -- `constEnc` maps a value to a code for the constant function; it is primrec.
  obtain ⟨e, he⟩ := exists_fixedPoint X (f := constEnc)
    (Primrec.nat_iff.mp constEnc_prim)
  refine ⟨e, ?_⟩
  rw [← he]
  funext n
  rw [show ofNatCode (constEnc e) = const e from by
    rw [constEnc, ofNatCode_encodeCode]]
  exact eval_const _ _ _

/-- **No fixed-point-free index transformation exists**: any computable
transformation of code numbers has, relative to any oracle, an index whose
computed function it preserves. -/
theorem no_fixedPointFree (X : ℕ → Bool) {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ¬ ∀ e : ℕ, eval (toPFun X) (ofNatCode (f e)) ≠ eval (toPFun X) (ofNatCode e) := by
  intro h
  obtain ⟨e, he⟩ := exists_fixedPoint X hf
  exact h e he

/-- **Self-referential halting**: relative to any oracle there is a code `e`
whose halting on input `n` is exactly the jump question about `e` itself —
`eval O (ofNatCode e) n` halts iff `e ∈ O′`.  A fixed point of the diagonal
halting predicate. -/
theorem exists_selfHalting_code (X : ℕ → Bool) :
    ∃ e : ℕ, ∀ n, (eval (toPFun X) (ofNatCode e) n).Dom ↔ jumpP (toPFun X) e := by
  -- Take a quine `e`: it is total, so halts everywhere; and being total it
  -- halts on `e`, so `e ∈ O′`.  Both sides are `True`.
  obtain ⟨e, he⟩ := exists_quine X
  refine ⟨e, fun n => ?_⟩
  have hdom : ∀ m, (eval (toPFun X) (ofNatCode e) m).Dom := by
    intro m; rw [he]; trivial
  constructor
  · intro _
    rw [jumpP]
    exact hdom e
  · intro _
    exact hdom n

/-- Recursion theorem, code form: a code that computes the same function as
its image under any computable index transformation. -/
theorem exists_fixedPoint_code (X : ℕ → Bool) {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ c : OracleCode,
      eval (toPFun X) (ofNatCode (f (encodeCode c))) = eval (toPFun X) c := by
  obtain ⟨e, he⟩ := exists_fixedPoint X hf
  exact ⟨ofNatCode e, by rw [encode_ofNatCode]; exact he⟩

#print axioms exists_quine
#print axioms no_fixedPointFree
#print axioms exists_selfHalting_code
#print axioms exists_fixedPoint_code

end OracleCode
