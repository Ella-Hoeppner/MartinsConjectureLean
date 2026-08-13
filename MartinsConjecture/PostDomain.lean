/-
Post's theorem, Σ₁ direction: the domain of a partial `O`-recursive function
is decidable in `O′`.

`dom_iff_jumpP` (`LimitLemma.lean`) turns each individual halting question
into a diagonal jump question at a primitively-computed code.  Assembling
over a fixed code `c` for `f` gives that the *whole* domain predicate of `f`
is computable from the jump:

* **`domain_recursiveIn_jump`** — `fun n => [(f n).Dom]` (as a 0/1 function)
  is recursive in `jumpFn O`, for any `f` recursive in `O`;
* **`halting_recursiveIn_jump`** — the special case: the diagonal halting
  predicate of `O` is decidable in `O′`.

This is the Σ₁-in-`O` ≤ᵀ `O′` half of Post's theorem, and the recursion-
theoretic engine of the (0′-computable) finite-extension constructions such
as Kleene–Post below `0′`.
-/
import MartinsConjecture.LimitLemma

open scoped Computability
open OracleCode

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- **Post's theorem, Σ₁ direction.**  If `f` is recursive in `O`, then the
characteristic function of its domain is recursive in the jump `O′`. -/
theorem domain_recursiveIn_jump {O f : ℕ →. ℕ} (hf : Nat.RecursiveIn {O} f) :
    Nat.RecursiveIn {jumpFn O}
      (fun n : ℕ => ((if (f n).Dom then 1 else 0 : ℕ) : Part ℕ)) := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn hf
  -- the primitive-recursive family of jump-codes deciding halting of `c`.
  set q : ℕ → ℕ := fun n => compEnc (encodeCode c) (constEnc n) with hq
  have hqP : Nat.Primrec q := by
    rw [hq]
    exact Primrec.nat_iff.mp (compEnc_prim.comp (Primrec.const (encodeCode c))
      constEnc_prim)
  have hkey : ∀ n, (f n).Dom ↔ jumpP O (q n) := by
    intro n
    rw [hq, ← hc]
    have := dom_iff_jumpP O (encodeCode c) n
    rwa [ofNatCode_encodeCode] at this
  -- query the jump at `q n`.
  have hquery : Nat.RecursiveIn {jumpFn O}
      (fun n : ℕ => ((q n : ℕ) : Part ℕ) >>= jumpFn O) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) hqP.recursiveIn
  refine hquery.of_eq fun n => ?_
  have hval : jumpFn O (q n) = ((if (f n).Dom then 1 else 0 : ℕ) : Part ℕ) := by
    rw [jumpFn, Part.coe_some]
    by_cases hd : (f n).Dom
    · rw [if_pos hd, if_pos ((hkey n).mp hd)]
    · rw [if_neg hd, if_neg (fun hcc => hd ((hkey n).mpr hcc))]
  rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some, hval]

/-- **The general halting problem relative to a total oracle is decidable in
its jump**: for a Cantor point `X`, the predicate `(e, n) ↦ Φₑˣ(n)↓` is
recursive in `X′`.  (Uses the universal machine `eval_universal`, so it needs
a total oracle.) -/
theorem general_halting_recursiveIn_jump (X : ℕ → Bool) :
    Nat.RecursiveIn {jumpFn (Cantor.toPFun X)}
      (fun p : ℕ =>
        ((if (eval (Cantor.toPFun X) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2).Dom
          then 1 else 0 : ℕ) : Part ℕ)) :=
  domain_recursiveIn_jump (eval_universal X)

#print axioms domain_recursiveIn_jump
#print axioms general_halting_recursiveIn_jump

end OracleCode
