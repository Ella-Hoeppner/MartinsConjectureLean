/-
The s-m-n (parametrization) theorem and the Padding Lemma.

* **`smn`** — a primitive recursive `s` with
  `eval O (ofNatCode (s e n)) x = eval O (ofNatCode e) (pair n x)`, uniformly
  in every oracle (the parametrization / s-m-n theorem, here `s = curryEnc`).
* **`padCode`** / **`eval_padCode`** — an injective family of codes all
  computing the same function; hence **`infinite_indices`**: every function
  recursive in `O` has infinitely many indices (the Padding Lemma).
-/
import MartinsConjecture.Universal

open scoped Computability
open OracleCode

namespace OracleCode

/-- **s-m-n / parametrization theorem**: `curryEnc` is a primitive recursive
index transformation specializing the first argument, uniformly in the
oracle. -/
theorem smn (O : ℕ →. ℕ) (e n x : ℕ) :
    eval O (ofNatCode (curryEnc e n)) x
      = eval O (ofNatCode e) (Nat.pair n x) := by
  have h1 : curryEnc e n = encodeCode (curry (ofNatCode e) n) := by
    rw [encodeCode_curry, encode_ofNatCode]
  rw [h1, ofNatCode_encodeCode, eval_curry]

theorem smn_primrec : Primrec₂ curryEnc := curryEnc_prim

/-! ### Padding -/

/-- Wrap a code in `k` layers of identity-composition. -/
def padCode (c : OracleCode) : ℕ → OracleCode
  | 0 => c
  | k + 1 => .comp (padCode c k) idCode

/-- All padded codes compute the same function. -/
theorem eval_padCode (O : ℕ →. ℕ) (c : OracleCode) :
    ∀ k, eval O (padCode c k) = eval O c
  | 0 => rfl
  | k + 1 => by
    funext x
    rw [padCode, eval_comp, eval_idCode]
    rw [show (Part.some x >>= eval O (padCode c k)) = eval O (padCode c k) x
      from Part.bind_some _ _]
    rw [eval_padCode O c k]

/-- Composition strictly increases the code number. -/
theorem lt_encodeCode_comp (cf cg : OracleCode) :
    encodeCode cf < encodeCode (.comp cf cg) := by
  rw [encodeCode_comp, compEnc]
  have := Nat.left_le_pair (encodeCode cf) (encodeCode cg)
  omega

/-- The padded codes have strictly increasing indices. -/
theorem strictMono_encode_padCode (c : OracleCode) :
    StrictMono (fun k => encodeCode (padCode c k)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_encodeCode_comp (padCode c k) idCode

/-- The index map `k ↦ encodeCode (padCode c k)` is injective. -/
theorem injective_encode_padCode (c : OracleCode) :
    Function.Injective (fun k => encodeCode (padCode c k)) :=
  (strictMono_encode_padCode c).injective

/-- **The Padding Lemma**: every function recursive in `O` has infinitely
many indices. -/
theorem infinite_indices {O f : ℕ →. ℕ} (hf : Nat.RecursiveIn {O} f) :
    {e : ℕ | eval O (ofNatCode e) = f}.Infinite := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn hf
  refine Set.infinite_of_injective_forall_mem (f := fun k => encodeCode (padCode c k))
    (injective_encode_padCode c) (fun k => ?_)
  rw [Set.mem_setOf_eq, ofNatCode_encodeCode, eval_padCode O c k, hc]

#print axioms smn
#print axioms eval_padCode
#print axioms infinite_indices

end OracleCode
