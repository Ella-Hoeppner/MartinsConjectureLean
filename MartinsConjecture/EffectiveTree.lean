/-
**Toward Lutz–Siskind Lemma 2.1** (effective injectivity on perfect trees):
a computable injective functional on a perfect tree lets the branch be recovered
from its image together with the tree.

This file builds the two analytic pillars — the **use principle** (forward
continuity: a converging oracle computation depends on only a finite prefix of the
oracle) and, on top of König's lemma (`Konig.exists_branch`), the compactness
argument that the recovery search terminates.
-/
import MartinsConjecture.Konig
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.Universal

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- **The use principle** (forward continuity).  If code `e` run with oracle `x`
converges to `v` at input `k`, then it does so using only a finite prefix of `x`:
there is a bound `K` such that *any* oracle `x'` agreeing with `x` on the first `K`
bits yields the same value. -/
theorem use_principle {e : ℕ} {x : ℕ → Bool} {k v : ℕ}
    (h : v ∈ eval (toPFun x) (ofNatCode e) k) :
    ∃ K, ∀ x' : ℕ → Bool, (∀ i, i < K → x' i = x i) →
      v ∈ eval (toPFun x') (ofNatCode e) k := by
  obtain ⟨K, hK⟩ := evaln_complete (toPFun_eq_bitg x) h
  refine ⟨K, fun x' hx' => evaln_sound (fun i hi => ?_) hK⟩
  have hiK : i < K := by simpa using hi
  rw [← graphOf_sound (toPFun_eq_bitg x) K i hi, toPFun_eq_bitg, toPFun_eq_bitg]
  congr 1
  unfold bitg
  rw [hx' i hiK]

end Martin
