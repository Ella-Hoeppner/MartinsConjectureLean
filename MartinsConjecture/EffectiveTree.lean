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

/-! ### Finite oracle prefixes and branches -/

/-- `x` is a **branch** of the tree `T` (a predicate on finite binary strings):
all of its finite prefixes lie in `T`. -/
def IsBranch (T : List Bool → Prop) (x : ℕ → Bool) : Prop :=
  ∀ n, T ((List.range n).map x)

/-- The real obtained by padding a finite string with `false`s. -/
def extReal (τ : List Bool) : ℕ → Bool := fun i => τ.getD i false

theorem extReal_eq {τ : List Bool} {i : ℕ} (hi : i < τ.length) : extReal τ i = τ[i] := by
  simp only [extReal, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- The bit computed by code `e` from the finite oracle prefix `τ`, using `|τ|`
steps of fuel and `τ` as the oracle table. -/
def fbit (e : ℕ) (τ : List Bool) (j : ℕ) : Option ℕ :=
  evaln τ.length (τ.map bbit) (ofNatCode e) j

/-- **Finite-prefix soundness.**  If code `e` computes bit `v` at `j` from the
finite oracle prefix `τ`, then every real extending `τ` genuinely computes `v`
there. -/
theorem fbit_sound {e : ℕ} {τ : List Bool} {j v : ℕ} (h : fbit e τ j = some v)
    {z : ℕ → Bool} (hz : ∀ i (hi : i < τ.length), z i = τ[i]) :
    v ∈ eval (toPFun z) (ofNatCode e) j := by
  refine evaln_sound (fun i hi => ?_) h
  have hiτ : i < τ.length := by simpa using hi
  simp only [toPFun_eq_bitg, List.getElem_map, bitg_eq_bbit]
  rw [hz i hiτ]

/-- The real obtained by concatenating a finite string `σ` in front of a branch
`y`.  Used to turn a König branch of the suffix tree back into a genuine branch. -/
def catReal (σ : List Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if h : i < σ.length then σ[i] else y (i - σ.length)

theorem catReal_prefix (σ : List Bool) (y : ℕ → Bool) {k : ℕ} (hk : σ.length ≤ k) :
    (List.range k).map (catReal σ y) = σ ++ (List.range (k - σ.length)).map y := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    by_cases hi : i < σ.length
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [catReal, hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [catReal, hi, dif_neg, not_false_iff]
      rw [List.getElem_map, List.getElem_range]

theorem catReal_take (σ : List Bool) (y : ℕ → Bool) {k : ℕ} (hk : k ≤ σ.length) :
    (List.range k).map (catReal σ y) = σ.take k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_take]
    have hi : i < σ.length := by simp at h1; omega
    simp [catReal, hi]

end Martin
