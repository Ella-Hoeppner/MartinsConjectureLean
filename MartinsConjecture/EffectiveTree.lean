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

theorem cond_one_zero_inj {a b : Bool} (h : (cond a 1 0 : ℕ) = cond b 1 0) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `τ`'s computed bits agree with the real `w` up to `|τ|`. -/
def Agrees (e : ℕ) (w : ℕ → Bool) (τ : List Bool) : Prop :=
  ∀ j (hj : j < τ.length), fbit e τ j = some (bitg w j)

/-- **The separation lemma** (compactness core of Lemma 2.1).  For a computable
injective functional `g` (code `e`) on the branches of a tree `T`, and a branch
`x`, any *wrong* node `σ` (`σ ≠ x↾|σ|`) has a level `m` past which **no** descendant
`τ` of `σ` in `T` computes bits agreeing with `g x`.  (Otherwise König's lemma
produces a branch `z` through `σ` with `g z = g x`, so `z = x` and `σ = x↾|σ|`.) -/
theorem separation {T : List Bool → Prop} (hTclosed : ∀ σ b, T (σ ++ [b]) → T σ)
    {e : ℕ} {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ y, IsBranch T y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    (hinj : ∀ y y', IsBranch T y → IsBranch T y' → g y = g y' → y = y')
    {x : ℕ → Bool} (hx : IsBranch T x)
    {σ : List Bool} (hσne : σ ≠ (List.range σ.length).map x) :
    ∃ m, ∀ τ, T τ → σ <+: τ → τ.length = m → ¬ Agrees e (g x) τ := by
  by_contra hcon
  push_neg at hcon
  -- The suffix tree of nodes with an agreeing extension.
  set S : List Bool → Prop := fun t =>
    T (σ ++ t) ∧ ∃ τ, T τ ∧ (σ ++ t) <+: τ ∧ Agrees e (g x) τ with hSdef
  have hSclosed : ∀ t b, S (t ++ [b]) → S t := by
    intro t b ht
    obtain ⟨hT1, τ, hτT, hτpre, hτag⟩ := ht
    rw [← List.append_assoc] at hT1 hτpre
    exact ⟨hTclosed _ _ hT1, τ, hτT, (List.prefix_append (σ ++ t) [b]).trans hτpre, hτag⟩
  have hSinf : Konig.HasInf S [] := by
    intro m
    obtain ⟨τ, hτT, hτpre, hτlen, hτag⟩ := hcon (σ.length + m)
    obtain ⟨t, rfl⟩ := hτpre
    refine ⟨t, ⟨hτT, σ ++ t, hτT, List.prefix_rfl, hτag⟩, ?_, ?_⟩
    · simp
    · simp only [List.length_append] at hτlen; omega
  obtain ⟨y', hy'⟩ := Konig.exists_branch hSclosed hSinf
  set z := catReal σ y' with hzdef
  have hzbranch : IsBranch T z := by
    intro k
    by_cases hk : σ.length ≤ k
    · rw [hzdef, catReal_prefix σ y' hk]; exact (hy' (k - σ.length)).1
    · rw [hzdef, catReal_take σ y' (by omega)]
      exact Konig.mem_of_prefix hTclosed σ (by
        have := (hy' 0).1; simpa using this) _ (List.take_prefix k σ)
  have hσz : (List.range σ.length).map z = σ := by
    rw [hzdef, catReal_take σ y' (le_refl _), List.take_length]
  -- g z = g x, via the use principle and the agreeing extensions.
  have hgzx : g z = g x := by
    funext j
    have hzval : bitg (g z) j ∈ eval (toPFun z) (ofNatCode e) j := by
      rw [hg z hzbranch, toPFun_eq_bitg]; exact Part.mem_some _
    obtain ⟨K, hK⟩ := use_principle hzval
    set k := K + σ.length + j + 1 with hkdef
    obtain ⟨hT1, τ, hτT, hτpre, hτag⟩ := hy' (k - σ.length)
    have hzk : (List.range k).map z = σ ++ (List.range (k - σ.length)).map y' := by
      rw [hzdef, catReal_prefix σ y' (by omega)]
    have hzk_pre : (List.range k).map z <+: τ := by rw [hzk]; exact hτpre
    have hklen : ((List.range k).map z).length = k := by simp
    have hτk : k ≤ τ.length := by have h := hzk_pre.length_le; rwa [hklen] at h
    have hjτ : j < τ.length := by omega
    have hgx_mem : bitg (g x) j ∈ eval (toPFun (extReal τ)) (ofNatCode e) j :=
      fbit_sound (hτag j hjτ) (fun i hi => extReal_eq hi)
    have hagreeK : ∀ i, i < K → extReal τ i = z i := by
      intro i hiK
      have hik : i < k := by omega
      obtain ⟨w, hw⟩ := hzk_pre
      have happ : extReal τ i = ((List.range k).map z ++ w).getD i false := by rw [← hw]; rfl
      have hlt : i < ((List.range k).map z).length := by rw [hklen]; omega
      rw [happ, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      simp [List.getElem?_map, List.getElem?_range, hik]
    have hgz_mem : bitg (g z) j ∈ eval (toPFun (extReal τ)) (ofNatCode e) j :=
      hK (extReal τ) hagreeK
    exact cond_one_zero_inj (Part.mem_unique hgz_mem hgx_mem)
  exact hσne (hσz.symm.trans (congrArg (fun f => (List.range σ.length).map f)
    (hinj z x hzbranch hx hgzx)))

end Martin
