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
import Mathlib.Data.Fintype.Vector

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

/-- `τ` is **consistent** with the real `w`: every bit that its finite computation
converges to matches `w`.  (Weaker than requiring convergence — this is what makes
it prefix-closed, so both "wrong nodes die" and "right nodes survive".) -/
def Consistent (e : ℕ) (w : ℕ → Bool) (τ : List Bool) : Prop :=
  ∀ j v, fbit e τ j = some v → v = bitg w j

/-- Consistency is prefix-closed: dropping the last bit of a consistent node keeps
it consistent (a shorter computation persists under more fuel/oracle). -/
theorem consistent_of_append {e : ℕ} {w : ℕ → Bool} {τ : List Bool} {b : Bool}
    (h : Consistent e w (τ ++ [b])) : Consistent e w τ := by
  intro j v hv
  refine h j v ?_
  simp only [fbit] at hv ⊢
  refine evaln_mono (by simp) ?_ hv
  exact ⟨[bbit b], by simp⟩

/-- Every finite prefix of a branch is consistent with the branch's value. -/
theorem consistent_take {T : List Bool → Prop} {e : ℕ} {g : (ℕ → Bool) → ℕ → Bool}
    (hg : ∀ y, IsBranch T y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    {x : ℕ → Bool} (hx : IsBranch T x) (m : ℕ) :
    Consistent e (g x) ((List.range m).map x) := by
  intro j v hv
  have hmap : ((List.range m).map x).map bbit = graphOf (bitg x) m := by
    simp [graphOf, List.map_map, Function.comp, bitg_eq_bbit]
  simp only [fbit, List.length_map, List.length_range, hmap] at hv
  have : v ∈ eval (toPFun x) (ofNatCode e) j := evaln_sound (graphOf_sound (toPFun_eq_bitg x) m) hv
  rw [hg x hx, toPFun_eq_bitg] at this
  exact Part.mem_some_iff.mp this

/-- **The separation lemma** (compactness core of Lemma 2.1).  For a computable
injective functional `g` (code `e`) on the branches of a tree `T`, and a branch
`x`, any *wrong* node `σ` (`σ ≠ x↾|σ|`) has a level `m` past which **no** descendant
`τ` of `σ` in `T` is consistent with `g x`.  (Otherwise König's lemma produces a
branch `z` through `σ` with `g z = g x`, so `z = x` and `σ = x↾|σ|`.) -/
theorem separation {T : List Bool → Prop} (hTclosed : ∀ σ b, T (σ ++ [b]) → T σ)
    {e : ℕ} {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ y, IsBranch T y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    (hinj : ∀ y y', IsBranch T y → IsBranch T y' → g y = g y' → y = y')
    {x : ℕ → Bool} (hx : IsBranch T x)
    {σ : List Bool} (hσne : σ ≠ (List.range σ.length).map x) :
    ∃ M, ∀ τ, T τ → σ <+: τ → Consistent e (g x) τ → τ.length < M := by
  by_contra hcon
  push_neg at hcon
  set S : List Bool → Prop := fun t =>
    T (σ ++ t) ∧ Consistent e (g x) (σ ++ t) with hSdef
  have hSclosed : ∀ t b, S (t ++ [b]) → S t := by
    intro t b ht
    obtain ⟨hT1, hcons⟩ := ht
    rw [← List.append_assoc] at hT1 hcons
    exact ⟨hTclosed _ _ hT1, consistent_of_append hcons⟩
  have hSinf : Konig.HasInf S [] := by
    intro m
    obtain ⟨τ, hτT, hτpre, hτcons, hτlen⟩ := hcon (σ.length + m)
    obtain ⟨t, rfl⟩ := hτpre
    refine ⟨t, ⟨hτT, hτcons⟩, ?_, ?_⟩
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
  -- g z = g x, because every prefix of z is consistent and z's value converges.
  have hgzx : g z = g x := by
    funext j
    have hzval : bitg (g z) j ∈ eval (toPFun z) (ofNatCode e) j := by
      rw [hg z hzbranch, toPFun_eq_bitg]; exact Part.mem_some _
    obtain ⟨K, hK⟩ := evaln_complete (toPFun_eq_bitg z) hzval
    set m := K + σ.length + 1 with hm
    have hzm_cons : Consistent e (g x) ((List.range m).map z) := by
      have h3 : (List.range m).map z = σ ++ (List.range (m - σ.length)).map y' := by
        rw [hzdef, catReal_prefix σ y' (by omega)]
      rw [h3]; exact (hy' (m - σ.length)).2
    have hmap : ((List.range m).map z).map bbit = graphOf (bitg z) m := by
      simp [graphOf, List.map_map, Function.comp, bitg_eq_bbit]
    have hfbit : fbit e ((List.range m).map z) j = some (bitg (g z) j) := by
      simp only [fbit, List.length_map, List.length_range, hmap]
      exact evaln_mono (by omega) (graphOf_prefix (by omega)) hK
    exact cond_one_zero_inj (hzm_cons j (bitg (g z) j) hfbit)
  exact hσne (hσz.symm.trans (congrArg (fun f => (List.range σ.length).map f)
    (hinj z x hzbranch hx hgzx)))

/-! ### The search that computes the branch from its image and the tree -/

/-- The search predicate: at level `m`, some length-`m` node of `T` is consistent
with `w`, and *all* consistent length-`m` nodes share their first `n` bits.  When
this holds, that common `n`-prefix is `x↾n` (`search_correct`), and it holds for
some `m` (`search_terminates`). -/
def searchGood (T : List Bool → Prop) (e : ℕ) (w : ℕ → Bool) (n m : ℕ) : Prop :=
  (∃ τ, T τ ∧ τ.length = m ∧ Consistent e w τ) ∧
  (∀ τ τ', T τ → τ.length = m → Consistent e w τ →
    T τ' → τ'.length = m → Consistent e w τ' → τ.take n = τ'.take n)

/-- **Correctness of the search.**  When `searchGood` holds at level `m ≥ n`, every
consistent length-`m` node's first `n` bits are exactly `x↾n` (because `x↾m` is
itself a consistent length-`m` node). -/
theorem search_correct {T : List Bool → Prop} {e : ℕ} {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ y, IsBranch T y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    {x : ℕ → Bool} (hx : IsBranch T x) {n m : ℕ} (hnm : n ≤ m)
    (hgood : searchGood T e (g x) n m) {τ₀ : List Bool}
    (hτ₀T : T τ₀) (hτ₀len : τ₀.length = m) (hτ₀cons : Consistent e (g x) τ₀) :
    τ₀.take n = (List.range n).map x := by
  have hxm := hgood.2 τ₀ ((List.range m).map x) hτ₀T hτ₀len hτ₀cons
    (hx m) (by simp) (consistent_take hg hx m)
  rw [hxm, ← List.map_take, List.take_range, Nat.min_eq_left hnm]

/-- **Termination of the search.**  `searchGood` holds at some level `m ≥ n`: past
the (finitely many) death levels of the wrong length-`n` nodes, every consistent
length-`m` node has first `n` bits `x↾n`, and `x↾m` is such a node. -/
theorem search_terminates {T : List Bool → Prop} (hTclosed : ∀ σ b, T (σ ++ [b]) → T σ)
    {e : ℕ} {g : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ y, IsBranch T y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    (hinj : ∀ y y', IsBranch T y → IsBranch T y' → g y = g y' → y = y')
    {x : ℕ → Bool} (hx : IsBranch T x) (n : ℕ) :
    ∃ m, n ≤ m ∧ searchGood T e (g x) n m := by
  classical
  have hbd : ∀ f : Fin n → Bool, ∃ M, List.ofFn f ≠ (List.range n).map x →
      ∀ τ, T τ → List.ofFn f <+: τ → Consistent e (g x) τ → τ.length < M := by
    intro f
    by_cases hw : List.ofFn f = (List.range n).map x
    · exact ⟨0, fun h => absurd hw h⟩
    · obtain ⟨M, hM⟩ := separation hTclosed hg hinj hx
        (show List.ofFn f ≠ (List.range (List.ofFn f).length).map x by
          rw [List.length_ofFn]; exact hw)
      exact ⟨M, fun _ => hM⟩
  choose bd hbd using hbd
  set M := (Finset.univ : Finset (Fin n → Bool)).sup bd with hMdef
  refine ⟨max M n, le_max_right _ _,
    ⟨(List.range (max M n)).map x, hx _, by simp, consistent_take hg hx _⟩, ?_⟩
  have key : ∀ ρ, T ρ → ρ.length = max M n → Consistent e (g x) ρ →
      ρ.take n = (List.range n).map x := by
    intro ρ hρT hρlen hρcons
    by_contra hne
    have hlen_n : (ρ.take n).length = n := by rw [List.length_take, hρlen]; omega
    set f : Fin n → Bool := fun i => (ρ.take n).getD i false with hf
    have hof : List.ofFn f = ρ.take n := by
      apply List.ext_getElem (by simp [hlen_n])
      intro i h1 h2
      simp only [hf, List.getElem_ofFn]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
    have hbound := hbd f (by rw [hof]; exact hne) ρ hρT
      (by rw [hof]; exact List.take_prefix n ρ) hρcons
    have hle : bd f ≤ M := Finset.le_sup (Finset.mem_univ f)
    omega
  intro τ τ' hτT hτlen hτcons hτ'T hτ'len hτ'cons
  rw [key τ hτT hτlen hτcons, key τ' hτ'T hτ'len hτ'cons]

end Martin
