/-
The Kleene–Post theorem: incomparable Turing degrees exist.

The classical finite-extension argument (Kleene–Post 1954), built on the use
principle `eval_locality`: two reals `A, B` are constructed in stages as
limits of finite strings; at stage `2e` the pair of strings is extended so
that machine `e` fails to compute `A` from any oracle extending the
`B`-string (either by forcing a convergent computation and diagonalizing the
`A`-bit against its value, or — if no total extension yields convergence —
by doing nothing, since divergence is then automatic); odd stages are
symmetric.

Main results:
* `KleenePost.step` — the single-requirement extension lemma (the
  combinatorial heart).
* `KleenePost.kleene_post` — `∃ A B, ¬ A ≤ₜ B ∧ ¬ B ≤ₜ A`.
* `TuringDegree.exists_incomparable` — incomparable elements of Mathlib's
  `TuringDegree`; in particular the degree order is not linear
  (`TuringDegree.not_isTotal_le`).
-/
import MartinsConjecture.Locality

open scoped Computability
open OracleCode Cantor

namespace KleenePost

/-- `Y` is a total extension of the finite string `σ`. -/
def Agrees (σ : List Bool) (Y : ℕ → Bool) : Prop :=
  ∀ i, i < σ.length → Y i = σ.getD i false

/-- `σ'` end-extends `σ` (as position-value tables). -/
def Ext (σ σ' : List Bool) : Prop :=
  σ.length ≤ σ'.length ∧ ∀ i, i < σ.length → σ'.getD i false = σ.getD i false

theorem ext_rfl (σ : List Bool) : Ext σ σ := ⟨le_refl _, fun _ _ => Eq.refl _⟩

theorem Ext.trans {σ₁ σ₂ σ₃ : List Bool} (h1 : Ext σ₁ σ₂) (h2 : Ext σ₂ σ₃) :
    Ext σ₁ σ₃ :=
  ⟨h1.1.trans h2.1, fun i hi => (h2.2 i (lt_of_lt_of_le hi h1.1)).trans (h1.2 i hi)⟩

theorem Agrees.mono {σ σ' : List Bool} {Y : ℕ → Bool} (h : Ext σ σ')
    (hY : Agrees σ' Y) : Agrees σ Y :=
  fun i hi => (hY i (lt_of_lt_of_le hi h.1)).trans (h.2 i hi)

theorem ext_append (σ : List Bool) (b : Bool) : Ext σ (σ ++ [b]) := by
  constructor
  · simp
  · intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- **The extension step.**  Any pair of strings `(σ, τ)` can be extended to
`(σ', τ')` so that machine `e` with any oracle extending `τ'` fails to
compute (the characteristic function of) any real extending `σ'`. -/
theorem step (σ τ : List Bool) (e : ℕ) :
    ∃ στ' : List Bool × List Bool,
      Ext σ στ'.1 ∧ Ext τ στ'.2 ∧
      σ.length < στ'.1.length ∧ τ.length < στ'.2.length ∧
      ∀ A B : ℕ → Bool, Agrees στ'.1 A → Agrees στ'.2 B →
        eval (toPFun B) (ofNatCode e) ≠ toPFun A := by
  by_cases hcase : ∃ (Y : ℕ → Bool) (v : ℕ),
      Agrees τ Y ∧ v ∈ eval (toPFun Y) (ofNatCode e) σ.length
  · -- Convergence can be forced: freeze the use and flip the diagonal bit.
    obtain ⟨Y', v, hY', hv⟩ := hcase
    -- Replace `Y'` by a version that literally extends `τ` bit-for-bit.
    set Y : ℕ → Bool := fun n => if n < τ.length then τ.getD n false else Y' n with hYdef
    have hYY' : ∀ n, Y n = Y' n := by
      intro n
      by_cases hn : n < τ.length
      · simp only [hYdef, if_pos hn]
        exact (hY' n hn).symm
      · simp [hYdef, hn]
    have hv : v ∈ eval (toPFun Y) (ofNatCode e) σ.length := by
      have : Y = Y' := funext hYY'
      rw [this]
      exact hv
    obtain ⟨L, hL⟩ := eval_locality (ofNatCode e) σ.length v Y hv
    set M := max L τ.length + 1 with hM
    refine ⟨(σ ++ [decide (v ≠ 1)], (List.range M).map Y), ext_append σ _, ?_, ?_, ?_, ?_⟩
    · constructor
      · simp [hM]
        omega
      · intro i hi
        have hiM : i < M := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hiM]
        simp [hYdef, hi]
    · simp
    · simp [hM]
      omega
    · intro A B hA hB heq
      -- `B` agrees with `Y` on the use, so the computation from `B` converges to `v`.
      have hBY : ∀ n, n < L → B n = Y n := by
        intro n hn
        have hnM : n < M := by omega
        have := hB n (by simpa using hnM)
        rw [this]
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hnM]
      have hvB : v ∈ eval (toPFun B) (ofNatCode e) σ.length := hL B hBY
      rw [heq] at hvB
      have hval : v = cond (A σ.length) 1 0 := Part.mem_some_iff.mp hvB
      have hAbit : A σ.length = decide (v ≠ 1) := by
        have := hA σ.length (by simp)
        rw [this]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [hAbit] at hval
      by_cases hv1 : v = 1 <;> simp [hv1] at hval
  · -- Convergence cannot be forced: divergence defeats the requirement.
    refine ⟨(σ ++ [false], τ ++ [false]), ext_append σ _, ext_append τ _,
      by simp, by simp, ?_⟩
    intro A B hA hB heq
    have hdom : (toPFun A σ.length).Dom := trivial
    rw [← heq] at hdom
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
    exact hcase ⟨B, v, Agrees.mono (ext_append τ false) hB, hv⟩

/-! ### The construction -/

/-- One scheduled extension: even stages defeat "compute the left real from
the right" for machine `k / 2`, odd stages the converse. -/
theorem stepEx (p : List Bool × List Bool) (k : ℕ) :
    ∃ p' : List Bool × List Bool,
      Ext p.1 p'.1 ∧ Ext p.2 p'.2 ∧
      p.1.length < p'.1.length ∧ p.2.length < p'.2.length ∧
      (if k % 2 = 0 then
        ∀ A B : ℕ → Bool, Agrees p'.1 A → Agrees p'.2 B →
          eval (toPFun B) (ofNatCode (k / 2)) ≠ toPFun A
      else
        ∀ A B : ℕ → Bool, Agrees p'.1 A → Agrees p'.2 B →
          eval (toPFun A) (ofNatCode (k / 2)) ≠ toPFun B) := by
  by_cases hk : k % 2 = 0
  · obtain ⟨q, h1, h2, h3, h4, h5⟩ := step p.1 p.2 (k / 2)
    exact ⟨q, h1, h2, h3, h4, by rw [if_pos hk]; exact h5⟩
  · obtain ⟨q, h1, h2, h3, h4, h5⟩ := step p.2 p.1 (k / 2)
    exact ⟨(q.2, q.1), h2, h1, h4, h3, by
      rw [if_neg hk]
      exact fun A B hA hB => h5 B A hB hA⟩

/-- The stagewise construction. -/
noncomputable def stages : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | k + 1 => Classical.choose (stepEx (stages k) k)

theorem stages_spec (k : ℕ) :
    Ext (stages k).1 (stages (k + 1)).1 ∧ Ext (stages k).2 (stages (k + 1)).2 ∧
    (stages k).1.length < (stages (k + 1)).1.length ∧
    (stages k).2.length < (stages (k + 1)).2.length ∧
    (if k % 2 = 0 then
      ∀ A B : ℕ → Bool, Agrees (stages (k + 1)).1 A → Agrees (stages (k + 1)).2 B →
        eval (toPFun B) (ofNatCode (k / 2)) ≠ toPFun A
    else
      ∀ A B : ℕ → Bool, Agrees (stages (k + 1)).1 A → Agrees (stages (k + 1)).2 B →
        eval (toPFun A) (ofNatCode (k / 2)) ≠ toPFun B) :=
  Classical.choose_spec (stepEx (stages k) k)

theorem ext_stages_le {k l : ℕ} (h : k ≤ l) :
    Ext (stages k).1 (stages l).1 ∧ Ext (stages k).2 (stages l).2 := by
  induction l with
  | zero =>
    rw [Nat.le_zero.mp h]
    exact ⟨ext_rfl _, ext_rfl _⟩
  | succ l ihl =>
    by_cases hkl : k = l + 1
    · rw [hkl]
      exact ⟨ext_rfl _, ext_rfl _⟩
    · have hk : k ≤ l := by omega
      exact ⟨(ihl hk).1.trans (stages_spec l).1,
        (ihl hk).2.trans (stages_spec l).2.1⟩

theorem length_stages (k : ℕ) :
    k ≤ (stages k).1.length ∧ k ≤ (stages k).2.length := by
  induction k with
  | zero => simp
  | succ k ihk =>
    have h1 := (stages_spec k).2.2.1
    have h2 := (stages_spec k).2.2.2.1
    exact ⟨by omega, by omega⟩

/-- The left real: the limit of the first coordinates. -/
noncomputable def A : ℕ → Bool := fun n => (stages (n + 1)).1.getD n false

/-- The right real: the limit of the second coordinates. -/
noncomputable def B : ℕ → Bool := fun n => (stages (n + 1)).2.getD n false

theorem agreesA (k : ℕ) : Agrees (stages k).1 A := by
  intro i hi
  have h1 := (ext_stages_le (le_max_left k (i + 1))).1
  have h2 := (ext_stages_le (le_max_right k (i + 1))).1
  have hlen : i < (stages (i + 1)).1.length := by
    have := (length_stages (i + 1)).1
    omega
  show (stages (i + 1)).1.getD i false = (stages k).1.getD i false
  rw [← h2.2 i hlen, h1.2 i hi]

theorem agreesB (k : ℕ) : Agrees (stages k).2 B := by
  intro i hi
  have h1 := (ext_stages_le (le_max_left k (i + 1))).2
  have h2 := (ext_stages_le (le_max_right k (i + 1))).2
  have hlen : i < (stages (i + 1)).2.length := by
    have := (length_stages (i + 1)).2
    omega
  show (stages (i + 1)).2.getD i false = (stages k).2.getD i false
  rw [← h2.2 i hlen, h1.2 i hi]

theorem not_le_AB : ¬ A ≤ₜ B := by
  intro h
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  set k := 2 * encodeCode c with hk
  have hspec := (stages_spec k).2.2.2.2
  rw [if_pos (by omega)] at hspec
  have he : k / 2 = encodeCode c := by omega
  rw [he] at hspec
  exact hspec A B (agreesA (k + 1)) (agreesB (k + 1))
    (by rw [ofNatCode_encodeCode]; exact hc)

theorem not_le_BA : ¬ B ≤ₜ A := by
  intro h
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  set k := 2 * encodeCode c + 1 with hk
  have hspec := (stages_spec k).2.2.2.2
  rw [if_neg (by omega)] at hspec
  have he : k / 2 = encodeCode c := by omega
  rw [he] at hspec
  exact hspec A B (agreesA (k + 1)) (agreesB (k + 1))
    (by rw [ofNatCode_encodeCode]; exact hc)

/-- **The Kleene–Post theorem (1954)**: there exist Turing-incomparable
points of Cantor space. -/
theorem kleene_post : ∃ A B : ℕ → Bool, ¬ A ≤ₜ B ∧ ¬ B ≤ₜ A :=
  ⟨A, B, not_le_AB, not_le_BA⟩

end KleenePost

/-- **Incomparable Turing degrees exist** (on Mathlib's `TuringDegree`). -/
theorem TuringDegree.exists_incomparable :
    ∃ d e : TuringDegree, ¬ d ≤ e ∧ ¬ e ≤ d :=
  ⟨Quot.mk _ (Cantor.toPFun KleenePost.A), Quot.mk _ (Cantor.toPFun KleenePost.B),
    KleenePost.not_le_AB, KleenePost.not_le_BA⟩

/-- The Turing degrees are not linearly ordered. -/
theorem TuringDegree.not_isTotal_le : ¬ ∀ d e : TuringDegree, d ≤ e ∨ e ≤ d := by
  intro h
  obtain ⟨d, e, h1, h2⟩ := TuringDegree.exists_incomparable
  rcases h d e with h' | h'
  · exact h1 h'
  · exact h2 h'

#print axioms KleenePost.kleene_post
#print axioms TuringDegree.exists_incomparable
#print axioms TuringDegree.not_isTotal_le
