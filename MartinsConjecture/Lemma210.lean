/-
**Lemma 2.10 (Martin; MSS 3.5): a countable-range function is constant on a pointed perfect
subtree of any cofinal set — derived from `MartinPPT'` (Lemma 2.9).**

Lutz thesis Lemma 2.10 is the workhorse that upgrades a *cofinal* (generic) property to one
holding *uniformly on a pointed perfect tree*, for any function of **countable range**.  It is
the engine beneath the whole regressive / measure-preserving uniformization theory: Lemma 2.11
(computable uniformization of a relation `R ⊆ ≥ᵀ`) is exactly this lemma applied to
`h(x) =` the least reduction index for `x`, an ℕ-valued function of a single real.

Here we discharge it from the repo's already-isolated `MartinPPT'` (every cofinal set contains a
pointed perfect tree — Martin's Lemma 2.3/2.9, itself a theorem modulo game determinacy).  The
only extra ingredient is that for an ℕ-valued `h`, **some fiber `A ∩ {h = n}` is still cofinal**:
otherwise each fiber is bounded by a real `zₙ`, and their recursive join `⨁ₙ zₙ` (`Cantor.joinFam`)
bounds *all* of them at once, contradicting cofinality of `A`.

`cofinal_fiber` is the pigeonhole step; `lemma210_of_martinPPT'` is Lemma 2.10 proper.  This gives
the project the missing "countable-range constancy" engine flagged in `TwoUniform.lean` (for
functions of a single real; the pair-relation form, Lemma 2.11, follows by the same countable-range
idea applied to the reduction index).
-/
import MartinsConjecture.RawPPT
import MartinsConjecture.UniformFunctionals

open scoped Computability
open Cantor

namespace Martin

/-- **Pigeonhole for cofinality along an ℕ-valued function.**  If `A` is cofinal and
`h : 2^ω → ℕ`, some fiber `{x | A x ∧ h x = n}` is still cofinal.  Proof: if every fiber were
bounded (by some `zₙ`), the recursive join `⨁ₙ zₙ` would bound all of them, so no `x` above it
could lie in `A` (its value `h x` would have to escape its own fiber's bound) — contradicting
cofinality of `A`. -/
theorem cofinal_fiber (A : (ℕ → Bool) → Prop) (hA : Cofinal A) (h : (ℕ → Bool) → ℕ) :
    ∃ n, Cofinal (fun x => A x ∧ h x = n) := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ n, ¬ Cofinal (fun x => A x ∧ h x = n)`.  Turn each into an explicit bound `zₙ`.
  have hz : ∀ n, ∃ z, ∀ x, z ≤ₜ x → A x → h x ≠ n := by
    intro n
    by_contra hn
    push_neg at hn
    exact hcon n hn
  choose z hz using hz
  obtain ⟨x, hwx, hAx⟩ := hA (Cantor.joinFam z)
  exact hz (h x) x ((Cantor.component_le_joinFam z (h x)).trans hwx) hAx rfl

/-- **Lemma 2.10 (from `MartinPPT'`).**  For a cofinal `A` and any ℕ-valued `h`, there is an
`n` and a pointed perfect tree `T` all of whose branches lie in `A` and satisfy `h x = n`
(i.e. `h` is constant `= n` on `[T]`). -/
theorem lemma210_of_martinPPT' (hPPT : MartinPPT') (A : (ℕ → Bool) → Prop) (hA : Cofinal A)
    (h : (ℕ → Bool) → ℕ) :
    ∃ (n : ℕ) (T : RawPPT), ∀ x, IsBranch (treeMem T.code) x → A x ∧ h x = n := by
  obtain ⟨n, hcof⟩ := cofinal_fiber A hA h
  obtain ⟨T, hT⟩ := hPPT (fun x => A x ∧ h x = n) hcof
  exact ⟨n, T, hT⟩

/-- **Corollary (the clean form): any ℕ-valued function is constant on some pointed perfect
tree.**  The `A = ⊤` case of Lemma 2.10 — "countable range ⟹ constant on a pointed tree," the
statement used throughout the Martin-conjecture literature as a stand-in for the cone theorem on
non-invariant data. -/
theorem exists_constant_pointedTree (hPPT : MartinPPT') (h : (ℕ → Bool) → ℕ) :
    ∃ (n : ℕ) (T : RawPPT), ∀ x, IsBranch (treeMem T.code) x → h x = n := by
  obtain ⟨n, T, hT⟩ :=
    lemma210_of_martinPPT' hPPT (fun _ => True) (fun z => ⟨z, Cantor.le.refl z, trivial⟩) h
  exact ⟨n, T, fun x hx => (hT x hx).2⟩

/-- **The `{1,2}`-branch specialization.**  Any `Bool`-valued function of a single real is
constant on a pointed perfect tree.  Consequence for Question 9.3: if the branch-choice
"`u₁` or `u₂`?" in a 2-uniform collapse depended only on the real `X` (not on the pair `X, Y`),
this would fix the branch on a pointed tree and uniformize `F` there — so *pair-dependence of the
branch is the sole remaining obstacle* to `TwoUniform.partI_twoUniform_of_uniformize`'s hypothesis. -/
theorem exists_constant_pointedTree_bool (hPPT : MartinPPT') (b : (ℕ → Bool) → Bool) :
    ∃ (v : Bool) (T : RawPPT), ∀ x, IsBranch (treeMem T.code) x → b x = v := by
  obtain ⟨n, T, hT⟩ := exists_constant_pointedTree hPPT (fun x => cond (b x) 1 0)
  refine ⟨decide (n = 1), T, fun x hx => ?_⟩
  have hn : cond (b x) 1 0 = n := hT x hx
  cases hbx : b x with
  | false => simp only [hbx, cond_false] at hn; simp [hbx, ← hn]
  | true => simp only [hbx, cond_true] at hn; simp [hbx, ← hn]

#print axioms cofinal_fiber
#print axioms lemma210_of_martinPPT'
#print axioms exists_constant_pointedTree
#print axioms exists_constant_pointedTree_bool

end Martin
