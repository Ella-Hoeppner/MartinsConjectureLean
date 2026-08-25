/-
**The `BnAm` sub-case leaks into Part 2 (transfinite rank).**

Recall the four-way jump-distance decomposition of the incomparable core (`IncomparableArithReduction`).
The `BnAm` sub-case is `X ≤ᵀ (F X)^(k)` (arithmetically increasing, `Bn`) together with `F X ≰ᵀ X^(m)`
for every finite `m` (`Am`, i.e. `F X ≰ₐ X`).  Consider the derived function `G X := jump^[k] (F X)`.  It is Turing-invariant
(`jumpIter_comp_invariant`) and, on the `Bn` cone, *above identity* (`X ≤ᵀ (F X)^(k) = G X`) — so Part 2
of Martin's Conjecture assigns it a rank in the jump hierarchy.

The result below shows that rank cannot be *finite*: if `G ≡ᵀ jump^[j]` on a cone for some finite `j`, then
`F X ≤ᵀ (F X)^(k) ≡ᵀ X^(j)`, i.e. `F X ≤ₐ X`, contradicting `Am`.  Hence `BnAm` forces `jump^[k]∘F` to be
a *transfinite*-rank above-identity function — a genuinely Part-2 object.  This is the precise sense in
which `BnAm` is not "native" to the incomparable core: it can only survive by exhibiting the kind of
non-finite-rank increasing function that Part 2 is about (and whose existence, off the uniform class, is
itself open).  Together with `ArithRegressiveSkeleton` (which routes `AnBm` through relativized
Slaman–Steel), this leaves the transfinite residue (`BnBm`/`AnAm`) as the genuine open heart.
-/
import MartinsConjecture.IncomparableArithReduction

open scoped Computability
open Cantor

namespace Martin

/-- `A ≤ᵀ jump^[k] A`: every set is below each of its finite jumps. -/
theorem self_le_jumpIter (A : ℕ → Bool) : ∀ k, A ≤ₜ Cantor.jump^[k] A
  | 0 => Cantor.le.refl A
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact (self_le_jumpIter A k).trans (Cantor.le_jump _)

/-- **`BnAm` forces infinite Part-2 rank.**  Under the `Am` hypothesis (`F X ≰ᵀ X^(m)` for all finite
`m`, on a cone — i.e. `F X ≰ₐ X`), the invariant above-identity function `X ↦ jump^[k] (F X)` is `≡ᵀ`
*no* finite jump `jump^[j]` on any cone: such an equivalence would give `F X ≤ᵀ (F X)^(k) ≡ᵀ X^(j)`,
contradicting `Am` at `m = j`.  So the `BnAm` sub-case leaks into Part 2 — it requires a transfinite-rank
increasing function.  (Only `Am` is used, so this equally covers the `AnAm` face, which also has `Am`.) -/
theorem bnAm_jumpComp_not_finite_jump {F : (ℕ → Bool) → ℕ → Bool} (k : ℕ)
    (hAm : OnCone (fun X => ∀ m, ¬ F X ≤ₜ Cantor.jump^[m] X)) :
    ¬ ∃ j, OnCone (fun X => Cantor.jump^[k] (F X) ≡ₜ Cantor.jump^[j] X) := by
  rintro ⟨j, hEq⟩
  obtain ⟨B, hB⟩ := onCone_and hAm hEq
  have hBB := hB B (Cantor.le.refl B)
  exact hBB.1 j ((self_le_jumpIter (F B) k).trans hBB.2.1)

/-- `jump^[k]` is monotone in `≤ᵀ`. -/
theorem jumpIter_mono {A B : ℕ → Bool} (h : A ≤ₜ B) :
    ∀ k, Cantor.jump^[k] A ≤ₜ Cantor.jump^[k] B
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Cantor.jump_mono (jumpIter_mono h k)

/-- **`BnBm` keeps `jump^[k]∘F` at FINITE Part-2 rank** — the exact contrast with `BnAm`.  On the `BnBm`
cone (`X ≤ᵀ (F X)^(k)` from `Bn`, and `F X ≤ᵀ X^(m)` from `Bm` — the *negation* of `Am`), the invariant
above-identity function `G X := jump^[k](F X)` is bounded by a fixed finite jump: `X ≤ᵀ G X ≤ᵀ X^(k+m)`.
So `G` has finite Part-2 rank on `BnBm`, whereas `bnAm_jumpComp_not_finite_jump` shows it has infinite
rank whenever `Am` holds (`BnAm` and `AnAm`).  The `Am`/`Bm` split — `F X ≰ₐ X` versus `F X ≤ₐ X`, the
sole difference between `BnAm` and `BnBm` — is *exactly* the infinite/finite Part-2-rank split of
`jump^[k]∘F`. -/
theorem bnBm_jumpComp_finite_bounded {F : (ℕ → Bool) → ℕ → Bool} (k m : ℕ)
    (hBn : OnCone (fun X => X ≤ₜ Cantor.jump^[k] (F X)))
    (hBm : OnCone (fun X => F X ≤ₜ Cantor.jump^[m] X)) :
    OnCone (fun X => X ≤ₜ Cantor.jump^[k] (F X) ∧
      Cantor.jump^[k] (F X) ≤ₜ Cantor.jump^[k + m] X) := by
  obtain ⟨B, hB⟩ := onCone_and hBn hBm
  refine ⟨B, fun X hX => ⟨(hB X hX).1, ?_⟩⟩
  have hmono : Cantor.jump^[k] (F X) ≤ₜ Cantor.jump^[k] (Cantor.jump^[m] X) :=
    jumpIter_mono (hB X hX).2 k
  rwa [← Function.iterate_add_apply] at hmono

/-- **Both `Am`-faces (`BnAm` and `AnAm`) leak to Part 2 via the graph.**  Whenever `F X ≰ₐ X` on a cone
(`Am` — the shared component of `BnAm` and `AnAm`), the *graph* `X ↦ X ⊕ F X` is an invariant above-identity
function (`X ≤ᵀ X ⊕ F X` always) whose Part-2 rank is not finite: `jump^[k](X ⊕ F X) ≡ᵀ jump^[j] X` on a
cone would force `F X ≤ᵀ X ⊕ F X ≤ᵀ (X ⊕ F X)^(k) ≡ᵀ X^(j)`, contradicting `Am`.  Unlike `jump^[k]∘F`
(above-id only on the `Bn` cone), the graph is *unconditionally* above-id, so this exhibits a genuine
transfinite-rank Part-2 object for the whole `Am` region — the two "arithmetically-non-regressive"
incomparable faces are Part-2 phenomena in disguise. -/
theorem am_graph_not_finite_jump {F : (ℕ → Bool) → ℕ → Bool} (k : ℕ)
    (hAm : OnCone (fun X => ∀ m, ¬ F X ≤ₜ Cantor.jump^[m] X)) :
    ¬ ∃ j, OnCone (fun X => Cantor.jump^[k] (Cantor.join X (F X)) ≡ₜ Cantor.jump^[j] X) := by
  apply bnAm_jumpComp_not_finite_jump (F := fun X => Cantor.join X (F X)) k
  obtain ⟨B, hB⟩ := hAm
  exact ⟨B, fun X hX m hle => hB X hX m ((Cantor.right_le_join X (F X)).trans hle)⟩

#print axioms self_le_jumpIter
#print axioms bnAm_jumpComp_not_finite_jump
#print axioms bnBm_jumpComp_finite_bounded
#print axioms am_graph_not_finite_jump

end Martin
