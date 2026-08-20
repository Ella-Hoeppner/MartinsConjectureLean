/-
**Prop 1.10 at the right abstraction: a pointed perfect tree realizes a cone.**

Martin's Lemma 2.3 produces a *pointed perfect tree*.  "Perfect" is witnessed
concretely by a **degree-preserving embedding** of Cantor space into the tree's
branches: a functional `emb : 2^ω → [T]` such that `emb z` is computable from
`z ⊕ code` and, conversely, `z` is recoverable from `emb z ⊕ code`.  (This is the
labelling homeomorphism of the perfect tree, relativized to the tree's code — the
recursion-theoretic content of perfection.)

From that embedding, **Prop 1.10** — every degree above the code is realized by a
branch — is a three-line `≤ᵀ`-calculation, needing no `RecursiveIn` plumbing:
for `d ≥ᵀ code`, the branch `emb d` satisfies `emb d ≡ᵀ d`.

This is the tractable half of what a future proof of `MartinPPT'` must supply for
the tree it builds (the other half being the determinacy game itself).  It is
proved here in full, so the remaining gap in `RawPPT.lean` is *only* the game.
-/
import MartinsConjecture.MartinTree

open scoped Computability
open Cantor

namespace Martin

/-- A **degree-preserving perfect embedding** of Cantor space into the branches
`mem` of a tree coded by `code`.  `emb z` is always a branch (`maps_to`), is
computable from `z ⊕ code` (`forward`), and lets `z` be recovered from `emb z ⊕
code` (`invert`).  This is the recursion-theoretic meaning of "the tree is
perfect", relative to its code — exactly what Martin's construction provides. -/
structure PerfectEmbedding (code : ℕ → Bool) (mem : (ℕ → Bool) → Prop) where
  /-- The labelling map `2^ω → [T]`. -/
  emb : (ℕ → Bool) → (ℕ → Bool)
  /-- Its image lands in the branches. -/
  maps_to : ∀ z, mem (emb z)
  /-- Forward computability: `emb z ≤ᵀ z ⊕ code`. -/
  forward : ∀ z, emb z ≤ₜ Cantor.join z code
  /-- Invertibility: `z ≤ᵀ emb z ⊕ code`. -/
  invert : ∀ z, z ≤ₜ Cantor.join (emb z) code

/-- **Prop 1.10.**  A pointed tree admitting a degree-preserving perfect embedding
realizes every degree above its code: for `d ≥ᵀ code`, the branch `emb d` has
`emb d ≡ᵀ d`.

Forward: `emb d ≤ᵀ d ⊕ code ≤ᵀ d` because `code ≤ᵀ d`.
Backward: `d ≤ᵀ emb d ⊕ code ≤ᵀ emb d` because `code ≤ᵀ emb d` (pointedness on the
branch `emb d`). -/
theorem realizes_of_perfectEmbedding {code : ℕ → Bool} {mem : (ℕ → Bool) → Prop}
    (hpointed : ∀ x, mem x → code ≤ₜ x) (E : PerfectEmbedding code mem) :
    ∀ d, code ≤ₜ d → ∃ x, mem x ∧ x ≡ₜ d := by
  intro d hcd
  refine ⟨E.emb d, E.maps_to d, ?_, ?_⟩
  · exact (E.forward d).trans (Cantor.join_le (Cantor.le.refl d) hcd)
  · exact (E.invert d).trans
      (Cantor.join_le (Cantor.le.refl _) (hpointed _ (E.maps_to d)))

/-- The embedding is faithful to "pointed": on a genuinely pointed tree, every
`emb z` computes the code (a sanity companion to `realizes_of_perfectEmbedding`;
immediate from `maps_to` + pointedness). -/
theorem code_le_emb {code : ℕ → Bool} {mem : (ℕ → Bool) → Prop}
    (hpointed : ∀ x, mem x → code ≤ₜ x) (E : PerfectEmbedding code mem) (z : ℕ → Bool) :
    code ≤ₜ E.emb z :=
  hpointed _ (E.maps_to z)

/-! ### Non-vacuity: the full space with the identity embedding -/

/-- The identity is a perfect embedding of `2^ω` into itself (the full tree,
`mem = fun _ => True`, computable code), witnessing that `PerfectEmbedding` is
inhabited and that `realizes_of_perfectEmbedding` fires. -/
def idPerfectEmbedding : PerfectEmbedding (fun _ => false) (fun _ => True) where
  emb := id
  maps_to := fun _ => trivial
  forward := fun z => Cantor.left_le_join z _
  invert := fun z => Cantor.left_le_join z _

/-- Sanity: via `idPerfectEmbedding`, the full space realizes every degree — the
`realizes`-style statement re-derived through the embedding machinery. -/
theorem full_realizes (d : ℕ → Bool) : ∃ x, (fun _ => True) x ∧ x ≡ₜ d :=
  realizes_of_perfectEmbedding (fun x _ => Cantor.le_of_computable (Computable.const false))
    idPerfectEmbedding d (Cantor.le_of_computable (Computable.const false))

#print axioms realizes_of_perfectEmbedding
#print axioms full_realizes

end Martin
