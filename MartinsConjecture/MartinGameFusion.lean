/-
**The non-invariant Martin fusion, reduced to a single computability-packaging step.**

`MartinGame.lean` proves the mathematical heart of Martin's Lemma 2.3 (the pointed-perfect-tree theorem)
for a *non-invariant* cofinal set: the asymmetric determinacy game, that a cofinal set makes player I
win it (`winsI_martinGame_of_cofinal`), and that a player-I win yields a degree-preserving
`PerfectEmbedding` of Cantor space into `A` with code `σ` (`martinGamePerfectEmbedding`).

`RawPPT.lean` already turns a `treeMem`-coded `PerfectTree` (a downward-closed tree with such an
embedding into *its own branches*) into a `RawPPT`, hence `MartinPPT'`, hence — via the rest of the
development — everything (`martinPPT'_of_perfect`, `partI_of_perfect_escaping`).

The *only* gap between the two is re-presenting the game's abstract perfect embedding into `A` as a
concrete `treeMem` tree.  That gap is the **even-part tree** `Tσ = {s : s ⊑ emb z for some z}`; it is a
genuine `treeMem` tree because (i) its code is `≤ᵀ σ` by a *bounded* search over player II's finitely
many free bits (as for `codeReal`), and (ii) its branches are exactly `{emb z} ⊆ A` since a continuous
image of the compact space `2^ω` is closed.  Building that tree is a `coneRawPPT`-scale computability
construction; here we isolate it as the single hypothesis `PerfectEmbeddingPackages`, and prove that it
is the *whole* remaining content: with it (and determinacy of the games), `MartinPPT'` follows.
-/
import MartinsConjecture.MartinGame
import MartinsConjecture.RawPPT

open scoped Computability
open Cantor

namespace Martin

/-- **The remaining computability step for Martin's fusion.**  Any degree-preserving perfect embedding
into `A` with code `σ` (the pointedness `σ ≤ᵀ x` built into the membership predicate) re-presents as a
`treeMem`-coded `PerfectTree` whose branches all lie in `A`.  This is the even-part-tree construction —
a pure tree/computability step, the determinacy content having already been discharged. -/
def PerfectEmbeddingPackages : Prop :=
  ∀ (A : Set (ℕ → Bool)) (σ : ℕ → Bool),
    PerfectEmbedding σ (fun x => x ∈ A ∧ σ ≤ₜ x) →
      ∃ T : PerfectTree, ∀ x, IsBranch (treeMem T.code) x → x ∈ A

/-- **Martin's Lemma 2.3 (natural form) reduces to the packaging step.**  Given full determinacy of the
non-invariant Martin games and the `treeMem` packaging of the game embedding, every cofinal set contains
a structural pointed perfect tree.  The determinacy game — the mathematical content — is fully
machine-checked (`winsI_martinGame_of_cofinal`, `martinGamePerfectEmbedding`); only the tree bookkeeping
is assumed. -/
theorem martinPPT_perfect_of_packaging (hpkg : PerfectEmbeddingPackages)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT_perfect := by
  intro A hcof
  obtain ⟨σ, hσ⟩ := winsI_martinGame_of_cofinal (A := A) hcof (hdet A)
  exact hpkg A σ (martinGamePerfectEmbedding hσ)

/-- **`MartinPPT'` from the (proven) game plus the packaging step.**  Chains
`martinPPT_perfect_of_packaging` with the existing `martinPPT'_of_perfect`.  So the *entire* non-invariant
half of Martin's pointed-perfect-tree theorem is now reduced to `PerfectEmbeddingPackages` — a single
computability construction — with the determinacy argument fully formalized. -/
theorem martinPPT'_of_packaging (hpkg : PerfectEmbeddingPackages)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT' :=
  martinPPT'_of_perfect (martinPPT_perfect_of_packaging hpkg hdet)

#print axioms martinPPT_perfect_of_packaging
#print axioms martinPPT'_of_packaging

end Martin
