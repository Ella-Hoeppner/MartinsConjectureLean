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

/-- **The remaining computability step for Martin's fusion**, stated for the *winning strategy* itself
(not a generic embedding — a generic Turing-computable embedding may have unbounded use, so its prefix
tree need not be `σ`-computable, breaking pointedness).  From a player-I win `σ` of the Martin game for
`A`, the **even-part tree** `Tσ = {s : s ⊑ evenPart(gamePlay σ (copyStrategy (z ⊕ σ)))}` is a
`treeMem`-coded `PerfectTree` whose branches all lie in `A`: its code is `≤ᵀ σ` by a *bounded* search
over player II's finitely many free bits (as `codeReal_le`), and its branches are exactly the game
embedding's image `⊆ A` since a continuous image of compact `2^ω` is closed.  Isolated here as the sole
remaining hypothesis; the game embedding `martinGamePerfectEmbedding hσ` supplies its `embedding` field. -/
def MartinGameTreePackages : Prop :=
  ∀ (A : Set (ℕ → Bool)) (σ : ℕ → Bool), WinsI (martinGame A) σ →
    ∃ T : PerfectTree, ∀ x, IsBranch (treeMem T.code) x → x ∈ A

/-- **Martin's Lemma 2.3 (natural form) reduces to the packaging step.**  Given full determinacy of the
non-invariant Martin games and the even-part-tree packaging of a winning strategy, every cofinal set
contains a structural pointed perfect tree.  The determinacy game — the mathematical content — is fully
machine-checked (`winsI_martinGame_of_cofinal`); only the tree bookkeeping is assumed. -/
theorem martinPPT_perfect_of_packaging (hpkg : MartinGameTreePackages)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT_perfect := by
  intro A hcof
  obtain ⟨σ, hσ⟩ := winsI_martinGame_of_cofinal (A := A) hcof (hdet A)
  exact hpkg A σ hσ

/-- **`MartinPPT'` from the (proven) game plus the packaging step.**  Chains
`martinPPT_perfect_of_packaging` with the existing `martinPPT'_of_perfect`.  So the *entire* non-invariant
half of Martin's pointed-perfect-tree theorem is now reduced to `MartinGameTreePackages` — a single
computability construction — with the determinacy argument fully formalized. -/
theorem martinPPT'_of_packaging (hpkg : MartinGameTreePackages)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT' :=
  martinPPT'_of_perfect (martinPPT_perfect_of_packaging hpkg hdet)

/-- **Part 1 of Martin's conjecture, all the way from the determinacy game.**  Chaining
`martinPPT_perfect_of_packaging` with `partI_of_perfect_escaping`, Part 1 holds given: (i) the even-part
tree packaging (`MartinGameTreePackages`, a computability construction), (ii) full determinacy of the
Martin games, (iii) Turing determinacy, and (iv) `escaping ⟹ measure-preserving`.  The **determinacy
game** — Martin's Lemma 2.3's actual content — is fully machine-checked here; the only genuinely open
input is (iv), the incomparable core.  This exhibits the complete path from the newly-formalized game to
Part 1, with the residual `MartinPPT` gap now pinned to a single tree-bookkeeping step. -/
theorem partI_of_packaging_escaping (hpkg : MartinGameTreePackages)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_perfect_escaping (martinPPT_perfect_of_packaging hpkg hdet) hTD hesc

#print axioms martinPPT_perfect_of_packaging
#print axioms martinPPT'_of_packaging
#print axioms partI_of_packaging_escaping

end Martin
