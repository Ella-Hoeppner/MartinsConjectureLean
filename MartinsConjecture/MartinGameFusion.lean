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

/-- The **even-part tree** of a winning strategy `σ`, as a predicate on finite strings: `s` is a node
iff it is a prefix of some game-embedding value `emb z = evenPart(gamePlay σ (copyStrategy (z ⊕ σ)))`. -/
def evenTree (σ : ℕ → Bool) (s : List Bool) : Prop :=
  ∃ z, ∀ i, i < s.length →
    evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = s.getD i false

/-- **`MartinGameTreePackages` reduces to coding the game-embedding image by a `≡ᵀ σ` tree.**  Given a
`treeMem` code that is (i) `≡ᵀ σ`, (ii) downward-closed, and (iii) whose branches are *exactly* the
game-embedding image `{emb z}`, every requirement of `MartinGameTreePackages` follows from the
machine-checked math: pointedness (`code ≡ᵀ σ ≤ᵀ emb z`), the degree-preserving perfect embedding
(`code ≡ᵀ σ` makes `forward` hold since `emb z ≡ᵀ z ⊕ σ`), and branches-in-`A`
(`evenPart_realizes_of_winsI`).

**NB (subtlety):** the code must be `≡ᵀ σ`, *not merely* `≤ᵀ σ`.  `RawPPT.realizes` realizes *every*
degree `≥ᵀ code`, and the branches realize exactly the degrees `≥ᵀ σ`; also `PerfectEmbedding.forward`
needs `code ≥ᵀ σ`.  The even-part tree's *characteristic* is only `≤ᵀ σ` (it loses player II's moves so
does not compute `σ`), so one uses a `≡ᵀ σ` real coding the same *branch set* (e.g. by adjoining a
`σ`-encoding); this is why the hypothesis is stated on the branch set rather than as `treeMem = evenTree`.
`exists_z_of_branch` is what proves such a code's branch set equals the image, when discharging the
hypothesis. -/
theorem martinGameTreePackages_of_treeCode
    (hcode : ∀ σ : ℕ → Bool, ∃ code : ℕ → Bool, code ≡ₜ σ ∧
      (∀ s b, treeMem code (s ++ [b]) → treeMem code s) ∧
      ∀ x, IsBranch (treeMem code) x ↔
        ∃ z, ∀ i, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i) :
    MartinGameTreePackages := by
  intro A σ hσ
  obtain ⟨code, hcodeσ, hclosed, hbr⟩ := hcode σ
  refine ⟨{ code := code
            closed := hclosed
            pointed := ?_
            embedding :=
              { emb := fun z => evenPart (gamePlay σ (copyStrategy (Cantor.join z σ)))
                maps_to := fun z => (hbr _).mpr ⟨z, fun _ => rfl⟩
                forward := ?_
                invert := ?_ } }, ?_⟩
  · -- pointed
    intro x hx
    obtain ⟨z, hz⟩ := (hbr x).mp hx
    have hxeq : x = evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) := funext fun i => (hz i).symm
    have hxA := evenPart_realizes_of_winsI hσ (z := Cantor.join z σ) (Cantor.right_le_join z σ)
    rw [hxeq]
    exact hcodeσ.1.trans ((Cantor.right_le_join z σ).trans hxA.2.2)
  · -- forward
    intro z
    have hxA := evenPart_realizes_of_winsI hσ (z := Cantor.join z σ) (Cantor.right_le_join z σ)
    exact hxA.2.1.trans (Cantor.join_le (Cantor.left_le_join z code)
      (hcodeσ.2.trans (Cantor.right_le_join z code)))
  · -- invert
    intro z
    have hxA := evenPart_realizes_of_winsI hσ (z := Cantor.join z σ) (Cantor.right_le_join z σ)
    exact ((Cantor.left_le_join z σ).trans hxA.2.2).trans (Cantor.left_le_join _ code)
  · -- branches ⊆ A
    intro x hx
    obtain ⟨z, hz⟩ := (hbr x).mp hx
    have hxeq : x = evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) := funext fun i => (hz i).symm
    rw [hxeq]
    exact (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).1

/-- **The remaining computability statement** for Martin's Lemma 2.3: for every winning strategy `σ`,
the game-embedding image `{emb z}` is the branch set of a downward-closed `treeMem` tree coded by a real
`≡ᵀ σ`.  A `codeReal`-style construction: `emb_locality` gives a bounded search (a code `≤ᵀ σ` for the
even-part tree); a `σ`-encoding boosts it to `≡ᵀ σ` without changing the branches; `exists_z_of_branch`
identifies the branch set with the image.  The determinacy game and all tree mathematics are proved;
this coding is the only remaining piece. -/
def GameTreeCodable : Prop :=
  ∀ σ : ℕ → Bool, ∃ code : ℕ → Bool, code ≡ₜ σ ∧
    (∀ s b, treeMem code (s ++ [b]) → treeMem code s) ∧
    ∀ x, IsBranch (treeMem code) x ↔
      ∃ z, ∀ i, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i

/-- **`MartinPPT'` from `GameTreeCodable` plus determinacy.**  The whole determinacy game and all the
tree mathematics are machine-checked; only the coding remains. -/
theorem martinPPT'_of_gameTreeCodable (hc : GameTreeCodable)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT' :=
  martinPPT'_of_packaging (martinGameTreePackages_of_treeCode hc) hdet

/-- **Part 1 of Martin's conjecture from `GameTreeCodable`.**  Part 1 holds given: (i) `GameTreeCodable`
(the `codeReal`-style tree coding — a computability lemma, *not* open), (ii) full determinacy of the
Martin games, (iii) Turing determinacy, and (iv) `escaping ⟹ MP`.  The *only genuinely open* input is
(iv), the incomparable core; (ii),(iii) are standard AD; (i) is a machine-checkable computability
construction.  Martin's Lemma 2.3 — the last determinacy black-box — is thus down to one computability
lemma, with its entire mathematical content (the asymmetric game, `emb_locality`, `exists_z_of_branch`,
the tree-packaging reduction) machine-checked. -/
theorem partI_of_gameTreeCodable_escaping (hc : GameTreeCodable)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_packaging_escaping (martinGameTreePackages_of_treeCode hc) hdet hTD hesc

/-! ### A cleaner route: discharging `MartinPPT` directly via the abstract `PPT`

`PPT.mem` is an abstract predicate (not a `treeMem` tree), so we may take `code := σ` outright.  Then
pointedness, `realizes`, and `mem ⊆ A` are immediate from `evenPart_realizes_of_winsI`, and the **only**
remaining obligation is `PPT.recover` — recovering a branch `emb z` from a computable injective image
`g (emb z)` together with `σ`.  This bypasses the `treeMem` σ-encoding subtlety entirely: `code = σ` is
`≡ᵀ σ` by fiat, so `realizes` (degrees `≥ᵀ σ`) and pointedness hold on the nose. -/

/-- **The `recover` obligation** (Lemma 2.1) for the game embedding: for any winning `σ`, a computable
injective functional `g` on the branch set `{emb z}` recovers each branch from its image and `σ`
(`emb z ≤ᵀ g(emb z) ⊕ σ`).  A bounded-search inversion using `emb_locality` (`g(emb z') ↾ m` depends on
`z' ↾` a bound, so `z` is found by a `σ`-bounded search) — a `lemma21`-scale `RecursiveIn` statement, and
the sole remaining piece of Martin's Lemma 2.3 on this route. -/
def GameRecover : Prop :=
  ∀ (σ : ℕ → Bool) (g : (ℕ → Bool) → ℕ → Bool),
    CompFunctionalOn (fun x => ∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = x) g →
    (∀ x y, (∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = x) →
        (∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = y) → g x = g y → x = y) →
    ∀ x, (∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = x) →
      x ≤ₜ Cantor.join (g x) σ

/-- **`MartinPPT` directly from the game, modulo `recover`.**  Every cofinal set contains a pointed
perfect tree with code `σ`, branches the game-embedding image, `mem ⊆ A`, pointedness and `realizes`
all discharged from `evenPart_realizes_of_winsI`; the one hypothesis is `GameRecover`.  This avoids the
`treeMem`/σ-encoding route (`GameTreeCodable`) entirely. -/
theorem martinPPT_of_recover (hrec : GameRecover)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT := by
  intro A hcof
  obtain ⟨σ, hσ⟩ := winsI_martinGame_of_cofinal (A := A) hcof (hdet A)
  refine ⟨{ code := σ
            mem := fun x => ∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = x
            pointed := ?_
            realizes := ?_
            recover := hrec σ }, ?_⟩
  · rintro x ⟨z, rfl⟩
    exact (Cantor.right_le_join z σ).trans
      (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).2.2
  · intro d hd
    refine ⟨_, ⟨d, rfl⟩, ?_⟩
    have hz := evenPart_realizes_of_winsI hσ (z := Cantor.join d σ) (Cantor.right_le_join d σ)
    have hjoin : Cantor.join d σ ≡ₜ d :=
      ⟨Cantor.join_le (Cantor.le.refl d) hd, Cantor.left_le_join d σ⟩
    exact ⟨hz.2.1.trans hjoin.1, hjoin.2.trans hz.2.2⟩
  · rintro x ⟨z, rfl⟩
    exact (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).1

/-- **Part 1 of Martin's conjecture from `GameRecover` (the clean route).**  Part 1 holds given
`GameRecover` (the `recover` inversion — a computability lemma), full determinacy of the Martin games,
Turing determinacy, and `escaping ⟹ MP`.  Only the last is genuinely open.  This is the sharpest and
cleanest reduction: Martin's Lemma 2.3 (`MartinPPT`) is down to a single `lemma21`-scale inversion, with
its entire mathematical content (the asymmetric game, `emb_locality`, degree-realization) proved. -/
theorem partI_of_gameRecover_escaping (hrec : GameRecover)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_martinPPT_escaping (martinPPT_of_recover hrec hdet) hTD hesc

#print axioms martinPPT_perfect_of_packaging
#print axioms martinPPT'_of_packaging
#print axioms partI_of_packaging_escaping
#print axioms martinGameTreePackages_of_treeCode
#print axioms partI_of_gameTreeCodable_escaping
#print axioms martinPPT_of_recover
#print axioms partI_of_gameRecover_escaping

end Martin
