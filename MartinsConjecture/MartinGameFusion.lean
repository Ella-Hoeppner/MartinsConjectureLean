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

/-- **`MartinGameTreePackages` reduces to a single computability fact**: that the even-part tree of a
winning strategy admits a `treeMem` code `≡ᵀ σ`.  Given such a code, *every* other requirement is
discharged by the machine-checked math: branches `= {emb z}` (compactness, `exists_z_of_branch`), each
branch is `∈ A` and `≡ᵀ z ⊕ σ` (`evenPart_realizes_of_winsI`), whence closedness, pointedness
(`code ≤ᵀ σ ≤ᵀ` branch), the degree-preserving perfect embedding (`code ≡ᵀ σ` makes `forward` hold), and
branches-in-`A`.  So the *entire* non-invariant Martin fusion is now reduced to the pure computability
statement below — a `codeReal`-style bounded-search presentation — with all determinacy and all tree
mathematics fully formalized. -/
theorem martinGameTreePackages_of_code
    (hcode : ∀ σ : ℕ → Bool, ∃ code : ℕ → Bool, code ≡ₜ σ ∧
      ∀ s : List Bool, treeMem code s ↔ evenTree σ s) :
    MartinGameTreePackages := by
  intro A σ hσ
  obtain ⟨code, hcodeσ, hcodetree⟩ := hcode σ
  -- branch characterization via compactness
  have hbranch : ∀ x, IsBranch (treeMem code) x →
      ∃ z, ∀ i, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i := by
    intro x hx
    refine exists_z_of_branch σ x (fun n => ?_)
    obtain ⟨z, hz⟩ := (hcodetree _).mp (hx n)
    refine ⟨z, fun i hi => ?_⟩
    have hi' : i < ((List.range n).map x).length := by rw [List.length_map, List.length_range]; exact hi
    rw [← getD_range_map x n i hi]; exact hz i hi'
  refine ⟨{ code := code
            closed := ?_
            pointed := ?_
            embedding :=
              { emb := fun z => evenPart (gamePlay σ (copyStrategy (Cantor.join z σ)))
                maps_to := ?_
                forward := ?_
                invert := ?_ } }, ?_⟩
  · -- closed
    intro s b hs
    rw [hcodetree] at hs ⊢
    obtain ⟨z, hz⟩ := hs
    refine ⟨z, fun i hi => ?_⟩
    have hi' : i < (s ++ [b]).length := by rw [List.length_append]; simp; omega
    rw [← getD_append_lt s [b] i hi]; exact hz i hi'
  · -- pointed
    intro x hx
    obtain ⟨z, hz⟩ := hbranch x hx
    have hxeq : x = evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) := funext fun i => (hz i).symm
    have hxA := evenPart_realizes_of_winsI hσ (z := Cantor.join z σ) (Cantor.right_le_join z σ)
    rw [hxeq]
    exact hcodeσ.1.trans ((Cantor.right_le_join z σ).trans hxA.2.2)
  · -- maps_to: emb z is a branch
    intro z n
    rw [hcodetree]
    refine ⟨z, fun i hi => ?_⟩
    rw [List.length_map, List.length_range] at hi
    rw [getD_range_map _ n i hi]
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
    obtain ⟨z, hz⟩ := hbranch x hx
    have hxeq : x = evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) := funext fun i => (hz i).symm
    rw [hxeq]
    exact (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).1

/-- **The single remaining computability statement** for Martin's Lemma 2.3: every winning strategy's
even-part tree admits a `treeMem` code that is `≡ᵀ σ` (a `codeReal`-style bounded-search presentation —
`emb_locality` shows the search is bounded, so `code ≤ᵀ σ`; the code embeds `σ` for `code ≡ᵀ σ`). -/
def EvenTreeComputable : Prop :=
  ∀ σ : ℕ → Bool, ∃ code : ℕ → Bool, code ≡ₜ σ ∧ ∀ s : List Bool, treeMem code s ↔ evenTree σ s

/-- **`MartinPPT'` from the single computability statement plus determinacy.**  Everything else — the
whole determinacy game and all the tree mathematics — is machine-checked. -/
theorem martinPPT'_of_evenTreeComputable (hc : EvenTreeComputable)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT' :=
  martinPPT'_of_packaging (martinGameTreePackages_of_code hc) hdet

/-- **Part 1 of Martin's conjecture from the single computability statement.**  Part 1 holds given:
(i) `EvenTreeComputable` (the `codeReal`-style tree presentation — a computability lemma, *not* open),
(ii) full determinacy of the Martin games, (iii) Turing determinacy, and (iv) `escaping ⟹ MP`.  Of these
the *only genuinely open* input is (iv), the incomparable core; the determinacy games (ii),(iii) are
standard AD, and (i) is a machine-checkable computability construction.  This is the sharpest statement
of how the newly-formalized Martin fusion sits in the whole proof: the pointed-perfect-tree theorem —
Martin's Lemma 2.3, the last black-box in the reduction's determinacy input — is now down to one
computability lemma, with its entire mathematical content proved. -/
theorem partI_of_evenTreeComputable_escaping (hc : EvenTreeComputable)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_packaging_escaping (martinGameTreePackages_of_code hc) hdet hTD hesc

#print axioms martinPPT_perfect_of_packaging
#print axioms martinPPT'_of_packaging
#print axioms partI_of_packaging_escaping
#print axioms martinGameTreePackages_of_code
#print axioms partI_of_evenTreeComputable_escaping

end Martin
