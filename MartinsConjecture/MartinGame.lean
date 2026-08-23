/-
**Martin's pointed-perfect-tree theorem — the asymmetric game and its degree-realization core.**

Martin's Lemma 2.3 (Lutz–Siskind; Marks–Slaman–Steel "Martin's conjecture, ≡_A, and countable Borel
equivalence relations", Lemma 3.5, attributed to Martin): under ZF+AD, a *cofinal* set `A ⊆ 2^ω`
contains a pointed perfect tree.  The proof uses an **asymmetric** game, not the plain membership game
of `cone_theorem`:

  Player I plays the real `x = evenPart z` (even bits), player II plays `y = oddPart z` (odd bits).
  **Player II loses unless `y ≥ᵀ x`; otherwise player I wins iff `x ≥ᵀ y` and `x ∈ A`.**

For cofinal `A`, player I beats *any* II-strategy `τ` by copying a fixed `x₀ ≥ᵀ τ` with `x₀ ∈ A`
(cofinality) — then `y ≤ᵀ x₀ ⊕ τ ≡ᵀ x₀`, so `x₀ ≥ᵀ y` and `x₀ ∈ A`, an I-win.  So II has no winning
strategy and (determinacy) player I wins.  From a player-I win, for every `z ≥ᵀ σ` the winning play
against "II copies `z`" has even part `x ≡ᵀ z` with `x ∈ A` — so `A` realizes every degree `≥ᵀ σ`.

This file formalizes the **degree-realization core** (`cofinal_realizes_cone`).  The remaining step to
`MartinPPT'` is packaging `{x : degree ≥ σ}` as a pointed perfect tree in the `treeMem` format.
Determinacy of the (non-invariant) payoff is threaded as an explicit hypothesis, never axiomatized.
-/
import MartinsConjecture.ConeTheorem
import MartinsConjecture.PerfectEmbedding
import MartinsConjecture.Konig

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- The even part of a play — player I's moves. -/
def evenPart (z : ℕ → Bool) : ℕ → Bool := fun k => z (2 * k)

/-- The odd part of a play — player II's moves. -/
def oddPart (z : ℕ → Bool) : ℕ → Bool := fun k => z (2 * k + 1)

theorem evenPart_le (z : ℕ → Bool) : evenPart z ≤ₜ z :=
  le_of_precomp (Primrec.nat_iff.mp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (fun _ => rfl)

theorem oddPart_le (z : ℕ → Bool) : oddPart z ≤ₜ z :=
  le_of_precomp (Primrec.nat_iff.mp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
    (fun _ => rfl)

/-- **Locality of the play under `copyStrategy (z ⊕ σ)`.**  The history after `n` moves depends on `z`
only below `n` — the crux behind `code ≤ᵀ σ` for the even-part tree (a *bounded* search over `z`'s
finitely many relevant bits).  Proved by induction: player II's move at odd step `m` is `(z ⊕ σ)(m/2)`,
reading `z` only at `m/4 < n`. -/
theorem histPlay_copy_join_locality (σ : ℕ → Bool) :
    ∀ (n : ℕ) (z z' : ℕ → Bool), (∀ j, j < n → z j = z' j) →
      histPlay σ (copyStrategy (Cantor.join z σ)) n
        = histPlay σ (copyStrategy (Cantor.join z' σ)) n := by
  intro n
  induction n with
  | zero => intro z z' _; rfl
  | succ n ih =>
    intro z z' hagree
    have hn := ih z z' (fun j hj => hagree j (by omega))
    rw [histPlay, histPlay, hn]
    congr 2
    by_cases hpar : n % 2 = 0
    · simp only [if_pos hpar]
    · simp only [if_neg hpar]
      congr 1
      set H := histPlay σ (copyStrategy (Cantor.join z' σ)) n with hH
      have hlenH : hlen H = n := by rw [hH]; exact hlen_histPlay σ _ n
      simp only [copyStrategy, hlenH, Cantor.join]
      by_cases hp2 : (n / 2) % 2 = 0
      · simp only [if_pos hp2]
        exact hagree (n / 2 / 2) (by omega)
      · simp only [if_neg hp2]

/-- **Locality of the game embedding.**  `emb z k = evenPart(gamePlay σ (copyStrategy (z ⊕ σ))) k`
depends on `z` only below `2k`.  This is the bounded-use property that makes the even-part tree's code
`≤ᵀ σ` (a bounded search over the finitely many relevant `z`-bits, as `codeReal_use`). -/
theorem emb_locality (σ z z' : ℕ → Bool) (k : ℕ) (h : ∀ j, j < 2 * k → z j = z' j) :
    evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) k
      = evenPart (gamePlay σ (copyStrategy (Cantor.join z' σ))) k := by
  show gamePlay σ (copyStrategy (Cantor.join z σ)) (2 * k)
      = gamePlay σ (copyStrategy (Cantor.join z' σ)) (2 * k)
  rw [gamePlay, gamePlay, if_pos (by omega), if_pos (by omega),
    histPlay_copy_join_locality σ (2 * k) z z' h]

/-- Reading a `range`-map at an in-bounds index. -/
theorem getD_range_map (z : ℕ → Bool) (n j : ℕ) (hj : j < n) :
    ((List.range n).map z).getD j false = z j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

/-- Reading a prefix of an append (in-bounds). -/
theorem getD_append_lt (p q : List Bool) (j : ℕ) (hj : j < p.length) :
    (p ++ q).getD j false = p.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- **Compactness: the even-part tree's branches are exactly the embedding's image.**  If `x` is
approximated arbitrarily well by embedding values (for every `n`, some `z` has
`emb z ↾ n = x ↾ n`), then `x` itself is an embedding value `emb z`.  This is the closedness of the
(continuous, by `emb_locality`) image of the compact space `2^ω`, proved constructively via König's
lemma on the tree of `z`-prefixes.  Together with `emb_locality` it is the full *mathematical* content
of the even-part tree; only the `treeMem` σ-computability plumbing (à la `codeReal_le`) then remains. -/
theorem exists_z_of_branch (σ x : ℕ → Bool)
    (hbr : ∀ n, ∃ z, ∀ i, i < n →
      evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i) :
    ∃ z, ∀ i, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i := by
  classical
  let S : List Bool → Prop := fun p => ∀ k, 2 * k < p.length →
    evenPart (gamePlay σ (copyStrategy (Cantor.join (fun i => p.getD i false) σ))) k = x k
  have hclosed : ∀ p b, S (p ++ [b]) → S p := by
    intro p b hp k hk
    have hk' : 2 * k < (p ++ [b]).length := by rw [List.length_append]; simp; omega
    rw [← hp k hk']
    exact emb_locality σ _ _ k (fun j hj => (getD_append_lt p [b] j (by omega)).symm)
  have h0 : Konig.HasInf S [] := by
    intro m
    obtain ⟨z, hz⟩ := hbr m
    refine ⟨(List.range m).map z, fun k hk => ?_, List.nil_prefix, by
      rw [List.length_map, List.length_range]⟩
    rw [List.length_map, List.length_range] at hk
    rw [emb_locality σ _ z k (fun j hj => getD_range_map z m j (by omega))]
    exact hz k (by omega)
  obtain ⟨y, hy⟩ := Konig.exists_branch hclosed h0
  refine ⟨y, fun k => ?_⟩
  have hlen : 2 * k < ((List.range (2 * k + 1)).map y).length := by
    rw [List.length_map, List.length_range]; omega
  rw [← hy (2 * k + 1) k hlen]
  exact emb_locality σ y _ k (fun j hj => (getD_range_map y (2 * k + 1) j (by omega)).symm)

/-- **Martin's asymmetric game payoff** for a set `A`.  Player I (even bits `x = evenPart z`) wins iff
`y ≱ᵀ x` (II failed the domination requirement) or `x ≥ᵀ y ∧ x ∈ A`. -/
def martinGame (A : Set (ℕ → Bool)) : Set (ℕ → Bool) :=
  {z | ¬ evenPart z ≤ₜ oddPart z ∨ (oddPart z ≤ₜ evenPart z ∧ evenPart z ∈ A)}

/-- **cofinal `A` ⟹ player I wins Martin's game** (given the game is determined).  For any II-strategy
`τ`, player I copies a fixed `x₀ ≥ᵀ τ` with `x₀ ∈ A` (cofinality); the play's even part is `x₀ ∈ A`
and its odd part is `≤ᵀ x₀`, an I-win.  So II has no winning strategy, and determinacy gives I a win.
This is the step the plain membership game cannot deliver. -/
theorem winsI_martinGame_of_cofinal {A : Set (ℕ → Bool)}
    (hcof : ∀ w, ∃ x, w ≤ₜ x ∧ x ∈ A) (hDet : GameDetermined (martinGame A)) :
    ∃ σ, WinsI (martinGame A) σ := by
  rcases hDet with h | ⟨τ, hτ⟩
  · exact h
  · exfalso
    obtain ⟨x₀, hτx₀, hx₀A⟩ := hcof τ
    have hle : gamePlay (copyStrategy x₀) τ ≤ₜ x₀ := by
      refine gamePlay_le 0 (copyStrategy x₀) τ τ x₀ hτx₀ (fun n hn => ?_) (fun n hn => ?_)
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega), copyStrategy, hlen_histPlay]
    have heven : evenPart (gamePlay (copyStrategy x₀) τ) = x₀ := by
      funext k
      show gamePlay (copyStrategy x₀) τ (2 * k) = x₀ k
      rw [gamePlay_copy_even τ x₀ (2 * k) (by omega)]
      congr 1; omega
    refine hτ (copyStrategy x₀) (Or.inr ⟨?_, ?_⟩)
    · rw [heven]; exact (oddPart_le _).trans hle
    · rw [heven]; exact hx₀A

/-- **The winning play's even part realizes the copied degree.**  For `z ≥ᵀ σ`, when player II copies
`z` the resulting winning play `gamePlay σ (copyStrategy z)` has even part `≡ᵀ z` and lying in `A`.
This is the value-level form (exposes the specific witness for the perfect embedding below). -/
theorem evenPart_realizes_of_winsI {A : Set (ℕ → Bool)} {σ : ℕ → Bool}
    (hσ : WinsI (martinGame A) σ) {z : ℕ → Bool} (hz : σ ≤ₜ z) :
    evenPart (gamePlay σ (copyStrategy z)) ∈ A ∧ evenPart (gamePlay σ (copyStrategy z)) ≡ₜ z := by
  have hle : gamePlay σ (copyStrategy z) ≤ₜ z := by
    refine gamePlay_le 1 σ (copyStrategy z) σ z hz (fun n hn => ?_) (fun n hn => ?_)
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), copyStrategy, hlen_histPlay]
  have hodd : oddPart (gamePlay σ (copyStrategy z)) = z := by
    funext k
    show gamePlay σ (copyStrategy z) (2 * k + 1) = z k
    rw [gamePlay_copy_odd σ z (2 * k + 1) (by omega)]
    congr 1; omega
  have heven_le : evenPart (gamePlay σ (copyStrategy z)) ≤ₜ z := (evenPart_le _).trans hle
  rcases hσ (copyStrategy z) with h1 | ⟨h2a, h2b⟩
  · exfalso
    apply h1
    rw [hodd]; exact heven_le
  · rw [hodd] at h2a
    exact ⟨h2b, heven_le, h2a⟩

/-- **A player-I win in Martin's game makes `A` realize a cone of degrees.**  For `z ≥ᵀ σ`, some member
of `A` is `≡ᵀ z` (the winning play's even part). -/
theorem realizes_of_winsI_martinGame {A : Set (ℕ → Bool)} {σ : ℕ → Bool}
    (hσ : WinsI (martinGame A) σ) {z : ℕ → Bool} (hz : σ ≤ₜ z) :
    ∃ x, x ∈ A ∧ x ≡ₜ z :=
  ⟨_, evenPart_realizes_of_winsI hσ hz⟩

/-- **The determinacy game supplies the pointed perfect embedding into `A`** — the "game half" that
`PerfectEmbedding.lean` left open (it proved the other half, that such an embedding realizes a cone).
From a player-I win, `z ↦ evenPart(play against II copying z ⊕ σ)` is a degree-preserving perfect
embedding with code `σ`, whose branches lie in `A` and above `σ`.  Its three defining computations are
exactly `evenPart_realizes_of_winsI` at `z ⊕ σ` together with the join inequalities. -/
def martinGamePerfectEmbedding {A : Set (ℕ → Bool)} {σ : ℕ → Bool}
    (hσ : WinsI (martinGame A) σ) :
    PerfectEmbedding σ (fun x => x ∈ A ∧ σ ≤ₜ x) where
  emb z := evenPart (gamePlay σ (copyStrategy (Cantor.join z σ)))
  maps_to z :=
    ⟨(evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).1,
     (Cantor.right_le_join z σ).trans (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).2.2⟩
  forward z := (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).2.1
  invert z :=
    ((Cantor.left_le_join z σ).trans (evenPart_realizes_of_winsI hσ (Cantor.right_le_join z σ)).2.2).trans
      (Cantor.left_le_join _ σ)

/-- **Martin's Lemma 2.3, at the perfect-embedding level.**  A cofinal set `A` (whose Martin game is
determined) admits a code `σ` and a degree-preserving perfect embedding of Cantor space whose branches
lie in `A` and above `σ` — i.e. `A` contains a pointed perfect set.  Combined with
`realizes_of_perfectEmbedding` this recovers `cofinal_realizes_cone`; the only remaining step to
`MartinPPT'` is re-presenting this pointed perfect set as a tree in the `treeMem` format. -/
theorem cofinal_perfectEmbedding {A : Set (ℕ → Bool)}
    (hcof : ∀ w, ∃ x, w ≤ₜ x ∧ x ∈ A) (hDet : GameDetermined (martinGame A)) :
    ∃ σ, Nonempty (PerfectEmbedding σ (fun x => x ∈ A ∧ σ ≤ₜ x)) := by
  obtain ⟨σ, hσ⟩ := winsI_martinGame_of_cofinal hcof hDet
  exact ⟨σ, ⟨martinGamePerfectEmbedding hσ⟩⟩

/-- **Martin's theorem, degree-realization core** (Lemma 2.3, via the asymmetric game).  A cofinal set
`A` realizes a whole cone of degrees: given its Martin game is determined, there is a `σ` so that every
degree `≥ᵀ σ` has a representative in `A`.  This is the recursion-theoretic heart of Martin's pointed
perfect tree theorem; the remaining step to `MartinPPT'` is packaging the realized representatives as a
pointed perfect tree in the `treeMem` format. -/
theorem cofinal_realizes_cone {A : Set (ℕ → Bool)}
    (hcof : ∀ w, ∃ x, w ≤ₜ x ∧ x ∈ A) (hDet : GameDetermined (martinGame A)) :
    ∃ σ, ∀ z, σ ≤ₜ z → ∃ x, x ∈ A ∧ x ≡ₜ z := by
  obtain ⟨σ, hσ⟩ := winsI_martinGame_of_cofinal hcof hDet
  exact ⟨σ, fun z hz => realizes_of_winsI_martinGame hσ hz⟩

#print axioms winsI_martinGame_of_cofinal
#print axioms realizes_of_winsI_martinGame
#print axioms cofinal_realizes_cone

end Martin
