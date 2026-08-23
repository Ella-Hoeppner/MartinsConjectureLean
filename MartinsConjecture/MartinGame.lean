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

/-- **A player-I win in Martin's game makes `A` realize a cone of degrees.**  For `z ≥ᵀ σ`, player II
copies `z`; since I wins the resulting play, its even part `x` satisfies `x ≡ᵀ z` and `x ∈ A`. -/
theorem realizes_of_winsI_martinGame {A : Set (ℕ → Bool)} {σ : ℕ → Bool}
    (hσ : WinsI (martinGame A) σ) {z : ℕ → Bool} (hz : σ ≤ₜ z) :
    ∃ x, x ∈ A ∧ x ≡ₜ z := by
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
    exact ⟨evenPart (gamePlay σ (copyStrategy z)), h2b, heven_le, h2a⟩

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
