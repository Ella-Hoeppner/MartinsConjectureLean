/-
Degree theory on Cantor space.

Points of Cantor space `2^ω` are represented as `X : ℕ → Bool`; they embed
into oracles via `Cantor.toPFun` (total 0/1-valued partial functions), which
induces Turing reducibility `≤ₜ`, equivalence `≡ₜ`, and the jump on points.

Main results:
* `Cantor.lt_jump : X <ₜ Cantor.jump X` — jump strictness on Cantor space.
* `Cantor.le_bot_iff` — the bottom degree consists exactly of the computable
  points (sanity anchor: the reducibility is not vacuous).
-/
import MartinsConjecture.Jump

open scoped Computability
open OracleCode

attribute [local instance] Classical.propDecidable

namespace Cantor

/-- Embed a point of Cantor space as a (total, 0/1-valued) oracle. -/
def toPFun (X : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (cond (X n) 1 0)

/-- Turing reducibility between points of Cantor space. -/
def le (X Y : ℕ → Bool) : Prop := toPFun X ≤ᵀ toPFun Y

@[inherit_doc] scoped infix:50 " ≤ₜ " => Cantor.le

/-- Turing equivalence between points of Cantor space. -/
def equiv (X Y : ℕ → Bool) : Prop := X ≤ₜ Y ∧ Y ≤ₜ X

@[inherit_doc] scoped infix:50 " ≡ₜ " => Cantor.equiv

/-- Strict Turing reducibility between points of Cantor space. -/
def lt (X Y : ℕ → Bool) : Prop := X ≤ₜ Y ∧ ¬ Y ≤ₜ X

@[inherit_doc] scoped infix:50 " <ₜ " => Cantor.lt

protected theorem le.refl (X : ℕ → Bool) : X ≤ₜ X := TuringReducible.refl _

protected theorem le.trans {X Y Z : ℕ → Bool} (h1 : X ≤ₜ Y) (h2 : Y ≤ₜ Z) : X ≤ₜ Z :=
  TuringReducible.trans h1 h2

protected theorem equiv.refl (X : ℕ → Bool) : X ≡ₜ X := ⟨le.refl X, le.refl X⟩

protected theorem equiv.symm {X Y : ℕ → Bool} (h : X ≡ₜ Y) : Y ≡ₜ X := ⟨h.2, h.1⟩

protected theorem equiv.trans {X Y Z : ℕ → Bool} (h1 : X ≡ₜ Y) (h2 : Y ≡ₜ Z) : X ≡ₜ Z :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- The Turing jump of a point of Cantor space, as a point of Cantor space. -/
noncomputable def jump (X : ℕ → Bool) : ℕ → Bool :=
  fun e => decide (jumpP (toPFun X) e)

theorem toPFun_jump (X : ℕ → Bool) : toPFun (jump X) = jumpFn (toPFun X) := by
  funext e
  by_cases h : jumpP (toPFun X) e <;> simp [toPFun, jump, jumpFn, h]

theorem le_jump (X : ℕ → Bool) : X ≤ₜ jump X := by
  unfold le
  rw [toPFun_jump]
  exact turingReducible_jumpFn _

theorem not_jump_le (X : ℕ → Bool) : ¬ jump X ≤ₜ X := by
  unfold le
  rw [toPFun_jump]
  exact jumpFn_not_turingReducible _

/-- **Jump strictness on Cantor space.** -/
theorem lt_jump (X : ℕ → Bool) : X <ₜ jump X := ⟨le_jump X, not_jump_le X⟩

/-! ### The bottom degree: sanity anchors -/

theorem toPFun_const_false : toPFun (fun _ => false) = fun _ => Part.some 0 := by
  funext n
  simp [toPFun]

/-- A point is below the constantly-`false` point iff its characteristic
function is partial recursive: the bottom degree consists exactly of the
computable points. -/
theorem le_bot_iff {X : ℕ → Bool} : X ≤ₜ (fun _ => false) ↔ Partrec (toPFun X) := by
  constructor
  · intro h
    unfold le at h
    rw [toPFun_const_false] at h
    exact TuringReducible.partrec_of_const h
  · intro h
    exact h.turingReducible

/-- Computable points are in the bottom degree. -/
theorem le_of_computable {X Y : ℕ → Bool} (h : Computable X) : X ≤ₜ Y := by
  have h1 : Computable fun n => (cond (X n) 1 0 : ℕ) :=
    Computable.cond h (Computable.const 1) (Computable.const 0)
  exact Partrec.turingReducible h1.partrec

/-- The jump of any point is strictly above every computable point;
in particular `∅′` is not computable. -/
theorem not_computable_jump (X : ℕ → Bool) : ¬ Computable (jump X) := by
  intro h
  exact not_jump_le X (le_of_computable h)

end Cantor
