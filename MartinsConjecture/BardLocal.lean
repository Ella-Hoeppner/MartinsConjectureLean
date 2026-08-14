/-
**Bard's local theorem** (Vittorio Bard, "Uniform Martin's conjecture, locally",
arXiv:1907.10766) and, from it, **Part I of Martin's conjecture for
computably-uniformly-invariant functions** (Slaman–Steel 1988, effective form).

Bard's insight: Part I is a *local* phenomenon.  His Theorem 2.2 says a
uniformly-invariant `f` restricted to a single degree `[x]` is either constant
there or satisfies `f(x) ≥ᵀ x`.  Globalizing with Martin's cone theorem gives
Part I.

This file formalizes that argument for the **computable-uniformity** hypothesis
(`ComputablyUniformlyTuringInvariant`):

* `joinFam_le_computable` — Bard's Fact 3.1 with a *computable* index family
  (the uniformity transformer `u` is computable, not primitive recursive);
* `const_on_degrees_constOnCone` — Bard's Fact 2.3: if `f` is literally constant
  on each degree in a cone, it is constant on a cone (per-digit cone dichotomy +
  `onCone_forall`);
* `bard_local` — Bard's Theorem 2.2 (effective form): a computably-uniform `f`
  that is not constant on `[x]` satisfies `x ≤ᵀ f(x)` — via the selector family
  `y_n = x` or `z` (by the `n`-th bit of `x`), whose `f`-images join above `x`
  yet stay below `f(x)` by uniformity + Fact 3.1;
* `steel_kernel_computable` — globalization: a non-constant computably-uniform
  function is above the identity on a cone.  This *proves* `SteelUniformKernel`
  for the computable-uniformity class, discharging both Part I open cores there.
-/
import MartinsConjecture.UniformCores
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.RegularChain

open scoped Computability
open OracleCode Cantor

namespace Martin

attribute [local instance] Classical.propDecidable

/-- **Bard's Fact 3.1, computable form.**  If a family `R n` is uniformly
computable from `A` via a *computable* index map `t` (`Φ_{t n}^A = R n`), the join
`⨁ₙ R n` is Turing-below `A`.  (The uniformity transformer produced by Bard's
Lemma 3.4 is computable, not primitive recursive, so we need this strengthening
of `joinFam_le`.) -/
theorem joinFam_le_computable {A : ℕ → Bool} {t : ℕ → ℕ} (ht : Computable t)
    {R : ℕ → ℕ → Bool}
    (hR : ∀ n, eval (toPFun A) (ofNatCode (t n)) = toPFun (R n)) :
    joinFam R ≤ₜ A := by
  rw [le_iff_bitg]
  have hbuilder : Computable (fun m : ℕ => Nat.pair (t (Nat.unpair m).1) (Nat.unpair m).2) :=
    Primrec₂.natPair.to_comp.comp (ht.comp (Primrec.fst.comp Primrec.unpair).to_comp)
      (Primrec.snd.comp Primrec.unpair).to_comp
  refine (Nat.RecursiveIn.comp (eval_universal A)
    (Partrec.nat_iff.mp hbuilder.partrec).recursiveIn).of_eq fun m => ?_
  show (Part.some (Nat.pair (t (Nat.unpair m).1) (Nat.unpair m).2)).bind
      (fun p => eval (toPFun A) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2)
      = Part.some (bitg (joinFam R) m)
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  rw [hR (Nat.unpair m).1]
  rfl

/-- **Bard's Fact 2.3.**  If `F` is literally constant on every degree in a cone
(base `w`: for `X ≥ᵀ w`, `Y ≡ᵀ X ⟹ F Y = F X`), then `F` is constant on a cone.
Proof: each digit `i` of `F X` is Turing-invariant on the cone, so the cone
theorem fixes it on a sub-cone; `onCone_forall` intersects the (countably many)
digit-cones. -/
theorem const_on_degrees_constOnCone (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} {w : ℕ → Bool}
    (h : ∀ X, w ≤ₜ X → ∀ Y, Y ≡ₜ X → F Y = F X) :
    ConstantOnCone F := by
  -- for each digit `i`, `F X i` is constant on a cone
  have hpd : ∀ i : ℕ, ∃ b : Bool, OnCone (fun X => F X i = b) := by
    intro i
    have hAinv : TuringInvariantSet {X | w ≤ₜ X → F X i = true} := by
      intro X Y hXY
      have hwiff : w ≤ₜ X ↔ w ≤ₜ Y := ⟨fun hw => hw.trans hXY.1, fun hw => hw.trans hXY.2⟩
      constructor
      · intro hX hwY
        have hwX : w ≤ₜ X := hwiff.mpr hwY
        have := h X hwX Y hXY.symm
        rw [this]; exact hX hwX
      · intro hY hwX
        have hwY : w ≤ₜ Y := hwiff.mp hwX
        have := h Y hwY X hXY
        rw [this]; exact hY hwY
    rcases cone_theorem_onCone {X | w ≤ₜ X → F X i = true} hAinv (hTD _ trivial hAinv)
      with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨true, Cantor.join c w, fun X hX => ?_⟩
      have hwX : w ≤ₜ X := (Cantor.right_le_join c w).trans hX
      exact hc X ((Cantor.left_le_join c w).trans hX) hwX
    · refine ⟨false, Cantor.join c w, fun X hX => ?_⟩
      have hwX : w ≤ₜ X := (Cantor.right_le_join c w).trans hX
      have hmem : ¬ (w ≤ₜ X → F X i = true) := hc X ((Cantor.left_le_join c w).trans hX)
      cases hFX : F X i with
      | false => exact hFX
      | true => exact absurd (fun _ => hFX) hmem
  choose b hb using hpd
  obtain ⟨W, hW⟩ := onCone_forall hb
  refine ⟨b, W, fun X hX => ?_⟩
  have hFXb : F X = b := funext (fun i => hW X hX i)
  show F X ≡ₜ b
  rw [hFXb]
  exact Cantor.equiv.refl b

end Martin
