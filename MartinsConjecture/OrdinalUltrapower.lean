/-
**The cone measure's ordinal ultrapower is well-founded.**

**⚠️ NB (correction, 2026-08-23):** this file's "Fodor engine" was built to attack the *Turing*
regressive core, which is in fact a **KNOWN Slaman–Steel theorem** (`Reduction.RegressiveSlamanSteel`),
*not* open.  The well-foundedness result is valid mathematics, but the "regressive core ⟸ a rank"
framing targets an already-solved problem; the sole open Part-1 content is the incomparable core.

The cone filter is countably complete (`coneFilter_iInter`), so — by Scott's argument —
its ultrapower of the ordinals is *well-founded*: there is **no** infinite descending
sequence `ρ₀ ≻ ρ₁ ≻ …` of ordinal-valued functions where each drop `ρ_{n+1} X < ρ_n X`
holds on a cone.  (Countable completeness collapses the countably-many cones to one; a
point of it would give an infinite strictly-descending sequence of *ordinals*, impossible.)

This is the abstract engine behind every Fodor/pressing-down argument, and it isolates
*exactly* what a proof of the regressive core is missing: a degree-invariant **ordinal
rank** `ρ` that a regressive `F` strictly decreases on a cone (`ρ (F X) < ρ X`).  Given
such a `ρ`, `ρ ∘ F^[n]` would be an infinite descending sequence, contradicting this
theorem.  The only known such rank is `ω₁^x` (hyperarithmetic), which a Turing-regressive
`F` does *not* strictly decrease in the `ω₁`-preserving case — see `ATTACK.md`.
-/
import MartinsConjecture.ConeFilter
import Mathlib.SetTheory.Ordinal.Basic

open scoped Computability
open Cantor

namespace Martin

/-- **No infinite `≺`-descending sequence of ordinal-valued functions on cones.**  If for
every `n` the drop `ρ (n+1) X < ρ n X` holds on a cone, that is a contradiction: countable
completeness of the cone filter puts all the drops on one cone, whose points would carry an
infinite strictly-decreasing sequence of ordinals. -/
theorem no_descending_ordinal_cone {ρ : ℕ → (ℕ → Bool) → Ordinal}
    (h : ∀ n, OnCone (fun X => ρ (n + 1) X < ρ n X)) : False := by
  have hmem : ∀ n, {X | ρ (n + 1) X < ρ n X} ∈ coneFilter :=
    fun n => (onCone_iff_mem_coneFilter).mp (h n)
  have hInter : (⋂ n, {X | ρ (n + 1) X < ρ n X}) ∈ coneFilter := coneFilter_iInter hmem
  rw [mem_coneFilter] at hInter
  obtain ⟨Y, hY⟩ := hInter
  have hYmem : Y ∈ ⋂ n, {X | ρ (n + 1) X < ρ n X} := hY (Cantor.le.refl Y)
  have hdrop : ∀ n, ρ (n + 1) Y < ρ n Y := fun n => Set.mem_iInter.mp hYmem n
  obtain ⟨a, ⟨m, hm⟩, hmin⟩ :=
    Ordinal.lt_wf.has_min (Set.range fun n => ρ n Y) ⟨ρ 0 Y, 0, rfl⟩
  exact hmin (ρ (m + 1) Y) ⟨m + 1, rfl⟩ (hm ▸ hdrop m)

/-- **The regressive core follows from a strictly-decreasing invariant ordinal rank.**
If a Turing-invariant `F` admits a degree-invariant ordinal rank `ρ` that, on `cone base`,
is strictly decreased *and* stays available under iteration (`ρ (F X) < ρ X` whenever
`base ≤ᵀ X`, and `base ≤ᵀ F X`, i.e. cone-preserving), then `F` cannot be regressive-and-
nonconstant there — its iterates would descend the (well-founded) ordinal ultrapower forever.
This packages `no_descending_ordinal_cone`: it makes precise that the *sole* missing
ingredient is a suitable rank.  (The cone-preservation clause is the same wall the direct
descending-chain hits; the genuinely open content is producing `ρ` at all.) -/
theorem no_regressive_of_ordinal_rank {F : (ℕ → Bool) → ℕ → Bool} {base : ℕ → Bool}
    {ρ : (ℕ → Bool) → Ordinal}
    (hstep : ∀ X, base ≤ₜ X → ρ (F X) < ρ X ∧ base ≤ₜ F X) : False := by
  have hpres : ∀ n X, base ≤ₜ X → base ≤ₜ F^[n] X := by
    intro n
    induction n with
    | zero => intro X hX; simpa using hX
    | succ n ih => intro X hX; rw [Function.iterate_succ_apply']; exact (hstep _ (ih X hX)).2
  refine no_descending_ordinal_cone (ρ := fun n X => ρ (F^[n] X)) (fun n => ⟨base, fun X hX => ?_⟩)
  show ρ (F^[n + 1] X) < ρ (F^[n] X)
  rw [Function.iterate_succ_apply']
  exact (hstep _ (hpres n X hX)).1

#print axioms no_descending_ordinal_cone
#print axioms no_regressive_of_ordinal_rank

end Martin
