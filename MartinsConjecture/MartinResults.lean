/-
**Capstones**: with Bard's Lemma 3.4 (`uti_computable`) discharging the
computable-uniformity hypothesis, both headline results now hold for *bare*
uniform Turing invariance.

* `partI_uniform` — **Part I of Martin's conjecture for uniformly-invariant
  functions** (Slaman–Steel 1988), and both Part I open cores for that class
  (`regressive_uniform`, `incomparable_uniform`);
* `lachlan_dichotomy_cone_uniform`, `lachlan_no_post_solution_cone_uniform` —
  **Lachlan's theorem for r.e. operators**, for bare uniform invariance.

Everything is conditional only on Turing determinacy (threaded explicitly); no
axioms beyond `propext`, `Classical.choice`, `Quot.sound`. -/
import MartinsConjecture.BardUniformity
import MartinsConjecture.LachlanTheorem
import MartinsConjecture.MeasurePreserving

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- **The Steel kernel holds** (no longer a hypothesis): a non-constant
uniformly-invariant function is above the identity on a cone.  Proof: Bard 3.4
(`uti_computable`) supplies computable uniformity, then `steel_kernel_computable`. -/
theorem steelUniformKernel_holds (hTD : TuringDeterminacy fun _ => True) :
    SteelUniformKernel :=
  fun F hF hnc => steel_kernel_computable hTD (uti_computable hF) hnc

/-- **Part I of Martin's conjecture for uniformly-invariant functions**
(Slaman–Steel 1988): every uniformly-invariant `F` is constant on a cone or above
the identity on a cone. -/
theorem partI_uniform (hTD : TuringDeterminacy fun _ => True) : PartI_Uniform_Borel :=
  partI_uniform_of_steel (steelUniformKernel_holds hTD)

/-- **The regressive Part I core, proved for the uniform class**: a
uniformly-invariant function strictly below the identity on a cone is constant on
a cone. -/
theorem regressive_uniform (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hreg : OnCone (fun X => F X <ₜ X)) : ConstantOnCone F :=
  regressive_uniform_of_steel (steelUniformKernel_holds hTD) F hF hreg

/-- **The incomparable Part I core, proved for the uniform class.** -/
theorem incomparable_uniform (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ConstantOnCone F :=
  incomparable_uniform_of_steel (steelUniformKernel_holds hTD) F hF hinc

/-- **Lachlan's theorem for r.e. operators, bare-uniformity form**: a
*uniformly*-invariant r.e. operator above the identity on a cone satisfies, on a
cone, `Wˣ ≡ᵀ X` or `Wˣ ≡ᵀ X′`.  (Bard 3.4 removes the computable-uniformity
hypothesis of `lachlan_dichotomy_cone`.) -/
theorem lachlan_dichotomy_cone_uniform (e : ℕ)
    (hu : UniformlyTuringInvariant (reReal e)) (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy fun _ => True) :
    MartinEquiv (reReal e) (fun X => X) ∨ MartinEquiv (reReal e) (fun X => Cantor.jump X) :=
  lachlan_dichotomy_cone e (uti_computable hu) habove hTD

/-- **No r.e.-operator solution to Post's problem, bare-uniformity form.** -/
theorem lachlan_no_post_solution_cone_uniform (e : ℕ)
    (hu : UniformlyTuringInvariant (reReal e)) (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy fun _ => True) :
    ¬ OnCone (fun X => X <ₜ reReal e X ∧ reReal e X <ₜ Cantor.jump X) :=
  lachlan_no_post_solution_cone e (uti_computable hu) habove hTD

/-- **The uniform class satisfies the class-specific half of the measure-preserving
decomposition**: a non-constant uniformly-invariant function is measure-preserving.
This is the uniform analogue of the Lutz–Siskind lemma (non-trivial order-preserving
⟹ measure-preserving), obtained here from `steel_kernel_computable` — so the whole of
Part 1 for uniformly-invariant functions factors through `partI_iff_measurePreserving`
as this lemma plus Thm 3.4. -/
theorem uniform_nonconstant_measurePreserving (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : UniformlyTuringInvariant F) (hnc : ¬ ConstantOnCone F) :
    MeasurePreserving F :=
  aboveId_measurePreserving (steel_kernel_computable hTD (uti_computable hF) hnc)

/-- **Lutz–Siskind's Theorem 3.4, for the uniform class, tree-free.**  A
measure-preserving *uniformly*-invariant function is above the identity on a cone
— the central pointed-perfect-tree theorem of Lutz–Siskind, obtained here for
uniformly-invariant functions by a completely different route: measure-preservation
rules out constancy, and my Slaman–Steel formalization (`steel_kernel_computable`
∘ Bard 3.4) then forces above-identity, with no Groszek–Slaman coding. -/
theorem measurePreservingAboveId_uniform (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : UniformlyTuringInvariant F)
    (hmp : MeasurePreserving F) : AboveIdOnCone F :=
  steel_kernel_computable hTD (uti_computable hF)
    (fun hc => not_measurePreserving_of_constant hc hmp)

/-- **The uniformity bridge is the *entire* gap to the natural-class Part I.**
`PartI_Borel` and `PartI_Uniform_Borel` differ only by `TuringInvariant` vs
`UniformlyTuringInvariant` (both already assume `Measurable F`).  So, given
determinacy, the sole missing ingredient between the proven uniform case
(`partI_uniform`, Slaman–Steel) and the full published Borel Part I is the single
bridge **"measurable Turing-invariant ⟹ uniformly Turing-invariant"**.  For the Borel
class this bridge is a *known theorem* (Slaman–Steel), merely unformalized here — so this
isolates the single unformalized lemma between our machine-checked uniform case and the
published Borel Part I.  (The AD-*general* case — dropping `Measurable` — needs the bridge
for non-definable `F`, which is not known to hold; see `ATTACK.md`.) -/
theorem partI_Borel_of_uniformity_bridge (hTD : TuringDeterminacy fun _ => True)
    (bridge : ∀ F, Measurable F → TuringInvariant F → UniformlyTuringInvariant F) :
    PartI_Borel :=
  fun F hMeas hInv => partI_uniform hTD F hMeas (bridge F hMeas hInv)

/-- **Part I for uniformly-invariant functions, `Measurable`-free.**  The uniform
cores (`regressive_uniform`, `incomparable_uniform`) never use measurability, so the
`Measurable` hypothesis of `PartI_Uniform_Borel` is vestigial: a uniformly-invariant
`F` is constant on a cone or above the identity on a cone, full stop.  Proof: the
comparability trichotomy sends `≡ᵀ`/`>ᵀ` to above-id and `<ᵀ`/`⊥ᵀ` to the two cores. -/
theorem partI_uniform_general (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hU : UniformlyTuringInvariant F) :
    ConstantOnCone F ∨ AboveIdOnCone F := by
  rcases comparability_on_cone hTD hU.turingInvariant with heq | hgt | hlt | hincomp
  · exact Or.inr ⟨_, fun X hX => (heq.choose_spec X hX).2⟩
  · exact Or.inr ⟨_, fun X hX => (hgt.choose_spec X hX).1⟩
  · exact Or.inl (regressive_uniform hTD F hU hlt)
  · exact Or.inl (incomparable_uniform hTD F hU hincomp)

/-- **Any Part-I counterexample is non-uniformly-invariant** (the contrapositive of
`partI_uniform_general`).  A Turing-invariant `F` that is neither constant on a cone
nor above the identity on a cone cannot be uniformly Turing-invariant — were it uniform,
`partI_uniform_general` would force one of the two excluded alternatives.  So a
hypothetical counterexample is genuinely "wild": its `≡ᵀ`-witness reductions cannot be
transformed uniformly. -/
theorem counterexample_not_uniformlyInvariant (hTD : TuringDeterminacy fun _ => True)
    (F : (ℕ → Bool) → ℕ → Bool) (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    ¬ UniformlyTuringInvariant F := fun hU =>
  (partI_uniform_general hTD F hU).elim hnc hnai

/-- **Capstone: the uniformity bridge is a *sufficient* condition for full
(AD-general) Part I.**  Given determinacy, if *every* Turing-invariant `F` is
uniformly Turing-invariant (on a cone), then Part I holds for *every* Turing-invariant
`F` — no `Measurable`, no class restriction — because `partI_uniform_general` is already
machine-checked.  This is the route by which the Borel case is proven (Borel ⟹ uniform).

*Honesty:* the bridge is **sufficient but not necessary**.  Part I says constant-or-above-id,
and neither implies uniformity (a constant `F` is not uniform; an above-id `F` need not be).
So this is a natural *strengthening* whose own truth for non-definable `F` is itself open — not
a reformulation of Part I.  Part I could conceivably hold via a different argument even if the
bridge fails.  What the barrier in `ATTACK.md` shows is that *this* (the most natural) route is
blocked by cone dichotomy vs cone uniformization. -/
theorem partI_general_of_uniformity (hTD : TuringDeterminacy fun _ => True)
    (bridge : ∀ F, TuringInvariant F → UniformlyTuringInvariant F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  fun F hF => partI_uniform_general hTD F (bridge F hF)

/-- **The uniformity bridge subsumes the `escaping ⟹ MP` route.**  The two known
sufficient conditions for Part I — the uniformity bridge (this file) and
`MartinPPT ∧ (escaping ⟹ MP)` (`partI_of_martinPPT_escaping`) — are not independent:
the uniformity bridge already delivers `escaping ⟹ MP`.  Indeed a uniform `F` is
constant or above-id (`partI_uniform_general`); an escaping `F` isn't constant
(`not_constant_of_escaping`), so it's above-id, hence measure-preserving.  So the
uniformity bridge is the *stronger* of the two open sufficient conditions. -/
theorem escapingMP_of_uniformity_bridge (hTD : TuringDeterminacy fun _ => True)
    (bridge : ∀ F, TuringInvariant F → UniformlyTuringInvariant F) :
    ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F := by
  intro F hF hesc
  rcases partI_uniform_general hTD F (bridge F hF) with hc | hai
  · exact absurd hc (not_constant_of_escaping hesc)
  · exact aboveId_measurePreserving hai

#print axioms partI_uniform
#print axioms partI_Borel_of_uniformity_bridge
#print axioms counterexample_not_uniformlyInvariant
#print axioms partI_uniform_general
#print axioms partI_general_of_uniformity
#print axioms escapingMP_of_uniformity_bridge
#print axioms regressive_uniform
#print axioms incomparable_uniform
#print axioms lachlan_dichotomy_cone_uniform
#print axioms uniform_nonconstant_measurePreserving
#print axioms measurePreservingAboveId_uniform

end Martin
