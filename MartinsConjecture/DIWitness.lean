/-
**The dominated-inverting witness of an incomparable counterexample must be a jump-type operator.**

Part 1's open core reduces (Lutz–Siskind) to two questions about `DominatedInvertible F`
(`∃` invariant `g`, `X ≤ᵀ g(F X)` on a cone):
* **Q3** — is every non-constant invariant `F` dominated-invertible?
* **Q4** — does `DominatedInvertible F ⟹ MeasurePreserving F`?  (Equivalently: is there a
  dominated-invertible *incomparable* `F`? — the sharp Q4 disproof target.)

This file gives elementary but sharpening constraints on both disproof targets.  A witness is
**regressive** if `g c ≤ᵀ c` for every `c` (it never lifts the degree).  Contents:

**Q4 side (the witness of a DI-incomparable `F` is jump-type).**
* `aboveId_of_regressive_diWitness` — a regressive witness forces `F` above the identity
  (`X ≤ᵀ g(F X) ≤ᵀ F X`), hence measure-preserving.
* `not_regressive_diWitness_of_incomparable` / `diWitness_nonRegressive_of_incomparable` — an
  incomparable `F` admits **no** regressive witness; its witness `g` has `g c ≰ᵀ c` somewhere.
* `measurePreserving_of_regressive_diWitness` — *positive* Q4: DI via a regressive witness ⟹ MP, so
  Q4's open content is exactly the non-regressive-witness case.
* `aboveId_of_diWitness_regressive_onValues` / `diWitness_liftsValues_of_incomparable` — the lift is
  *at `F`'s values*: `g(F X) ≰ᵀ F X` cofinally.
* `dominatedInvertible_inflationary` — WLOG the witness is inflationary (`c ≤ᵀ g c`).
* `incomparableDI_strictlyBelow_mp` — a DI-incomparable `F` is *strictly* Martin-below its invariant MP
  dominator `g ∘ F`.
* Honesty pair: `everyInvariant_below_mp` (below an MP function is *universal*, hence vacuous) vs
  `dominatedInvertible_mpFactorsThroughF` (the real content: the MP dominator factors through `F X`).

**Q3 side.**
* `notDominatedInvertible_escapes_jump` — a `¬DI` counterexample has `X ≰ᵀ (F X)′` on every cone
  (jump is a valid invariant witness); iterating, `X` escapes *every* jump-iterate of `F X`.
* `notDI_incomparable_jumpSymmetric` — jump-symmetric: also `(jump X) ≰ᵀ F X`, so neither of `X, F X`
  sits below the other's jump.

**Dynamics of any incomparable `F`.**
* `incomparable_conePreserving_orbitIncomparable` — for a cone-preserving incomparable `F`, consecutive
  orbit iterates are incomparable (`F X ⊥ᵀ F²X`), so the orbit never becomes self-dominating.

Net picture (`incomparable_dichotomy`): a Part-1 counterexample is either `¬DI` (Q3: `F X` loses `X`
below every finite jump-iterate) or DI-incomparable (Q4: `X` recovered from `F X` by a **jump-type** `g`
lifting `F`'s values, while `F X ⊥ᵀ X`).  `MP ⟹ DI` uses the *identity* (regressive) witness — exactly the
route blocked in the incomparable case; and `MP ⟺` DI-via-a-regressive-witness
(`measurePreserving_iff_regressive_diWitness`) crisply separates the solved side from the open core.
-/
import MartinsConjecture.MeasurePreservingCK
import MartinsConjecture.JumpInvariance

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A regressive dominated-inverting witness forces `F` above the identity.**  If `g c ≤ᵀ c` for all
`c` and `X ≤ᵀ g(F X)` on a cone, then `X ≤ᵀ g(F X) ≤ᵀ F X` on that cone, i.e. `AboveIdOnCone F`. -/
theorem aboveId_of_regressive_diWitness {g : (ℕ → Bool) → ℕ → Bool}
    (hreg : ∀ c, g c ≤ₜ c) (hdi : OnCone (fun X => X ≤ₜ g (F X))) : AboveIdOnCone F := by
  obtain ⟨base, hbase⟩ := hdi
  exact ⟨base, fun X hX => (hbase X hX).trans (hreg (F X))⟩

/-- **An incomparable `F` has no regressive dominated-inverting witness.**  A regressive witness would
put `F` above the identity (`aboveId_of_regressive_diWitness`), contradicting `¬ X ≤ᵀ F X`.  Hence the
witness of a dominated-invertible incomparable counterexample must be **non-regressive** (jump-type). -/
theorem not_regressive_diWitness_of_incomparable {g : (ℕ → Bool) → ℕ → Bool}
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hreg : ∀ c, g c ≤ₜ c) :
    ¬ OnCone (fun X => X ≤ₜ g (F X)) := by
  intro hdi
  obtain ⟨b1, hb1⟩ := hinc
  obtain ⟨b2, hb2⟩ := aboveId_of_regressive_diWitness hreg hdi
  exact (hb1 (Cantor.join b1 b2) (Cantor.left_le_join _ _)).2
    (hb2 (Cantor.join b1 b2) (Cantor.right_le_join _ _))

/-- **The witness of a dominated-invertible incomparable `F` is non-regressive** (packaged with
`DominatedInvertible`).  Extracting the witness `g` from `DominatedInvertible F`, there is a degree `c`
with `g c ≰ᵀ c` — `g` genuinely lifts some degree (a jump-type operator, not a mere reprocessing of its
input).  So a Q4 counterexample inverts `F` by strictly *raising* degrees. -/
theorem diWitness_nonRegressive_of_incomparable
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hDI : DominatedInvertible F) :
    ∃ g, TuringInvariant g ∧ OnCone (fun X => X ≤ₜ g (F X)) ∧ ∃ c, ¬ g c ≤ₜ c := by
  obtain ⟨g, hg_inv, hg_cone⟩ := hDI
  refine ⟨g, hg_inv, hg_cone, ?_⟩
  by_contra hall
  push_neg at hall
  exact not_regressive_diWitness_of_incomparable hinc hall hg_cone

/-- **Q4 holds for the regressive-witness subclass.**  If `F` is dominated-invertible via a *regressive*
witness, then `F` is measure-preserving.  So the open content of Q4 (`DI ⟹ MP`) is entirely the
**non-regressive-witness** case: a dominated-invertible `F` all of whose witnesses genuinely lift degrees.
(Positive companion to `not_regressive_diWitness_of_incomparable`.) -/
theorem measurePreserving_of_regressive_diWitness (hM : MartinPPT) (hF : TuringInvariant F)
    {g : (ℕ → Bool) → ℕ → Bool} (hreg : ∀ c, g c ≤ₜ c)
    (hdi : OnCone (fun X => X ≤ₜ g (F X))) : MeasurePreserving F :=
  (mp_iff_aboveId_of_martinPPT hM hF).mpr (aboveId_of_regressive_diWitness hreg hdi)

/-- **Measure-preservation ⟺ dominated-invertibility via a *regressive* witness.**  `MP F` iff `F` has
a dominated-inverting witness that never lifts a degree (the identity `g = id` works, since `MP ⟹`
above-id).  So the "solved" side of the DI hierarchy is exactly the regressive-witness (`ℕ`-handle) case;
the incomparable core is precisely where no such regressive witness exists
(`not_regressive_diWitness_of_incomparable`). -/
theorem measurePreserving_iff_regressive_diWitness (hM : MartinPPT) (hF : TuringInvariant F) :
    MeasurePreserving F ↔
      ∃ g, TuringInvariant g ∧ (∀ c, g c ≤ₜ c) ∧ OnCone (fun X => X ≤ₜ g (F X)) := by
  constructor
  · intro hmp
    exact ⟨fun c => c, fun _ _ h => h, fun c => Cantor.le.refl c,
      (mp_iff_aboveId_of_martinPPT hM hF).mp hmp⟩
  · rintro ⟨g, _, hreg, hcone⟩
    exact measurePreserving_of_regressive_diWitness hM hF hreg hcone

/-! ### The Q3 side: a `¬DI` counterexample escapes even `F`'s jump -/

/-- **A non-dominated-invertible `F` has `F X`'s jump fail to recover `X` on every cone.**  Since the
Turing jump is an invariant map, `X ≤ᵀ (F X)′` on a cone would witness `DominatedInvertible F` (via
`g = jump`).  So `¬DominatedInvertible F ⟹ ¬OnCone(X ≤ᵀ (F X)′)`.  Iterating (each finite/transfinite
jump-iterate is invariant), a `¬DI` counterexample — the Q3 disproof target — must satisfy
`X ≰ᵀ (F X)^{(α)}` cofinally for **every** jump-iterate `α`: `F X` loses `X` so thoroughly that no
invariant jump recovers it.  A strong information-loss demand, matching why `¬DI` is hard to realize. -/
theorem notDominatedInvertible_escapes_jump (h : ¬ DominatedInvertible F) :
    ¬ OnCone (fun X => X ≤ₜ Cantor.jump (F X)) :=
  fun hcone => h ⟨Cantor.jump, turingInvariant_jump, hcone⟩

/-- **A `¬DI` incomparable `F` is jump-symmetrically incomparable to its argument.**  On a cone,
`X ≰ᵀ (F X)′` (the value's jump does not recover `X` — `¬DI`) *and* `(jump X) ≰ᵀ F X` (the argument's
jump is not below the value — incomparability, since `X ≤ᵀ jump X`).  So neither of `X, F X` sits below
the other's jump: the Q3 disproof target is genuinely two-sided at the jump level. -/
theorem notDI_incomparable_jumpSymmetric
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (h : ¬ DominatedInvertible F) :
    ¬ OnCone (fun X => X ≤ₜ Cantor.jump (F X)) ∧
      OnCone (fun X => ¬ Cantor.jump X ≤ₜ F X) := by
  refine ⟨notDominatedInvertible_escapes_jump h, ?_⟩
  obtain ⟨b, hb⟩ := hinc
  exact ⟨b, fun X hX hj => (hb X hX).2 ((Cantor.le_jump X).trans hj)⟩

/-- **Every finite jump-iterate is Turing invariant** (`jump^[n]`), by induction: `jump^[0] = id` and
`jump^[n+1] = jump ∘ jump^[n]`, and `jump` preserves `≡ᵀ` (`jump_congr`). -/
theorem turingInvariant_jumpIter : ∀ n : ℕ, TuringInvariant (Cantor.jump^[n])
  | 0 => fun _ _ h => by simpa using h
  | (n + 1) => fun X Y h => by
      simp only [Function.iterate_succ', Function.comp_apply]
      exact Cantor.jump_congr (turingInvariant_jumpIter n X Y h)

/-- **A `¬DI` counterexample escapes *every finite jump-iterate* of `F X`.**  For each `n`, the map
`jump^[n]` is invariant, so `X ≤ᵀ (F X)^{(n)}` on a cone would witness `DominatedInvertible F`.  Hence
`¬DI ⟹ X ≰ᵀ (F X)^{(n)}` cofinally, for all `n`: the value's whole finite jump-tower fails to recover
`X` — the rigorous form of the information-loss demand on the Q3 disproof target. -/
theorem notDI_escapes_jumpIter (n : ℕ) (h : ¬ DominatedInvertible F) :
    ¬ OnCone (fun X => X ≤ₜ (Cantor.jump^[n]) (F X)) :=
  fun hcone => h ⟨Cantor.jump^[n], turingInvariant_jumpIter n, hcone⟩

/-! ### A dynamical constraint: consecutive orbit iterates are incomparable -/

/-- **For a cone-preserving incomparable `F`, consecutive orbit iterates are incomparable.**  If `F`
maps `cone(base)` into itself and is incomparable to its argument there, then applying incomparability
*at the value* `F X` (which lies in the cone) gives `F X ⊥ᵀ F(F X)`.  So the orbit `X, F X, F²X, …` of a
cone-preserving counterexample consists of consecutively-incomparable degrees — it cannot become
self-dominating (`F(F X) ≤ᵀ F X` is impossible on the cone).  Complements the repo's
`graphOrbit_strictMono` (the orbit *joins* strictly increase). -/
theorem incomparable_conePreserving_orbitIncomparable {base : ℕ → Bool}
    (hpres : ∀ X, base ≤ₜ X → base ≤ₜ F X)
    (hinc : ∀ X, base ≤ₜ X → ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) :
    ∀ X, base ≤ₜ X → ¬ F (F X) ≤ₜ F X ∧ ¬ F X ≤ₜ F (F X) :=
  fun X hX => hinc (F X) (hpres X hX)

/-! ### Localizing the lift to `F`'s values (a sharper form) -/

/-- **Regressivity only *at `F`'s values* already forces above-identity.**  If `g(F X) ≤ᵀ F X` on a
cone (the witness does not lift `F`'s own values), then `X ≤ᵀ g(F X) ≤ᵀ F X` on a cone. -/
theorem aboveId_of_diWitness_regressive_onValues {g : (ℕ → Bool) → ℕ → Bool}
    (hval : OnCone (fun X => g (F X) ≤ₜ F X)) (hdi : OnCone (fun X => X ≤ₜ g (F X))) :
    AboveIdOnCone F := by
  obtain ⟨b1, h1⟩ := hval
  obtain ⟨b2, h2⟩ := hdi
  refine ⟨Cantor.join b1 b2, fun X hX => ?_⟩
  exact (h2 X ((Cantor.right_le_join _ _).trans hX)).trans
    (h1 X ((Cantor.left_le_join _ _).trans hX))

/-- **A dominated-invertible incomparable `F` has a witness that lifts its values cofinally.**  There
is an invariant witness `g` with `X ≤ᵀ g(F X)` on a cone but `g(F X) ≰ᵀ F X` on a *cofinal* set — `g(F X)`
strictly exceeds `F X` in degree infinitely often.  Since `g` is invariant, `g(F X)` is an invariant
degree-lift of `deg(F X)` that nonetheless computes `X`: the extra information recovering `X` comes from
lifting `deg(F X)` (jump-style), not from `F X` itself.  This is the precise shape of a Q4 counterexample. -/
theorem diWitness_liftsValues_of_incomparable
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hDI : DominatedInvertible F) :
    ∃ g, TuringInvariant g ∧ OnCone (fun X => X ≤ₜ g (F X)) ∧
      ¬ OnCone (fun X => g (F X) ≤ₜ F X) := by
  obtain ⟨g, hg_inv, hg_cone⟩ := hDI
  refine ⟨g, hg_inv, hg_cone, fun hval => ?_⟩
  obtain ⟨b1, hb1⟩ := hinc
  obtain ⟨b2, hb2⟩ := aboveId_of_diWitness_regressive_onValues hval hg_cone
  exact (hb1 (Cantor.join b1 b2) (Cantor.left_le_join _ _)).2
    (hb2 (Cantor.join b1 b2) (Cantor.right_le_join _ _))

/-! ### The witness may be taken inflationary, and the induced MP dominator -/

/-- **WLOG the dominated-inverting witness is inflationary** (`c ≤ᵀ g c`).  Replacing any witness `g₀`
by `g c := c ⊕ g₀ c` keeps it invariant and dominating (`X ≤ᵀ g₀(F X) ≤ᵀ g(F X)`) while making it lie
above the identity.  So `DominatedInvertible F` always has a witness that never *lowers* a degree. -/
theorem dominatedInvertible_inflationary (hDI : DominatedInvertible F) :
    ∃ g, TuringInvariant g ∧ (∀ c, c ≤ₜ g c) ∧ OnCone (fun X => X ≤ₜ g (F X)) := by
  obtain ⟨g₀, hg₀inv, hg₀cone⟩ := hDI
  refine ⟨fun c => Cantor.join c (g₀ c), ?_, fun c => Cantor.left_le_join _ _, ?_⟩
  · intro X Y hXY
    exact ⟨Cantor.join_le (hXY.1.trans (Cantor.left_le_join _ _))
            ((hg₀inv X Y hXY).1.trans (Cantor.right_le_join _ _)),
           Cantor.join_le (hXY.2.trans (Cantor.left_le_join _ _))
            ((hg₀inv X Y hXY).2.trans (Cantor.right_le_join _ _))⟩
  · obtain ⟨b, hb⟩ := hg₀cone
    exact ⟨b, fun X hX => (hb X hX).trans (Cantor.right_le_join _ _)⟩

/-- **Every invariant `F` is Martin-below an invariant measure-preserving function** — namely
`H X = (X ⊕ F X)′`, the jump of the join.  So lying *below* an MP function is **universal**: it holds for
*every* invariant `F` and hence carries no information.  This is exactly why "below an MP function" is the
*wrong* reading of dominated-invertibility; the real content is that the recovery of `X` **factors through
`F X` alone** (`dominatedInvertible_mpFactorsThroughF`). -/
theorem everyInvariant_below_mp (hM : MartinPPT) (hF : TuringInvariant F) :
    ∃ H, TuringInvariant H ∧ MeasurePreserving H ∧
      OnCone (fun X => F X ≤ₜ H X) ∧ OnCone (fun X => X ≤ₜ H X) := by
  have hHinv : TuringInvariant (fun X => jump (Cantor.join X (F X))) := by
    intro X Y hXY
    exact jump_congr ⟨Cantor.join_le (hXY.1.trans (Cantor.left_le_join _ _))
          ((hF X Y hXY).1.trans (Cantor.right_le_join _ _)),
        Cantor.join_le (hXY.2.trans (Cantor.left_le_join _ _))
          ((hF X Y hXY).2.trans (Cantor.right_le_join _ _))⟩
  have haboveId : OnCone (fun X => X ≤ₜ jump (Cantor.join X (F X))) :=
    ⟨fun _ => false, fun X _ => (Cantor.left_le_join X (F X)).trans (Cantor.le_jump _)⟩
  exact ⟨fun X => jump (Cantor.join X (F X)), hHinv,
    (mp_iff_aboveId_of_martinPPT hM hHinv).mpr haboveId,
    ⟨fun _ => false, fun X _ => (Cantor.right_le_join X (F X)).trans (Cantor.le_jump _)⟩, haboveId⟩

/-- **The DI-specific content: the measure-preserving dominator factors through `F`.**  For a
dominated-invertible `F`, the inflationary witness `g` makes `H := g ∘ F` invariant and measure-preserving
with `X ≤ᵀ H X` — and `H` is a function of `F X` **alone**.  Contrast `everyInvariant_below_mp`: *below* an
MP function is free, but a dominator *depending only on `F X`* that still recovers `X` is exactly
`StrictHalfFor F` — the genuine strict-half content, here with a single witness `g` realizing both. -/
theorem dominatedInvertible_mpFactorsThroughF (hM : MartinPPT) (hF : TuringInvariant F)
    (hDI : DominatedInvertible F) :
    ∃ g, TuringInvariant g ∧ MeasurePreserving (fun X => g (F X)) ∧
      OnCone (fun X => X ≤ₜ g (F X)) := by
  obtain ⟨g, hginv, _, hcone⟩ := dominatedInvertible_inflationary hDI
  have hHinv : TuringInvariant (fun X => g (F X)) := fun X Y hXY => hginv (F X) (F Y) (hF X Y hXY)
  exact ⟨g, hginv, (mp_iff_aboveId_of_martinPPT hM hHinv).mpr hcone, hcone⟩

/-- **A dominated-invertible incomparable `F` is *strictly* Martin-below its invariant measure-preserving
dominator.**  With the inflationary witness `g`, set `H := g ∘ F` (invariant, MP).  Then `F X ≤ᵀ H X` on a
cone (inflationarity) but `H X ≰ᵀ F X` cofinally (else `H`'s regressivity at values would force `F`
above-identity, contradicting incomparability).  So `F <_Martin H` strictly: the sideways counterexample
sits *properly beneath* a genuine MP (jump-type) function — the gap `H \ F` is precisely the invariant
degree-lift that recovers `X`.  (Uses incomparability, unlike `everyInvariant_below_mp`.) -/
theorem incomparableDI_strictlyBelow_mp (hM : MartinPPT) (hF : TuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (hDI : DominatedInvertible F) :
    ∃ H, TuringInvariant H ∧ MeasurePreserving H ∧
      OnCone (fun X => F X ≤ₜ H X) ∧ ¬ OnCone (fun X => H X ≤ₜ F X) := by
  obtain ⟨g, hginv, hinfl, hcone⟩ := dominatedInvertible_inflationary hDI
  have hHinv : TuringInvariant (fun X => g (F X)) := fun X Y hXY => hginv (F X) (F Y) (hF X Y hXY)
  refine ⟨fun X => g (F X), hHinv, (mp_iff_aboveId_of_martinPPT hM hHinv).mpr hcone,
    ⟨fun _ => false, fun X _ => hinfl (F X)⟩, fun hval => ?_⟩
  obtain ⟨b1, hb1⟩ := hinc
  obtain ⟨b2, hb2⟩ := aboveId_of_diWitness_regressive_onValues hval hcone
  exact (hb1 (Cantor.join b1 b2) (Cantor.left_le_join _ _)).2
    (hb2 (Cantor.join b1 b2) (Cantor.right_le_join _ _))

/-- **The complete counterexample dichotomy** (synthesis of the Q3 and Q4 characterizations).  An
incomparable invariant `F` is exactly one of:
* **Q4** — dominated-invertible via an invariant witness `g` that **lifts `F`'s values** (`g(F X) ≰ᵀ F X`
  cofinally, a jump-type operator recovering `X` from a lift of `deg(F X)`); or
* **Q3** — *not* dominated-invertible, in which case `X` escapes **every finite jump-iterate** of `F X`.

So any Part-1 counterexample is a "value-lifting-recoverable" (Q4) or "jump-transcendently-lossy" (Q3)
invariant sideways function — the two horns, both open only at the level of *invariant realizability*. -/
theorem incomparable_dichotomy (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) :
    (∃ g, TuringInvariant g ∧ OnCone (fun X => X ≤ₜ g (F X)) ∧
        ¬ OnCone (fun X => g (F X) ≤ₜ F X))
      ∨ (∀ n, ¬ OnCone (fun X => X ≤ₜ (Cantor.jump^[n]) (F X))) := by
  by_cases hDI : DominatedInvertible F
  · exact Or.inl (diWitness_liftsValues_of_incomparable hinc hDI)
  · exact Or.inr (fun n => notDI_escapes_jumpIter n hDI)

#print axioms aboveId_of_regressive_diWitness
#print axioms measurePreserving_of_regressive_diWitness
#print axioms notDominatedInvertible_escapes_jump
#print axioms turingInvariant_jumpIter
#print axioms notDI_escapes_jumpIter
#print axioms incomparable_dichotomy
#print axioms notDI_incomparable_jumpSymmetric
#print axioms incomparable_conePreserving_orbitIncomparable
#print axioms incomparableDI_strictlyBelow_mp
#print axioms not_regressive_diWitness_of_incomparable
#print axioms diWitness_nonRegressive_of_incomparable
#print axioms aboveId_of_diWitness_regressive_onValues
#print axioms diWitness_liftsValues_of_incomparable
#print axioms dominatedInvertible_inflationary
#print axioms everyInvariant_below_mp
#print axioms dominatedInvertible_mpFactorsThroughF

end Martin
