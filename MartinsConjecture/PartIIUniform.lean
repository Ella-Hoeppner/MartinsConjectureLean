/-
**Part II of Martin's conjecture for the uniform class.**

Slaman–Steel (1988) proved Part II for uniformly-invariant functions: the
above-identity uniformly-invariant functions are *prewellordered* by the Martin
order `≤ₘ`, with the jump `F ↦ F′` (`F′ X = jump (F X)`) as immediate successor.
This file structures that statement, specialized to the uniform class, into the
same three cores as the Borel version (`FullReduction.lean`, `CoreAnalysis.lean`),
proves the *assembly* (the three cores ⟹ Part II for the uniform class) and every
fragment the existing uniform machinery already yields, and brackets the genuinely
recursion-theoretic cores as explicit named `Prop` hypotheses.

The uniform class here is

    `UniformRegular F := UniformlyTuringInvariant F ∧ AboveIdOnCone F`

— the uniform analogue of `Regular` (`Martin.lean`).  We drop `Measurable`: the
uniform Part-I machinery (`MartinResults.lean`) is entirely measurability-free, so
the `Measurable` hypothesis of `Regular` is vestigial for this class.

### What is PROVED here (assembly + fragments), sorry-free, standard axioms only

* `UniformRegular.jumpComp`, `uniformRegular_jumpIter`, `uniformRegular_id`,
  `uniformRegular_chain` — closure of the class and the canonical Steel chain
  `id <ₘ (·′) <ₘ (·″) <ₘ ⋯` living inside it (from the jump-iterate results).
* `comparison_on_cone_uniform` — the pairwise comparison trichotomy for two
  uniformly-invariant functions (a direct instance of `comparison_on_cone`).
* `partIIUniform_total_of_core`, `partIIUniform_WF_of_core`,
  `partIIUniform_succ_of_core` — each uniform core discharges its half of Part II
  (the assembly), mirroring `partII_*_of_core`.
* `partIIUniform_total_iff_core`, `partIIUniform_WF_iff_core`,
  `partIIUniform_succ_iff_core`, `partIIUniform_iff_cores` — the reductions are
  *exact* (both directions), mirroring `CoreAnalysis.lean`.
* `partIIUniform` / `partIIUniform_of_cores` — the capstone: the three uniform
  cores ⟹ Part II for the uniform class.
* `partIIUniform_succ_provable_half` — the provable half of the successor claim
  (`martinLT_jump`), packaged for the class.

### What is BRACKETED (the genuine Slaman–Steel content), as named `Prop`s

* `PartIIUniform_Comparison`  — no two uniform-regular functions are pointwise
  incomparable on a cone (the totality content).  This is the Slaman–Steel
  *comparison* argument (relativized Steel kernel / comparison game); the existing
  single-function machinery (`comparability_on_cone`, `steelUniformKernel_holds`)
  does not by itself yield the two-function comparison.  BRACKETED.
* `PartIIUniform_WF`          — no infinite `MartinLT`-descending chain of
  uniform-regular functions (well-foundedness).  BRACKETED.
* `PartIIUniform_Succ`        — jump minimality: nothing uniform-regular fits
  strictly between `F` and `F′`.  BRACKETED (the other half, `martinLT_jump`, is
  proved).

Everything conditional only on Turing determinacy (threaded explicitly).
-/
import MartinsConjecture.CoreAnalysis
import MartinsConjecture.MartinResults
import MartinsConjecture.CantorLimit
import Mathlib.Order.OrderIsoNat

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### The uniform class -/

/-- The class quantified over in Part II for the **uniform** case: uniformly
Turing invariant and Martin above the identity.  (The uniform analogue of
`Regular`; `Measurable` is dropped, being vestigial for the uniform Part-I
machinery.) -/
def UniformRegular (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  UniformlyTuringInvariant F ∧ AboveIdOnCone F

/-- Uniform-regularity implies plain Turing invariance. -/
theorem UniformRegular.turingInvariant {F} (h : UniformRegular F) :
    TuringInvariant F := h.1.turingInvariant

theorem UniformRegular.aboveId {F} (h : UniformRegular F) : AboveIdOnCone F := h.2

theorem UniformRegular.uniform {F} (h : UniformRegular F) :
    UniformlyTuringInvariant F := h.1

/-- A `Measurable` `UniformRegular` function is `Regular` (the two classes agree
once measurability is added). -/
theorem UniformRegular.regular {F} (h : UniformRegular F) (hM : Measurable F) :
    Regular F := ⟨hM, h.turingInvariant, h.aboveId⟩

/-! ### Closure of the uniform class and the canonical Steel chain -/

/-- The identity is uniform-regular. -/
theorem uniformRegular_id : UniformRegular (fun X : ℕ → Bool => X) :=
  ⟨uniformlyTuringInvariant_id, ⟨fun _ => false, fun X _ => le.refl X⟩⟩

/-- The uniform class is closed under composing with the jump: `F ↦ F′`. -/
theorem UniformRegular.jumpComp {F : (ℕ → Bool) → ℕ → Bool} (hF : UniformRegular F) :
    UniformRegular (fun X => Cantor.jump (F X)) := by
  obtain ⟨hU, B, hcone⟩ := hF
  exact ⟨uniformlyTuringInvariant_jump.comp hU,
    B, fun X hX => (hcone X hX).trans (le_jump (F X))⟩

/-- Every finite jump iterate is uniform-regular (the canonical Steel chain lives
in the class). -/
theorem uniformRegular_jumpIter : ∀ n, UniformRegular (fun X => Cantor.jump^[n] X) :=
  fun n => ⟨uniformlyTuringInvariant_jumpIterate n, (regular_jumpIter n).2.2⟩

/-- The jump chain `id <ₘ (·′) <ₘ (·″) <ₘ ⋯` is a strictly-increasing ω-chain of
uniform-regular functions — the concrete witness that Part II's order type is at
least `ω` inside the uniform class. -/
theorem uniformRegular_chain (n : ℕ) :
    UniformRegular (fun X => Cantor.jump^[n] X) ∧
    MartinLT (fun X => Cantor.jump^[n] X) (fun X => Cantor.jump^[n + 1] X) :=
  ⟨uniformRegular_jumpIter n, martinLT_jumpIter n⟩

/-! ### The three Part II cores, specialized to the uniform class -/

/-- **Uniform comparison core** (totality): no two uniform-regular functions are
pointwise incomparable on a cone.  This is the totality content of Part II for the
uniform class — the Slaman–Steel comparison argument. -/
def PartIIUniform_Comparison : Prop :=
  ∀ F G : (ℕ → Bool) → ℕ → Bool, UniformRegular F → UniformRegular G →
    OnCone (fun X => ¬ F X ≤ₜ G X ∧ ¬ G X ≤ₜ F X) → False

/-- **Uniform descending-chain core** (well-foundedness): there is no strictly
`≤ₘ`-descending ω-sequence of uniform-regular functions. -/
def PartIIUniform_WF : Prop :=
  ∀ Fs : ℕ → (ℕ → Bool) → ℕ → Bool, (∀ n, UniformRegular (Fs n)) →
    (∀ n, MartinLT (Fs (n + 1)) (Fs n)) → False

/-- **Uniform jump-minimality core** (successor): nothing uniform-regular fits
strictly between `F` and `F′ = jump ∘ F`. -/
def PartIIUniform_Succ : Prop :=
  ∀ F G : (ℕ → Bool) → ℕ → Bool, UniformRegular F → UniformRegular G →
    MartinLT F G → MartinLE (fun X => Cantor.jump (F X)) G

/-! ### The Part II statements for the uniform class -/

/-- Part II totality for the uniform class: the Martin order is total on
uniform-regular functions. -/
def PartIIUniform_Total : Prop :=
  ∀ F G, UniformRegular F → UniformRegular G → MartinLE F G ∨ MartinLE G F

/-- Part II well-foundedness for the uniform class. -/
def PartIIUniform_WellFounded : Prop :=
  WellFounded fun F G : {F // UniformRegular F} => MartinLT F.1 G.1

/-- Part II successor claim for the uniform class: the jump is the successor
operation on uniform-regular functions. -/
def PartIIUniform_Successor : Prop :=
  ∀ F, UniformRegular F →
    MartinLT F (fun X => Cantor.jump (F X)) ∧
    ∀ G, UniformRegular G → MartinLT F G → MartinLE (fun X => Cantor.jump (F X)) G

/-- **Part II of Martin's conjecture for the uniform class**: the Martin order
prewellorders the uniform-regular functions, with the jump as successor. -/
def PartIIUniform : Prop :=
  PartIIUniform_Total ∧ PartIIUniform_WellFounded ∧ PartIIUniform_Successor

/-! ### Pairwise comparison for uniformly-invariant functions -/

/-- Under Turing determinacy, any two uniformly-invariant functions compare on a
cone (a direct instance of `comparison_on_cone`). -/
theorem comparison_on_cone_uniform (hTD : TuringDeterminacy fun _ => True)
    {F G : (ℕ → Bool) → ℕ → Bool}
    (hF : UniformlyTuringInvariant F) (hG : UniformlyTuringInvariant G) :
    OnCone (fun X => F X ≤ₜ G X) ∨ OnCone (fun X => G X <ₜ F X) ∨
    OnCone (fun X => ¬ F X ≤ₜ G X ∧ ¬ G X ≤ₜ F X) :=
  comparison_on_cone hTD hF.turingInvariant hG.turingInvariant

/-! ### The assembly: each uniform core discharges its half of Part II -/

/-- **Totality assembly**: the comparison core gives Part II totality for the
uniform class (via the comparison trichotomy). -/
theorem partIIUniform_total_of_core (hTD : TuringDeterminacy fun _ => True)
    (hcore : PartIIUniform_Comparison) : PartIIUniform_Total := by
  intro F G hF hG
  rcases comparison_on_cone_uniform hTD hF.uniform hG.uniform with h | h | h
  · exact Or.inl h
  · exact Or.inr (onCone_mono (fun X hX => hX.1) h)
  · exact absurd h (fun hc => hcore F G hF hG hc)

/-- **Well-foundedness assembly**: the descending-chain core gives Part II
well-foundedness for the uniform class. -/
theorem partIIUniform_WF_of_core (hcore : PartIIUniform_WF) :
    PartIIUniform_WellFounded := by
  letI : IsIrrefl {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) :=
    ⟨fun F h => h.2 h.1⟩
  letI : IsTrans {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) :=
    ⟨fun F G H h1 h2 => ⟨h1.1.trans h2.1, fun hc => h2.2 (hc.trans h1.1)⟩⟩
  letI : IsStrictOrder {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) := ⟨⟩
  refine RelEmbedding.wellFounded_iff_isEmpty.mpr ⟨fun emb => ?_⟩
  exact hcore (fun n => (emb n).1) (fun n => (emb n).2)
    (fun n => emb.map_rel_iff.mpr (Nat.lt_succ_self n))

/-- **Successor assembly**: the provable half `martinLT_jump` together with the
jump-minimality core gives Part II successor for the uniform class. -/
theorem partIIUniform_succ_of_core (hcore : PartIIUniform_Succ) :
    PartIIUniform_Successor :=
  fun F hF => ⟨martinLT_jump F, fun G hG hFG => hcore F G hF hG hFG⟩

/-- **The capstone assembly**: under Turing determinacy, the three uniform cores
imply Part II of Martin's conjecture for the uniform class. -/
theorem partIIUniform_of_cores (hTD : TuringDeterminacy fun _ => True)
    (h3 : PartIIUniform_Comparison) (h4 : PartIIUniform_WF)
    (h5 : PartIIUniform_Succ) : PartIIUniform :=
  ⟨partIIUniform_total_of_core hTD h3, partIIUniform_WF_of_core h4,
   partIIUniform_succ_of_core h5⟩

/-! ### Exactness of the uniform reductions (both directions) -/

/-- The totality reduction is exact for the uniform class. -/
theorem partIIUniform_total_iff_core (hTD : TuringDeterminacy fun _ => True) :
    PartIIUniform_Total ↔ PartIIUniform_Comparison := by
  constructor
  · intro htot F G hF hG hinc
    obtain ⟨B, hB⟩ | ⟨B, hB⟩ := htot F G hF hG
    · obtain ⟨B', hB'⟩ := onCone_and ⟨B, hB⟩ hinc
      obtain ⟨hle, hnle, -⟩ := hB' B' (le.refl B')
      exact hnle hle
    · obtain ⟨B', hB'⟩ := onCone_and ⟨B, hB⟩ hinc
      obtain ⟨hle, -, hnle⟩ := hB' B' (le.refl B')
      exact hnle hle
  · exact partIIUniform_total_of_core hTD

/-- The well-foundedness reduction is exact for the uniform class. -/
theorem partIIUniform_WF_iff_core : PartIIUniform_WellFounded ↔ PartIIUniform_WF := by
  constructor
  · intro hWF Fs hreg hchain
    letI : IsIrrefl {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) :=
      ⟨fun F h => h.2 h.1⟩
    letI : IsTrans {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) :=
      ⟨fun F G H h1 h2 => ⟨h1.1.trans h2.1, fun hc => h2.2 (hc.trans h1.1)⟩⟩
    letI : IsStrictOrder {F // UniformRegular F} (fun F G => MartinLT F.1 G.1) := ⟨⟩
    exact (RelEmbedding.natGT (fun n => (⟨Fs n, hreg n⟩ : {F // UniformRegular F}))
      (fun n => hchain n)).not_wellFounded hWF
  · exact partIIUniform_WF_of_core

/-- The successor reduction is exact for the uniform class (given the proved half
`martinLT_jump`). -/
theorem partIIUniform_succ_iff_core : PartIIUniform_Successor ↔ PartIIUniform_Succ := by
  constructor
  · intro hsucc F G hF hG hFG
    exact (hsucc F hF).2 G hG hFG
  · exact partIIUniform_succ_of_core

/-- **The full exactness theorem for the uniform class**: under Turing
determinacy, Part II for the uniform class is *equivalent* to the conjunction of
its three cores.  The isolation of the open content is lossless in both
directions (mirroring `partII_iff_cores`). -/
theorem partIIUniform_iff_cores (hTD : TuringDeterminacy fun _ => True) :
    PartIIUniform ↔
      (PartIIUniform_Comparison ∧ PartIIUniform_WF ∧ PartIIUniform_Succ) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(partIIUniform_total_iff_core hTD).mp h1, partIIUniform_WF_iff_core.mp h2,
      partIIUniform_succ_iff_core.mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact partIIUniform_of_cores hTD h1 h2 h3

/-! ### The provable half of the successor claim -/

/-- The provable half of the Part II successor claim for the uniform class: for
every uniform-regular `F`, its jump-composition is again uniform-regular and
strictly Martin above it.  (The open half is *minimality* — `PartIIUniform_Succ`.) -/
theorem partIIUniform_succ_provable_half (F : (ℕ → Bool) → ℕ → Bool)
    (hF : UniformRegular F) :
    UniformRegular (fun X => Cantor.jump (F X)) ∧
    MartinLT F (fun X => Cantor.jump (F X)) :=
  ⟨hF.jumpComp, martinLT_jump F⟩

/-! ### Relating to the Borel Part II framing -/

/-- Any `Regular` (Borel) function that is uniformly invariant is
`UniformRegular`.  This lets the Borel cores be *transferred* on the overlap. -/
theorem uniformRegular_of_regular_uniform {F} (hF : Regular F)
    (hU : UniformlyTuringInvariant F) : UniformRegular F :=
  ⟨hU, hF.2.2⟩

/-- The uniform comparison core follows from the Borel comparison core **for
uniformly-invariant functions that are also measurable** (transfer Borel ⟹
uniform on the measurable overlap; the general uniform statement is stated
`Measurable`-free, which is why this needs the measurability side-hypothesis). -/
theorem partIIUniform_comparison_of_borel
    (hBorel : ComparisonCore)
    (hmeas : ∀ F, UniformRegular F → Measurable F) : PartIIUniform_Comparison :=
  fun F G hF hG hinc =>
    hBorel F G (hF.regular (hmeas F hF)) (hG.regular (hmeas G hG)) hinc

#print axioms uniformRegular_jumpIter
#print axioms uniformRegular_chain
#print axioms comparison_on_cone_uniform
#print axioms partIIUniform_total_of_core
#print axioms partIIUniform_WF_of_core
#print axioms partIIUniform_succ_of_core
#print axioms partIIUniform_of_cores
#print axioms partIIUniform_total_iff_core
#print axioms partIIUniform_WF_iff_core
#print axioms partIIUniform_succ_iff_core
#print axioms partIIUniform_iff_cores
#print axioms partIIUniform_succ_provable_half

end Martin
