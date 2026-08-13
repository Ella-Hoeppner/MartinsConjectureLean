/-
Reduction of Martin's conjecture, Part I, to its open cores.

Under Turing determinacy, every Turing-invariant function falls, on a cone,
into exactly one of four comparability regimes with respect to the identity
(`comparability_on_cone`): equivalent, strictly above, strictly below, or
incomparable.  In the first two regimes Part I holds outright.  Hence
**Part I reduces to two statements** (`partI_of_cores`):

* `RegressiveImpliesConstant` — a Turing-invariant function strictly below
  the identity on a cone is constant on a cone;
* `IncomparableImpliesConstant` — a Turing-invariant function pointwise
  incomparable with the identity on a cone is constant on a cone.

These are exactly the open cores of the conjecture: both are known when the
function is uniformly invariant (Steel; Slaman–Steel) or order preserving
(Lutz–Siskind), and open in general — for Borel functions this is the open
part of the Borel Martin conjecture.  We also prove the classical first step
of every known attack on the cores: **index stabilization**
(`exists_uniform_index_on_cone`) — on a cone, every degree has a
representative on which `F` is computed by a single fixed oracle machine.

All results here take `TuringDeterminacy` as an explicit hypothesis (see
`MartinMeasure.lean`): with the class `Γ := fun _ => True` it is the AD-style
hypothesis; the corresponding Borel statements would substitute Martin's
Borel determinacy theorem (ZFC, not yet formalized in Lean).
-/
import MartinsConjecture.MartinMeasure

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-! ### The four comparability regimes are Turing invariant -/

private theorem ti_equiv (hF : TuringInvariant F) :
    TuringInvariantSet {X | F X ≡ₜ X} := by
  intro X Y hXY
  have hFXY := hF X Y hXY
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hFXY.2.trans h1).trans hXY.1, (hXY.2.trans h2).trans hFXY.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hFXY.1.trans h1).trans hXY.2, (hXY.1.trans h2).trans hFXY.2⟩

private theorem le_congr (hF : TuringInvariant F) {X Y : ℕ → Bool}
    (hXY : X ≡ₜ Y) (h : X ≤ₜ F X) : Y ≤ₜ F Y :=
  (hXY.2.trans h).trans (hF X Y hXY).1

private theorem ge_congr (hF : TuringInvariant F) {X Y : ℕ → Bool}
    (hXY : X ≡ₜ Y) (h : F X ≤ₜ X) : F Y ≤ₜ Y :=
  ((hF X Y hXY).2.trans h).trans hXY.1

private theorem ti_above (hF : TuringInvariant F) :
    TuringInvariantSet {X | X <ₜ F X} := by
  intro X Y hXY
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_congr hF hXY h1, fun hc => h2 (ge_congr hF hXY.symm hc)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_congr hF hXY.symm h1, fun hc => h2 (ge_congr hF hXY hc)⟩

private theorem ti_below (hF : TuringInvariant F) :
    TuringInvariantSet {X | F X <ₜ X} := by
  intro X Y hXY
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨ge_congr hF hXY h1, fun hc => h2 (le_congr hF hXY.symm hc)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ge_congr hF hXY.symm h1, fun hc => h2 (le_congr hF hXY hc)⟩

private theorem ti_incomp (hF : TuringInvariant F) :
    TuringInvariantSet {X | ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X} := by
  intro X Y hXY
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (ge_congr hF hXY.symm hc), fun hc => h2 (le_congr hF hXY.symm hc)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (ge_congr hF hXY hc), fun hc => h2 (le_congr hF hXY hc)⟩

/-- Indexed packaging of the four regimes, for the σ-pigeonhole. -/
private def compSets (F : (ℕ → Bool) → ℕ → Bool) : ℕ → Set (ℕ → Bool)
  | 0 => {X | F X ≡ₜ X}
  | 1 => {X | X <ₜ F X}
  | 2 => {X | F X <ₜ X}
  | _ + 3 => {X | ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X}

/-- **Comparability trichotomy** (four-chotomy): under Turing determinacy,
every Turing-invariant function is, on a cone, equivalent to the identity,
strictly above it, strictly below it, or pointwise incomparable with it. -/
theorem comparability_on_cone (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) :
    OnCone (fun X => F X ≡ₜ X) ∨ OnCone (fun X => X <ₜ F X) ∨
    OnCone (fun X => F X <ₜ X) ∨ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) := by
  have hTI : ∀ n, TuringInvariantSet (compSets F n) := by
    intro n
    match n with
    | 0 => exact ti_equiv hF
    | 1 => exact ti_above hF
    | 2 => exact ti_below hF
    | m + 3 => exact ti_incomp hF
  have hcover : cone (fun _ => false) ⊆ ⋃ n, compSets F n := by
    intro X _
    by_cases h1 : F X ≤ₜ X <;> by_cases h2 : X ≤ₜ F X
    · exact Set.mem_iUnion.mpr ⟨0, ⟨h1, h2⟩⟩
    · exact Set.mem_iUnion.mpr ⟨2, ⟨h1, h2⟩⟩
    · exact Set.mem_iUnion.mpr ⟨1, ⟨h2, h1⟩⟩
    · exact Set.mem_iUnion.mpr ⟨3, ⟨h1, h2⟩⟩
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover
  match n with
  | 0 => exact Or.inl hn
  | 1 => exact Or.inr (Or.inl hn)
  | 2 => exact Or.inr (Or.inr (Or.inl hn))
  | m + 3 => exact Or.inr (Or.inr (Or.inr hn))

/-! ### The open cores, and the reduction -/

/-- **Open core 1 (the regressive case)**: every Turing-invariant function
strictly below the identity on a cone is constant on a cone.  Known for
uniformly invariant and for order-preserving functions; open in general. -/
def RegressiveImpliesConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X <ₜ X) → ConstantOnCone F

/-- **Open core 2 (the incomparable case)**: every Turing-invariant function
pointwise incomparable with the identity on a cone is constant on a cone.
Known for uniformly invariant and for order-preserving functions; open in
general. -/
def IncomparableImpliesConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) → ConstantOnCone F

/-- **The reduction**: under Turing determinacy, Part I of Martin's
conjecture follows from its two open cores. -/
theorem partI_of_cores (hTD : TuringDeterminacy fun _ => True)
    (h1 : RegressiveImpliesConstant) (h2 : IncomparableImpliesConstant) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
      ConstantOnCone F ∨ AboveIdOnCone F := by
  intro F hF
  rcases comparability_on_cone hTD hF with h | h | h | h
  · exact Or.inr (onCone_mono (fun X hX => hX.2) h)
  · exact Or.inr (onCone_mono (fun X hX => hX.1) h)
  · exact Or.inl (h1 F hF h)
  · exact Or.inl (h2 F hF h)

/-- The reduction, specialized to the Borel statement `PartI_Borel`. -/
theorem partI_Borel_of_cores (hTD : TuringDeterminacy fun _ => True)
    (h1 : RegressiveImpliesConstant) (h2 : IncomparableImpliesConstant) :
    PartI_Borel :=
  fun F _ hF => partI_of_cores hTD h1 h2 F hF

/-! ### Index stabilization -/

/-- **Index stabilization**: under Turing determinacy, if `F` is Turing
invariant and computable-from-the-input on a cone, then a *single* oracle
machine computes `F` on some representative of every degree on a cone.  This
is the standard first step of the known attacks on the open cores (Lachlan,
Steel, Slaman–Steel). -/
theorem exists_uniform_index_on_cone (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hreg : OnCone fun X => F X ≤ₜ X) :
    ∃ e : ℕ, OnCone fun X => ∃ Y, Y ≡ₜ X ∧
      eval (toPFun Y) (ofNatCode e) = toPFun (F Y) := by
  obtain ⟨W, hW⟩ := hreg
  set A : ℕ → Set (ℕ → Bool) := fun e =>
    {X | ∃ Y, Y ≡ₜ X ∧ eval (toPFun Y) (ofNatCode e) = toPFun (F Y)} with hA
  have hTI : ∀ e, TuringInvariantSet (A e) := by
    intro e X X' hXX'
    constructor
    · rintro ⟨Y, hY, hcomp⟩
      exact ⟨Y, hY.trans hXX', hcomp⟩
    · rintro ⟨Y, hY, hcomp⟩
      exact ⟨Y, hY.trans hXX'.symm, hcomp⟩
  have hcover : cone W ⊆ ⋃ e, A e := by
    intro X hX
    obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp (hW X hX))
    exact Set.mem_iUnion.mpr ⟨encodeCode c, X, equiv.refl X,
      by rw [ofNatCode_encodeCode]; exact hc⟩
  exact exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover

#print axioms comparability_on_cone
#print axioms partI_of_cores
#print axioms exists_uniform_index_on_cone

end Martin
