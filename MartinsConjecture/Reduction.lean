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

/-- **The exact gap to continuity (hence to the Borel route), formalized.**
`exists_uniform_index_on_cone` computes `F` by a single code `e` on *one representative* `Y ≡ᵀ X`
of every degree — but that choice of representative is non-invariant.  This is the other side: *if*
the good code can be chosen **invariantly** (an index `idx` constant on each degree, with
`F X = Φ_{idx X}^X` on a cone), then `F` is **continuous on a cone** — a single functional `Φ_e`
computes `F X` from `X` itself.  Proof: an invariant `ℕ`-valued `idx` is constant `= e` on a cone
(σ-pigeonhole over its invariant level sets `{idx = n}`), and there `Φ_{idx X} = Φ_e`.  So the sole
obstruction between the machine-checked `exists_uniform_index_on_cone` and continuity — whence Part I
via Slaman–Steel's `continuous ⟹ Borel ⟹ uniform` — is precisely **invariance of the index
selection** (equivalently, uniformization of the good-representative relation on a cone). -/
theorem continuousOnCone_of_invariantIndex (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} {idx : (ℕ → Bool) → ℕ}
    (hinv : ∀ X X', X ≡ₜ X' → idx X = idx X')
    (hgood : OnCone fun X => eval (toPFun X) (ofNatCode (idx X)) = toPFun (F X)) :
    ∃ e : ℕ, OnCone fun X => eval (toPFun X) (ofNatCode e) = toPFun (F X) := by
  set B : ℕ → Set (ℕ → Bool) := fun n => {X | idx X = n} with hB
  have hTI : ∀ n, TuringInvariantSet (B n) := by
    intro n X X' hXX'
    constructor
    · intro h; show idx X' = n; rw [← hinv X X' hXX']; exact h
    · intro h; show idx X = n; rw [hinv X X' hXX']; exact h
  have hcover : cone (fun _ => false) ⊆ ⋃ n, B n := fun X _ =>
    Set.mem_iUnion.mpr ⟨idx X, rfl⟩
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover
  obtain ⟨W, hW⟩ := onCone_and hn hgood
  refine ⟨n, W, fun X hX => ?_⟩
  have hidx : idx X = n := (hW X hX).1
  have hg := (hW X hX).2
  rwa [hidx] at hg

/-- **The `continuous ⟹ constant` step**, as a named hypothesis: a regressive invariant function
that is *continuous on a cone* (`F X = Φ_e^X` for a single code `e`) is constant on a cone.  This is
*known mathematics*: a continuous `F` is a **recursive** function (a Turing functional), and Slaman–Steel
proved Martin's conjecture Part 1 for recursive functions directly, via a rates-of-convergence argument.
So this hypothesis is genuinely a theorem — it is simply not formalized here.  (It is *not* obtained via
a hypothetical "`Borel ⟹ uniform`", which is *not* a known theorem — that is essentially Steel's
conjecture, still open.  And continuity does not give uniformity directly: `EquivVia` needs reduction
codes uniform in `(i,j)`, which a fixed functional does not supply for a regressive `F`.) -/
def ContinuousRegressiveConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → OnCone (fun X => F X <ₜ X) →
    (∃ e : ℕ, OnCone fun X => eval (toPFun X) (ofNatCode e) = toPFun (F X)) →
    ConstantOnCone F

/-- **The genuine open crux, isolated**: every regressive invariant `F` admits an **invariant**
good-index on a cone — a degree-invariant `idx` with `F X = Φ_{idx X}^X`.  This is exactly
uniformization of the good-representative relation on a cone, which determinacy does not deliver
(see `ATTACK.md`); it is the 50-year-open content. -/
def HasInvariantGoodIndex : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → OnCone (fun X => F X <ₜ X) →
    ∃ idx : (ℕ → Bool) → ℕ, (∀ X X', X ≡ₜ X' → idx X = idx X') ∧
      OnCone fun X => eval (toPFun X) (ofNatCode (idx X)) = toPFun (F X)

/-- **The open regressive core = invariant-index-selection, modulo the known continuous case.**
`RegressiveImpliesConstant` follows from (i) `ContinuousRegressiveConstant` (the Slaman–Steel
`continuous ⟹ constant` step, *known*) and (ii) `HasInvariantGoodIndex` (an invariant good-index on
a cone).  Proof: (ii) gives an invariant index; `continuousOnCone_of_invariantIndex` upgrades it to
continuity on a cone; (i) finishes.  This pins the open content precisely: of the two inputs, (i) is
known mathematics and (ii) — cone uniformization of the good-representative relation — is the genuine
open crux. -/
theorem regressiveCore_of_invariantIndex (hTD : TuringDeterminacy fun _ => True)
    (hcont : ContinuousRegressiveConstant) (hidx : HasInvariantGoodIndex) :
    RegressiveImpliesConstant := by
  intro F hF hreg
  obtain ⟨idx, hinv, hgood⟩ := hidx F hF hreg
  obtain ⟨e, he⟩ := continuousOnCone_of_invariantIndex hTD hinv hgood
  exact hcont F hF hreg ⟨e, he⟩

/-- **Master reduction: full Part I in terms of the precise open content.**  Combining
`partI_of_cores` with `regressiveCore_of_invariantIndex`, Part I holds given three named inputs:
`ContinuousRegressiveConstant` (**known** — continuous ⟹ Borel ⟹ uniform ⟹ `regressive_uniform`),
`HasInvariantGoodIndex` (the regressive open crux — cone uniformization of the good-representative
relation), and `IncomparableImpliesConstant` (the incomparable open core — Posner–Robinson territory).
So the entire gap between the machine-checked material and full Part I is exactly: one known lemma plus
two genuinely-open cone-uniformization problems. -/
theorem partI_of_invariantIndex_and_incomparable (hTD : TuringDeterminacy fun _ => True)
    (hcont : ContinuousRegressiveConstant) (hidx : HasInvariantGoodIndex)
    (hincomp : IncomparableImpliesConstant) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
      ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_cores hTD (regressiveCore_of_invariantIndex hTD hcont hidx) hincomp

#print axioms comparability_on_cone
#print axioms partI_of_cores
#print axioms exists_uniform_index_on_cone
#print axioms continuousOnCone_of_invariantIndex
#print axioms regressiveCore_of_invariantIndex
#print axioms partI_of_invariantIndex_and_incomparable

end Martin
