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

Of these two, the **regressive core is a KNOWN theorem** in general — Slaman–Steel
proved Part 1 for all regressive functions on the Turing degrees (Thm 1.4; see
`RegressiveSlamanSteel` / `regressiveImpliesConstant_of_slamanSteel`).  The
**incomparable core is the sole genuinely-open** content of Part 1 (both are, in
addition, known for uniformly-invariant and order-preserving functions).  We also
prove the classical first step
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

/-- **The regressive case** — *not open*, a **Slaman–Steel theorem** (see
`regressiveImpliesConstant_of_slamanSteel`): every Turing-invariant function
strictly below the identity on a cone is constant on a cone. -/
def RegressiveImpliesConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X <ₜ X) → ConstantOnCone F

/-- **The incomparable case — the SOLE genuinely-open core of Part 1**: every
Turing-invariant function pointwise incomparable with the identity on a cone is
constant on a cone.  (Known for uniformly-invariant and order-preserving functions;
open in general — this is the "off to the side" case of Lutz–Siskind's Figure 1.) -/
def IncomparableImpliesConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) → ConstantOnCone F

/-- **The reduction**: under Turing determinacy, Part I of Martin's
conjecture follows from its two cores (the regressive one being a known
Slaman–Steel theorem; see `partI_of_slamanSteel_incomparable`). -/
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

/-! ### The regressive core is KNOWN (Slaman–Steel); only the incomparable core is open -/

/-- **Slaman–Steel's regressive theorem, as a named KNOWN hypothesis** (ZF+AD): a regressive
Turing-invariant function (`F X ≤ᵀ X` on a cone) is constant on a cone or above the identity on a cone.
This is **established mathematics** — Slaman–Steel proved Part 1 of Martin's conjecture for *all*
regressive functions on the Turing degrees (Lutz–Siskind Thm 1.4; independently confirmed: "if `f` is
Turing-invariant with `f(x) ≤ᵀ x` for all `x`, then `f` is constant on a cone or `f(x) ≡ᵀ x` on a
cone").  It is **not open** — merely unformalized here.  (Earlier framing in this project mislabeled the
regressive core as the open ~50-year problem, conflating it with Lutz's *hyperarithmetic-degrees*
result, `arXiv:2306.05746`, which concerns a different degree structure.) -/
def RegressiveSlamanSteel : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X ≤ₜ X) → ConstantOnCone F ∨ AboveIdOnCone F

/-- **The regressive core is a consequence of Slaman–Steel's theorem — i.e. it is NOT open.**  A
strictly-regressive `F` (`F X <ᵀ X` on a cone) is in particular regressive (`F X ≤ᵀ X`), so Slaman–Steel
gives constant-or-above-id; strict regressivity rules out above-id (it would force `X <ᵀ X`).  Hence
`RegressiveImpliesConstant` holds outright given `RegressiveSlamanSteel`. -/
theorem regressiveImpliesConstant_of_slamanSteel (hSS : RegressiveSlamanSteel) :
    RegressiveImpliesConstant := by
  intro F hF hreg
  rcases hSS F hF (onCone_mono (fun _ h => h.1) hreg) with hc | hai
  · exact hc
  · exfalso
    obtain ⟨W, hW⟩ := onCone_and hreg hai
    exact (hW W (Cantor.le.refl W)).1.2 (hW W (Cantor.le.refl W)).2

/-- **The corrected picture of Part 1's open content.**  Part 1 follows from `RegressiveSlamanSteel`
(a KNOWN Slaman–Steel theorem) together with `IncomparableImpliesConstant`.  Since the former is known,
the **sole genuinely-open content of Part 1 is the incomparable core** — ruling out functions "off to
the side" (`F X ⊥ᵀ X`, incomparable to their argument), exactly the remaining case Lutz–Siskind
identify (their Figure 1). -/
theorem partI_of_slamanSteel_incomparable (hTD : TuringDeterminacy fun _ => True)
    (hSS : RegressiveSlamanSteel) (h2 : IncomparableImpliesConstant) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_cores hTD (regressiveImpliesConstant_of_slamanSteel hSS) h2

/-- **A Part-1 counterexample is incomparable to its argument** — the sharpened profile, using the
KNOWN regressive theorem.  A Turing-invariant `F` that is neither constant nor above-id on a cone is,
on a cone, `F X ⊥ᵀ X`: the `≡ᵀ`/`>ᵀ` regimes give above-id, and the regressive `<ᵀ` regime gives
constant (Slaman–Steel).  So any counterexample lives entirely in the incomparable core. -/
theorem counterexample_incomparable_to_argument (hTD : TuringDeterminacy fun _ => True)
    (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) := by
  rcases comparability_on_cone hTD hF with heq | hgt | hlt | hincomp
  · exact absurd (onCone_mono (fun _ hX => hX.2) heq) hnai
  · exact absurd (onCone_mono (fun _ hX => hX.1) hgt) hnai
  · exact absurd (regressiveImpliesConstant_of_slamanSteel hSS F hF hlt) hnc
  · exact hincomp

/-- **The reverse direction**: Part 1 implies the incomparable core (an above-id `F` cannot be
incomparable to its argument). -/
theorem incomparableImpliesConstant_of_partI
    (hpartI : ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) :
    IncomparableImpliesConstant := by
  intro F hF hincomp
  rcases hpartI F hF with hc | hai
  · exact hc
  · exfalso
    obtain ⟨W, hW⟩ := onCone_and hincomp hai
    exact (hW W (Cantor.le.refl W)).1.2 (hW W (Cantor.le.refl W)).2

/-- **Part 1 ⟺ the incomparable core** (given the KNOWN regressive theorem).  Since Slaman–Steel's
regressive theorem is established (`RegressiveSlamanSteel`), Part 1 of Martin's conjecture is
*equivalent* to its single open core — the incomparable case.  This is the precise corrected statement
of exactly what remains open in Part 1. -/
theorem partI_iff_incomparable (hTD : TuringDeterminacy fun _ => True) (hSS : RegressiveSlamanSteel) :
    (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F)
      ↔ IncomparableImpliesConstant :=
  ⟨incomparableImpliesConstant_of_partI, partI_of_slamanSteel_incomparable hTD hSS⟩

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

/-- **A sufficient condition for the regressive core** (⚠️ *not* the open content — the regressive
core is a KNOWN Slaman–Steel theorem, `regressiveImpliesConstant_of_slamanSteel`): every regressive
invariant `F` admits an **invariant** good-index on a cone — a degree-invariant `idx` with
`F X = Φ_{idx X}^X`.  This is uniformization of the good-representative relation on a cone.  (Prior
framing called this "the 50-year-open content"; that was the regressive-is-open error.  It remains a
valid *sufficient* route, but Slaman–Steel proved the regressive core outright by other means.) -/
def HasInvariantGoodIndex : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → OnCone (fun X => F X <ₜ X) →
    ∃ idx : (ℕ → Bool) → ℕ, (∀ X X', X ≡ₜ X' → idx X = idx X') ∧
      OnCone fun X => eval (toPFun X) (ofNatCode (idx X)) = toPFun (F X)

/-- **A sufficient route to the (KNOWN) regressive core = invariant-index-selection, modulo the
continuous case.**  `RegressiveImpliesConstant` (⚠️ itself a *known* Slaman–Steel theorem — see
`regressiveImpliesConstant_of_slamanSteel`) *also* follows from (i) `ContinuousRegressiveConstant` and
(ii) `HasInvariantGoodIndex`.  Proof: (ii) gives an invariant index; `continuousOnCone_of_invariantIndex`
upgrades it to continuity on a cone; (i) finishes.  This is a *sufficient* route, from the era when the
regressive core was mistakenly thought open; it is not the open content of Part 1. -/
theorem regressiveCore_of_invariantIndex (hTD : TuringDeterminacy fun _ => True)
    (hcont : ContinuousRegressiveConstant) (hidx : HasInvariantGoodIndex) :
    RegressiveImpliesConstant := by
  intro F hF hreg
  obtain ⟨idx, hinv, hgood⟩ := hidx F hF hreg
  obtain ⟨e, he⟩ := continuousOnCone_of_invariantIndex hTD hinv hgood
  exact hcont F hF hreg ⟨e, he⟩

/-- **`ContinuousRegressiveConstant` is subsumed by the KNOWN regressive theorem.**  The
continuity hypothesis is unnecessary: Slaman–Steel's regressive theorem already gives constancy for
*every* strictly-regressive `F`.  (So the `hcont` input of `regressiveCore_of_invariantIndex` is free,
confirming that reduction targets an already-solved core.) -/
theorem continuousRegressiveConstant_of_slamanSteel (hSS : RegressiveSlamanSteel) :
    ContinuousRegressiveConstant :=
  fun F hF hreg _ => regressiveImpliesConstant_of_slamanSteel hSS F hF hreg

/-- **Master reduction (a sufficient route), superseded by `partI_of_slamanSteel_incomparable`.**
Combining `partI_of_cores` with `regressiveCore_of_invariantIndex`, Part I holds given
`ContinuousRegressiveConstant`, `HasInvariantGoodIndex`, and `IncomparableImpliesConstant`.  ⚠️ Of
these, the first two concern the *regressive* core, which is a **KNOWN Slaman–Steel theorem** (so this
route is *sufficient* but unnecessary — prefer `partI_of_slamanSteel_incomparable`).  The **only
genuinely-open** input is `IncomparableImpliesConstant` (cone uniformization / Posner–Robinson). -/
theorem partI_of_invariantIndex_and_incomparable (hTD : TuringDeterminacy fun _ => True)
    (hcont : ContinuousRegressiveConstant) (hidx : HasInvariantGoodIndex)
    (hincomp : IncomparableImpliesConstant) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
      ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_cores hTD (regressiveCore_of_invariantIndex hTD hcont hidx) hincomp

#print axioms comparability_on_cone
#print axioms partI_of_cores
#print axioms exists_uniform_index_on_cone
#print axioms regressiveImpliesConstant_of_slamanSteel
#print axioms partI_of_slamanSteel_incomparable
#print axioms counterexample_incomparable_to_argument
#print axioms partI_iff_incomparable
#print axioms continuousOnCone_of_invariantIndex
#print axioms regressiveCore_of_invariantIndex
#print axioms partI_of_invariantIndex_and_incomparable

end Martin
