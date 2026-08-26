/-
**Measure-theoretic attack on the RK-rigidity frontier, via the Church–Kleene ordinal.**

The sole open content of Part 1 is `escaping ⟹ MP`, equivalently (Lutz–Siskind) `U_M` has no nonprincipal
Rudin–Keisler predecessor on the Turing degrees but itself. This file records the ordinal side of the
*measure-theoretic* attack: since a measure-preserving function is above the identity (Thm 3.4,
`mp_iff_aboveId_of_martinPPT`) and the relativized Church–Kleene ordinal `ω₁ˣ` is monotone
(`churchKleene_mono`), **every MP function is CK-non-decreasing**. Contrapositive: a **CK-regressive**
invariant function (`ω₁^{F X} < ω₁ˣ` on a cone) is **not** measure-preserving.

So an *escaping* CK-regressive `F` witnesses `¬(escaping ⟹ MP)` — it is a counterexample-candidate. This
locates one part of the open core: the CK-regressive escaping regime (`F X` Turing-unbounded but
hyperarithmetically *simpler* than `X`), which is exactly the `ω₁`-decreasing case that the ordinal-ultrapower
engine `no_omega1_decreasing_conePreserving` cannot reach — because escaping breaks its cone-preservation
hypothesis (`F X ⊥ᵀ Z_0` for an avoided `Z_0 ≤ᵀ` base forces `F X ⊉ᵀ` base).

**Honest scope.** This is a *partial* measure-theoretic handle, NOT a solve. It (i) constrains counterexamples
on the CK-ordinal (a genuine, choice-free consequence of the pushforward — the CK ordinal is invariant, so
no representative-choosing is needed, correcting an earlier over-statement that Fodor is "fully blocked"); but
(ii) it is too coarse to close the crux: `¬MP` counterexamples need NOT be CK-regressive (a value `F X` can be
CK-*increasing* yet Turing-*incomparable* to the avoided `Z_0`), and CK-regressive escaping functions are not
ruled out here. The residual degree-level `{0,1}`-content is the inner-model-theoretic frontier (Steel/Siskind).
-/
import MartinsConjecture.ChurchKleene
import MartinsConjecture.PartIRecast
import MartinsConjecture.CounterexampleConstraints

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A measure-preserving function is Church–Kleene non-decreasing.**  `MP ⟹ above-id` (Thm 3.4), and
`X ≤ᵀ F X` gives `ω₁ˣ ≤ ω₁^{F X}` by monotonicity of the relativized Church–Kleene ordinal.  So MP functions
never *lower* the CK ordinal. -/
theorem measurePreserving_ck_nondecreasing (hM : MartinPPT) (hF : TuringInvariant F)
    (hmp : MeasurePreserving F) : OnCone (fun X => churchKleene X ≤ churchKleene (F X)) :=
  onCone_mono (fun _ hX => churchKleene_mono hX)
    ((mp_iff_aboveId_of_martinPPT hM hF).mp hmp)

/-- **A CK-regressive invariant function is NOT measure-preserving.**  If `ω₁^{F X} < ω₁ˣ` on a cone, then
`F` cannot be MP (MP forces `ω₁ˣ ≤ ω₁^{F X}`).  Combined with `escaping ⟺ ¬constant`, an escaping
CK-regressive `F` is a genuine counterexample-candidate to `escaping ⟹ MP` — the measure-theoretic
localization of (part of) the sole open core into the `ω₁`-decreasing regime. -/
theorem ck_regressive_not_measurePreserving (hM : MartinPPT) (hF : TuringInvariant F)
    (hreg : OnCone (fun X => churchKleene (F X) < churchKleene X)) : ¬ MeasurePreserving F := by
  intro hmp
  obtain ⟨B, hB⟩ := onCone_and hreg (measurePreserving_ck_nondecreasing hM hF hmp)
  have h := hB B (Cantor.le.refl B)
  exact absurd h.2 (not_le.mpr h.1)

/-- **Escaping measure-preservation forces CK-non-regression (contrapositive form).**  If `escaping ⟹ MP`
held for `F` (the sole open content, on the escaping branch), then in particular `F` is CK-non-decreasing.
So *any* measure-theoretic proof of the core must, at minimum, rule out CK-regressive escaping functions —
the `ω₁`-decreasing case with no cone-preservation.  Stated as: MP ⟹ ¬(CK-regressive on a cone). -/
theorem measurePreserving_not_ck_regressive (hM : MartinPPT) (hF : TuringInvariant F)
    (hmp : MeasurePreserving F) : ¬ OnCone (fun X => churchKleene (F X) < churchKleene X) :=
  fun hreg => ck_regressive_not_measurePreserving hM hF hreg hmp

/-- **The Church–Kleene dichotomy for any invariant function** (generalizing `regressive_omega1_dichotomy`
off the regressive hypothesis).  On a cone, either `ω₁^{F X} < ω₁ˣ` (CK-regressive) or `ω₁ˣ ≤ ω₁^{F X}`
(CK-non-decreasing).  The cone-theorem applies to the invariant set `{X : ω₁^{F X} < ω₁ˣ}`. -/
theorem ck_dichotomy (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F) :
    OnCone (fun X => churchKleene (F X) < churchKleene X) ∨
    OnCone (fun X => churchKleene X ≤ churchKleene (F X)) := by
  have hTI : TuringInvariantSet {X | churchKleene (F X) < churchKleene X} := by
    intro X Y hXY
    have hFeq : churchKleene (F X) = churchKleene (F Y) := churchKleene_invariant (hF X Y hXY)
    have hXeq : churchKleene X = churchKleene Y := churchKleene_invariant hXY
    constructor
    · intro h; rw [Set.mem_setOf_eq, ← hFeq, ← hXeq]; exact h
    · intro h; rw [Set.mem_setOf_eq, hFeq, hXeq]; exact h
  rcases cone_theorem _ hTI (hTD _ trivial hTI) with ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl ⟨W, fun X hX => hW hX⟩
  · exact Or.inr ⟨W, fun X hX => not_lt.mp (hW hX)⟩

/-- **The Church–Kleene trichotomy.**  Refining `ck_dichotomy`: on a cone, an invariant `F` is exactly one
of CK-**regressive** (`ω₁^{F X} < ω₁ˣ`), CK-**preserving** (`ω₁^{F X} = ω₁ˣ`), or CK-**increasing**
(`ω₁ˣ < ω₁^{F X}`).  For the open core (escaping `F`) these name the three sub-regimes: regressive ⟹ ¬MP
(a Part-1 refutation, `ck_regressive_not_measurePreserving`); preserving ⟹ `F X ≤_h X` on the graph, i.e.
regressive on the *hyperarithmetic* degrees — Lutz's proved territory; increasing ⟹ the graph is beyond
hyperarithmetic — the sharpest genuinely-open residue (the `ω₁`-level). -/
theorem ck_trichotomy (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F) :
    OnCone (fun X => churchKleene (F X) < churchKleene X) ∨
    OnCone (fun X => churchKleene (F X) = churchKleene X) ∨
    OnCone (fun X => churchKleene X < churchKleene (F X)) := by
  rcases ck_dichotomy hTD hF with hreg | hnd
  · exact Or.inl hreg
  · have hTI : TuringInvariantSet {X | churchKleene X < churchKleene (F X)} := by
      intro X Y hXY
      have hFeq : churchKleene (F X) = churchKleene (F Y) := churchKleene_invariant (hF X Y hXY)
      have hXeq : churchKleene X = churchKleene Y := churchKleene_invariant hXY
      constructor
      · intro h; rw [Set.mem_setOf_eq, ← hFeq, ← hXeq]; exact h
      · intro h; rw [Set.mem_setOf_eq, hFeq, hXeq]; exact h
    rcases cone_theorem _ hTI (hTD _ trivial hTI) with ⟨W, hW⟩ | ⟨W, hW⟩
    · exact Or.inr (Or.inr ⟨W, fun X hX => hW hX⟩)
    · obtain ⟨B, hB⟩ := onCone_and hnd ⟨W, fun X hX => hW hX⟩
      exact Or.inr (Or.inl ⟨B, fun X hX => le_antisymm (not_lt.mp (hB X hX).2) (hB X hX).1⟩)

/-- **The CK-decomposition of `escaping ⟹ MP`.**  Combining `ck_dichotomy` with the constraint: for an
invariant `F`, either it is CK-regressive on a cone — in which case it is automatically **not** MP
(`ck_regressive_not_measurePreserving`), so an escaping such `F` is a counterexample — or it is
CK-non-decreasing (`ω₁ˣ ≤ ω₁^{F X}`).  So `escaping ⟹ MP` reduces to exactly two tasks:
(a) rule out CK-regressive escaping functions (the `ω₁`-decreasing case, which evades
`no_omega1_decreasing_conePreserving` because `¬MP` makes the kernel non-cofinal — no cone-preserving base);
(b) prove CK-non-decreasing escaping functions are MP (the `ω₁`-preserving/increasing case).
Both remain open at the degree level; this is the measure-theoretic/ordinal *decomposition*, machine-checked. -/
theorem escaping_ck_cases (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hF : TuringInvariant F) :
    (OnCone (fun X => churchKleene (F X) < churchKleene X) ∧ ¬ MeasurePreserving F) ∨
    OnCone (fun X => churchKleene X ≤ churchKleene (F X)) :=
  (ck_dichotomy hTD hF).imp (fun h => ⟨h, ck_regressive_not_measurePreserving hM hF h⟩) id

/-- **A CK-regressive escaping function would REFUTE Martin's Conjecture Part 1.**  Since Part 1 ⟺
`escaping ⟹ MP` (`partI_iff_escapingMP`, given `MartinPPT` + the known regressive theorem), and a
CK-regressive `F` is not MP (`ck_regressive_not_measurePreserving`), any *escaping* CK-regressive invariant
`F` is a genuine counterexample: it is escaping but not measure-preserving.  This turns the CK constraint
into a **concrete disproof target** — Part 1 fails iff some invariant `F` is escaping (equivalently
non-constant) yet *lowers the Church–Kleene ordinal* on a cone. -/
theorem partI_false_of_ckRegressive_escaping (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F) (hesc : Escaping F)
    (hreg : OnCone (fun X => churchKleene (F X) < churchKleene X)) :
    ¬ (∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → ConstantOnCone G ∨ AboveIdOnCone G) := by
  intro hPartI
  exact ck_regressive_not_measurePreserving hM hF hreg
    ((partI_iff_escapingMP hTD hM hSS).mp hPartI F hF hesc)

/-- **The clean CK-disjunction on the open branch.**  Under Part 1's hypotheses, an escaping invariant `F`
is EITHER a Part-1 refutation (CK-regressive) OR CK-non-decreasing.  Equivalently: *if* Part 1 holds, then
every escaping `F` is CK-non-decreasing (`ω₁ˣ ≤ ω₁^{F X}` on a cone) — a necessary condition any proof must
route through.  Combines `escaping_ck_cases` with `partI_false_of_ckRegressive_escaping`. -/
theorem escaping_ck_nondecreasing_of_partI (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel)
    (hPartI : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → ConstantOnCone G ∨ AboveIdOnCone G)
    (hF : TuringInvariant F) (hesc : Escaping F) :
    OnCone (fun X => churchKleene X ≤ churchKleene (F X)) :=
  measurePreserving_ck_nondecreasing hM hF ((partI_iff_escapingMP hTD hM hSS).mp hPartI F hF hesc)

/-- **`F`'s values eventually land in the kernel.**  This is exactly the Lutz–Siskind / Prop 5.24
*concentration hypothesis* `{x | Cone(x) ∈ F_*U_M} ∈ F_*U_M`, translated to the kernel `BelowF`: unfolding
the pushforward, `Cone(x) ∈ F_*U_M ⟺ BelowF F x` (`x` is dominated by `F` on a cone), so the concentration
hypothesis is `F X ∈ kernel` for `U_M`-most `X`. -/
def RangeInKernel (F : (ℕ → Bool) → ℕ → Bool) : Prop := OnCone (fun X => BelowF F (F X))

/-- **MP ⟹ `RangeInKernel`** (trivial direction).  If `F` is measure-preserving the kernel is everything
(`mp_iff_belowF_univ`), so in particular every value `F X` lies in it.  **The CONVERSE is the equivalence
half of RK-rigidity** (`U_M ≤_RK V ≤_RK U_M ⟹ V = U_M`): by Lutz–Siskind Prop 5.24, the concentration
hypothesis `RangeInKernel F` forces `F_*U_M = U_M`, i.e. `F` MP — but that proof needs the perfect-set
property + "perfect ∧ countably-directed ⟹ cofinal" (Cor 4.5), and is **open** at this generality (a mere
unbounded Turing ideal need not be cofinal, so it is NOT elementary — this is exactly Siskind trichotomy
case (2), the un-excluded escape).  So `RangeInKernel ⟹ MP` is the machine-stated open equivalence half. -/
theorem mp_rangeInKernel (hmp : MeasurePreserving F) : RangeInKernel F :=
  ⟨(fun _ => false), fun X _ => (mp_iff_belowF_univ.mp hmp) (F X)⟩

/-- **Lutz–Siskind Prop 5.24** (the *proved* fragment of the equivalence half / Question 4), as a named
classical input: a non-constant invariant `F` whose pushforward satisfies the concentration hypothesis
(`RangeInKernel F`, = `{x | Cone(x) ∈ F_*U_M} ∈ F_*U_M`) is measure-preserving (`F_*U_M = U_M`).  Proved in
ZF+AD by the perfect-set property + "perfect ∧ countably-directed ⟹ cofinal"; named here pending its DST
formalization. -/
def Prop524 : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → ¬ ConstantOnCone G → RangeInKernel G → MeasurePreserving G

/-- **The equivalence half for concentrated `F`** — the fragment of Question 4 that IS proved (Prop 5.24):
`RangeInKernel F ⟹ MP F`.  With `mp_rangeInKernel` (`MP ⟹ RangeInKernel`) this gives, under `Prop524`,
`MP F ⟺ RangeInKernel F`.  **The residual open content of Q4 is exactly the NON-concentrated case** —
Siskind-trichotomy case (2), `F_*U_M` concentrating on complements of cones — the `g`-inversion / inner-model
wall.  This is *dual* to `strictHalf_of_countableFibered`: **both halves = a proved fragment + an open
residue** (Q3: countable / uncountable-cone-null fibers, combinatorial; Q4: concentrated / case-2,
inner-model). -/
theorem equivHalf_of_rangeInKernel (hP : Prop524) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hrk : RangeInKernel F) : MeasurePreserving F :=
  hP F hF hnc hrk

/-- **The equivalence-half mechanism, machine-checked (the `g`-inversion recovery).**  If an invariant `g`
"inverts" `F` up to the Martin measure — i.e. `g ∘ F` is measure-preserving (equivalently `F_*U_M ≡_RK U_M`
via `g`) — then by Thm 3.4 the composite is above the identity, so `g(F X) ≥ᵀ X` on a cone.  This is exactly
the stall point of the *equivalence half* of RK-rigidity (`U_M ≤_RK V ≤_RK U_M ⟹ V = U_M`): the recovery
`g(F X) ≥ᵀ X` gives **no** comparison between `X` and `F X` itself, because the arbitrary invariant `g` is
free to *lift* a sideways value `F X ⊥ᵀ Z_0` up above `Z_0`.  So `∃ g, g∘F` MP does NOT force `F` MP — that
residue is the equivalence half (Lutz–Siskind Prop 5.24 / Siskind ultrapower), distinct from the strict half
(Marks's conjecture).  What IS machine-checked here is the recovery inequality; the gap is that it is not a
`≤ᵀ`-reduction. -/
theorem gcomp_mp_recovers (hM : MartinPPT) {g : (ℕ → Bool) → ℕ → Bool} (hg : TuringInvariant g)
    (hF : TuringInvariant F) (hmp : MeasurePreserving (fun X => g (F X))) :
    OnCone (fun X => X ≤ₜ g (F X)) :=
  (mp_iff_aboveId_of_martinPPT hM (fun X Y hXY => hg _ _ (hF X Y hXY))).mp hmp

/-- `F` is **dominated-invertible**: some invariant `g` recovers a degree `≥ᵀ X` from `F X`, on a cone. -/
def DominatedInvertible (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ g, TuringInvariant g ∧ OnCone (fun X => X ≤ₜ g (F X))

/-- The **strict half** of RK-rigidity for `F` (`U_M ≤_RK F_*U_M`): some invariant `g` inverts `F` up to the
Martin measure, i.e. `g ∘ F` is measure-preserving (`(g∘F)_*U_M = U_M`, so `g_*(F_*U_M) = U_M`). -/
def StrictHalfFor (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ g, TuringInvariant g ∧ MeasurePreserving (fun X => g (F X))

/-- **The strict half ⟺ dominated-invertibility** (given `MartinPPT`).  `U_M ≤_RK F_*U_M` holds iff some
invariant `g` dominates the identity through `F` (`X ≤ᵀ g(F X)` on a cone).  (⟸) is `aboveId ⟹ MP`
(`aboveId_measurePreserving`); (⟹) is `gcomp_mp_recovers`.  So the strict half's *entire* open content is:
**construct a dominating inverse `g`** — which Marks's conjecture supplies via a pointed perfect tree on which
`F` is injective (recover the branch from `F`-value + tree, then join).  For the incomparable core (`F X ⊥ᵀ X`)
`g` canNOT be a Turing reduction (`F X` does not compute `X`), so it must be a genuinely non-effective
invariant map — exactly the pointed-tree recovery, and exactly the strict half that Marks's conjecture buys. -/
theorem strictHalf_iff_dominatedInvertible (hM : MartinPPT) (hF : TuringInvariant F) :
    StrictHalfFor F ↔ DominatedInvertible F := by
  constructor
  · rintro ⟨g, hg, hmp⟩; exact ⟨g, hg, gcomp_mp_recovers hM hg hF hmp⟩
  · rintro ⟨g, hg, hdom⟩; exact ⟨g, hg, aboveId_measurePreserving hdom⟩

/-- **Part 1 splits EXACTLY into its two Church–Kleene branches.**  Given `MartinPPT` + the known
regressive theorem, Martin's Conjecture Part 1 is equivalent to the conjunction of:
(1) **no** invariant escaping `F` is CK-regressive (`ω₁^{F X} < ω₁ˣ` on a cone) — the *disproof* branch is
empty; and
(2) every invariant escaping CK-non-decreasing `F` is measure-preserving — the *proof* obligation.
This is the complete CK-characterization: the sole open content of Part 1, partitioned by the position of
`ω₁^{F X}` relative to `ω₁ˣ`.  (In the presence of (1), (2)'s CK-hypothesis is automatic, so (2) alone
carries the weight — but the split names precisely the two independent tasks.) -/
theorem partI_iff_ck_split (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) :
    (∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → ConstantOnCone G ∨ AboveIdOnCone G)
      ↔ ((∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → Escaping G →
            OnCone (fun X => churchKleene (G X) < churchKleene X) → False)
          ∧ (∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G → Escaping G →
            OnCone (fun X => churchKleene X ≤ churchKleene (G X)) → MeasurePreserving G)) := by
  constructor
  · intro hPartI
    refine ⟨fun G hG hesc hreg => partI_false_of_ckRegressive_escaping hTD hM hSS hG hesc hreg hPartI,
      fun G hG hesc _ => (partI_iff_escapingMP hTD hM hSS).mp hPartI G hG hesc⟩
  · rintro ⟨h1, h2⟩
    refine (partI_iff_escapingMP hTD hM hSS).mpr (fun G hG hesc => ?_)
    rcases ck_dichotomy hTD hG with hreg | hnd
    · exact absurd (h1 G hG hesc hreg) not_false
    · exact h2 G hG hesc hnd

#print axioms measurePreserving_ck_nondecreasing
#print axioms ck_regressive_not_measurePreserving
#print axioms ck_dichotomy
#print axioms ck_trichotomy
#print axioms escaping_ck_cases
#print axioms partI_false_of_ckRegressive_escaping
#print axioms escaping_ck_nondecreasing_of_partI
#print axioms partI_iff_ck_split
#print axioms gcomp_mp_recovers
#print axioms mp_rangeInKernel
#print axioms strictHalf_iff_dominatedInvertible
#print axioms equivHalf_of_rangeInKernel

end Martin
