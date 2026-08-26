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

#print axioms measurePreserving_ck_nondecreasing
#print axioms ck_regressive_not_measurePreserving
#print axioms ck_dichotomy
#print axioms escaping_ck_cases
#print axioms partI_false_of_ckRegressive_escaping
#print axioms escaping_ck_nondecreasing_of_partI

end Martin
