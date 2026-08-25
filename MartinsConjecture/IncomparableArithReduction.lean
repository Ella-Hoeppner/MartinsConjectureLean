/-
**Reducing the incomparable core: one of its four sub-cases falls to an arithmetic-regressive lemma.**

`RegressiveJumpDecomp.incomparableCore_of_cases` splits the sole open Part-1 core (`F X ⊥ᵀ X` on a cone
⟹ constant) into four sub-cases by the *arithmetic* position of `F X` vs `X`:
`(An/Bn) × (Am/Bm)`, where `Bm`: `F X ≤ᵀ X^(k)` (some fixed `k`; `F X ≤ₐ X`) and `An`:
`X ≰ᵀ (F X)^(k)` for all `k` (`X ≰ₐ F X`).

The `AnBm` sub-case is exactly *`F X` arithmetically-strictly-below `X`, yet Turing-incomparable*
(`F X <ₐ X`, `F X ⊥ᵀ X`).  This is `arithmetic`-regressive, so it falls to the **arithmetic-degrees**
analogue of the Slaman–Steel regressive theorem — a strictly weaker input than the full open core.
Isolating it reduces the open incomparable core from **four** sub-cases to **three** (`AnAm`, `BnAm`,
`BnBm`) plus this one named arithmetic lemma.  (The arithmetic-regressive theorem's status is genuinely
open here — Lutz settled the *hyperarithmetic* degrees; the arithmetic degrees are intermediate — so it
is a named `Prop`, NOT claimed proved.  This is a structural reduction of the open problem, honestly
conditional.)
-/
import MartinsConjecture.RegressiveJumpDecomp
import MartinsConjecture.Reduction

open scoped Computability
open Cantor

namespace Martin

/-- **Strict arithmetic-regressive ⟹ constant** (a named, genuinely-open input).  A *Turing-invariant*
`F` with `F X ≤ₐ X` but `X ≰ₐ F X` on a cone — `F X` arithmetically strictly below `X` — is constant on a
cone.  This is the `AnBm` sub-case of the incomparable core rephrased in arithmetic-reducibility terms.
NOTE: it is a *Turing*-invariant statement, hence *analogous to* but NOT literally the arithmetic-degrees
Martin conjecture (which concerns `≡ₐ`-invariant functions on `D_a`); Turing-invariance does not imply
`≡ₐ`-invariance.  See `MARTIN_PART1_OPEN_CONTENT.md` §3-4. -/
def StrictArithRegressiveConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => arithLe (F X) X ∧ ¬ arithLe X (F X)) → ConstantOnCone F

/-- **The `AnBm` sub-case of the incomparable core falls to `StrictArithRegressiveConstant`.**  On the
joint cone, `Bm` gives `F X ≤ₐ X` (with the fixed jump level `k`) and `An` gives `X ≰ₐ F X`, i.e.
`F X <ₐ X`; the arithmetic-regressive lemma then forces constancy. -/
theorem incomparable_AnBm_of_strictArithRegressive (h : StrictArithRegressiveConstant)
    (F : (ℕ → Bool) → ℕ → Bool) (hF : TuringInvariant F)
    (hAn : OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (F X)))
    (hBm : ∃ k, OnCone (fun X => F X ≤ₜ Cantor.jump^[k] X)) : ConstantOnCone F := by
  obtain ⟨k, hk⟩ := hBm
  obtain ⟨B, hB⟩ := onCone_and hk hAn
  exact h F hF ⟨B, fun X hX => ⟨⟨k, (hB X hX).1⟩, fun ⟨m, hm⟩ => (hB X hX).2 m hm⟩⟩

/-- **The incomparable core reduces to THREE sub-cases plus the arithmetic-regressive lemma.**  Given
handlers for the `AnAm`, `BnAm`, `BnBm` sub-cases and `StrictArithRegressiveConstant` (which discharges
`AnBm`), the full incomparable core follows.  So one of the four jump-distance sub-cases of the sole open
Part-1 core is not independently open — it is subsumed by the arithmetic-degrees regressive theorem. -/
theorem incomparableCore_of_three_cases_and_arith (hTD : TuringDeterminacy fun _ => True)
    (harith : StrictArithRegressiveConstant)
    (hAnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (G X)) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnBm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G) :
    IncomparableConstant :=
  incomparableCore_of_cases hTD hAnAm
    (fun G hG _hinc hAn hBm => incomparable_AnBm_of_strictArithRegressive harith G hG hAn hBm)
    hBnAm hBnBm

/-- **Part 1 of Martin's conjecture, structured to its sharpest open residue.**  Combining the KNOWN
Slaman–Steel regressive theorem (`RegressiveSlamanSteel`) with the incomparable-core reduction: Part 1
holds given (i) `RegressiveSlamanSteel` (known), (ii) `StrictArithRegressiveConstant` (the
arithmetic-degrees regressive lemma — a strictly weaker input than the open core, discharging the `AnBm`
sub-case), and (iii) handlers for the three remaining jump-distance sub-cases (`AnAm` arithmetically-
incomparable, `BnAm` arithmetically-above, `BnBm` arithmetically-equivalent).  So the *entire* open
content of Part 1 is now: an arithmetic-regressive theorem plus three sharp, arithmetically-classified
sub-cases — a strictly finer target than "the incomparable core." -/
theorem partI_of_three_cases_and_arith (hTD : TuringDeterminacy fun _ => True)
    (hSS : RegressiveSlamanSteel) (harith : StrictArithRegressiveConstant)
    (hAnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (G X)) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnAm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G)
    (hBnBm : ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
      OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
      (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
      (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_slamanSteel_incomparable hTD hSS
    (incomparableCore_of_three_cases_and_arith hTD harith hAnAm hBnAm hBnBm)

/-! ### The four-way decomposition is lossless -/

/-- The `AnAm` sub-case (both arithmetically incomparable) of the incomparable core. -/
def SubcaseAnAm : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (G X)) →
    OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G

/-- The `AnBm` sub-case (`G X <ₐ X`). -/
def SubcaseAnBm : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (G X)) →
    (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G

/-- The `BnAm` sub-case (`X <ₐ G X`). -/
def SubcaseBnAm : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
    OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G

/-- The `BnBm` sub-case (`G X ≡ₐ X`). -/
def SubcaseBnBm : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (G X))) →
    (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G

/-- **The four-way jump-distance decomposition of the incomparable core is LOSSLESS.**  The incomparable
core is *equivalent* to the conjunction of its four arithmetically-typed sub-cases — the split loses
nothing in either direction (`⟸` by `incomparableCore_of_cases`; `⟹` because each sub-case is the core
with extra hypotheses). Parallels `CoreAnalysis.partII_iff_cores`. -/
theorem incomparableConstant_iff_four_subcases (hTD : TuringDeterminacy fun _ => True) :
    IncomparableConstant ↔ (SubcaseAnAm ∧ SubcaseAnBm ∧ SubcaseBnAm ∧ SubcaseBnBm) := by
  constructor
  · intro h
    exact ⟨fun G hG hinc _ _ => h G hG hinc, fun G hG hinc _ _ => h G hG hinc,
           fun G hG hinc _ _ => h G hG hinc, fun G hG hinc _ _ => h G hG hinc⟩
  · rintro ⟨hAnAm, hAnBm, hBnAm, hBnBm⟩
    exact incomparableCore_of_cases hTD hAnAm hAnBm hBnAm hBnBm

#print axioms incomparable_AnBm_of_strictArithRegressive
#print axioms incomparableCore_of_three_cases_and_arith
#print axioms partI_of_three_cases_and_arith
#print axioms incomparableConstant_iff_four_subcases

end Martin
