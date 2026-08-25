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

/-- **A counterexample's value escapes the join with its argument and any fixed oracle.**  For an
incomparable `F` (`F X ⊥ᵀ X` on a cone) and any fixed `Z`, `F X ≰ᵀ X ⊕ Z` on a cone: above `Z` we have
`X ⊕ Z ≡ᵀ X`, so `F X ≤ᵀ X ⊕ Z` would give `F X ≤ᵀ X`, contradicting incomparability.  This is *stronger*
than escaping (`F X ≰ᵀ Z`): a counterexample's value is not even computable from its argument together
with any fixed oracle — it is "generic over `X` relative to every fixed `Z`".  Equivalently: a
counterexample is not *relative-regressive* (`F X ≤ᵀ X ⊕ Z` for a fixed `Z`), a class otherwise settled by
`RegressiveSlamanSteel` (relative-regressive ⟹ regressive on the cone above `Z`). -/
theorem incomparable_not_below_argJoin {F : (ℕ → Bool) → ℕ → Bool}
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (Z : ℕ → Bool) :
    OnCone (fun X => ¬ F X ≤ₜ Cantor.join X Z) := by
  obtain ⟨B, hB⟩ := hinc
  refine ⟨Cantor.join B Z, fun X hX hle => ?_⟩
  have hZX : Z ≤ₜ X := (Cantor.right_le_join B Z).trans hX
  have hBX : B ≤ₜ X := (Cantor.left_le_join B Z).trans hX
  exact (hB X hBX).1 (hle.trans (Cantor.join_le (Cantor.le.refl X) hZX))

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

/-! ### The primary two-way divide: `F X ≤ₐ X` versus `F X ≰ₐ X` -/

/-- **`Bm` half** — the arithmetically-bounded region `F X ≤ₐ X` (= `AnBm ∪ BnBm`): an incomparable `F`
whose value is arithmetic in its argument is constant. -/
def ArithBelowHalf : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    (∃ k, OnCone (fun X => G X ≤ₜ Cantor.jump^[k] X)) → ConstantOnCone G

/-- **`Am` half** — the arithmetically-escaping region `F X ≰ₐ X` (= `BnAm ∪ AnAm`): an incomparable `F`
whose value is *not* arithmetic in its argument is constant.  (Both faces here produce a transfinite-rank
Part-2 object via the graph — see `BnAmPartTwo.am_graph_not_finite_jump`.) -/
def ArithEscapingHalf : Prop :=
  ∀ G : (ℕ → Bool) → ℕ → Bool, TuringInvariant G →
    OnCone (fun X => ¬ G X ≤ₜ X ∧ ¬ X ≤ₜ G X) →
    OnCone (fun X => ∀ k, ¬ G X ≤ₜ Cantor.jump^[k] X) → ConstantOnCone G

/-- **The incomparable core splits LOSSLESSLY by the single arithmetic comparison `F X ≤ₐ X`.**  This is
the *primary* divide (one dichotomy, `jump_dichotomy_dual`), coarser than the four-way split: the `Bm`
half (`F X ≤ₐ X`, arithmetic-regressive-or-equal) refines into `AnBm ∪ BnBm`, and the `Am` half
(`F X ≰ₐ X`) into `BnAm ∪ AnAm`. -/
theorem incomparableConstant_iff_arith_halves (hTD : TuringDeterminacy fun _ => True) :
    IncomparableConstant ↔ (ArithBelowHalf ∧ ArithEscapingHalf) := by
  constructor
  · intro h
    exact ⟨fun G hG hinc _ => h G hG hinc, fun G hG hinc _ => h G hG hinc⟩
  · rintro ⟨hBm, hAm⟩ G hG hinc
    rcases jump_dichotomy_dual hTD hG with hAmc | hBmc
    · exact hAm G hG hinc hAmc
    · exact hBm G hG hinc hBmc

/-- **The `Bm` half reduces to the arithmetic regressive theorem plus the single native `BnBm` handler.**
On the arithmetically-bounded region `F X ≤ₐ X`, the `An`/`Bn` dichotomy (`regressive_jump_dichotomy`)
splits into `AnBm` (`F X <ₐ X`, discharged by `StrictArithRegressiveConstant` — note incomparability is not
even needed there) and `BnBm` (`F X ≡ₐ X`). So `ArithBelowHalf` needs exactly one *recognizable* open
theorem and the one genuinely-native sub-case. -/
theorem arithBelowHalf_of_cases (hTD : TuringDeterminacy fun _ => True)
    (harith : StrictArithRegressiveConstant) (hBnBm : SubcaseBnBm) : ArithBelowHalf := by
  intro G hG hinc hBm
  rcases regressive_jump_dichotomy hTD hG with hAn | hBn
  · exact incomparable_AnBm_of_strictArithRegressive harith G hG hAn hBm
  · exact hBnBm G hG hinc hBn hBm

/-- **Consequently: the incomparable core = arithmetic-regressive theorem + `BnBm` handler + `Am` half.**
Combining `incomparableConstant_iff_arith_halves` with `arithBelowHalf_of_cases`. The two "recognizable"
inputs are `StrictArithRegressiveConstant` (Part-1 method) and `ArithEscapingHalf` (Part-2-flavoured via
the graph); the single genuinely Turing-specific residue is `SubcaseBnBm`. -/
theorem incomparableConstant_of_arith_bnBm_escaping (hTD : TuringDeterminacy fun _ => True)
    (harith : StrictArithRegressiveConstant) (hBnBm : SubcaseBnBm) (hAm : ArithEscapingHalf) :
    IncomparableConstant :=
  (incomparableConstant_iff_arith_halves hTD).mpr ⟨arithBelowHalf_of_cases hTD harith hBnBm, hAm⟩

#print axioms arithBelowHalf_of_cases
#print axioms incomparableConstant_of_arith_bnBm_escaping
#print axioms incomparableConstant_iff_arith_halves
#print axioms incomparable_not_below_argJoin
#print axioms incomparable_AnBm_of_strictArithRegressive
#print axioms incomparableCore_of_three_cases_and_arith
#print axioms partI_of_three_cases_and_arith
#print axioms incomparableConstant_iff_four_subcases

end Martin
