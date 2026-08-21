/-
**Part 1 of Martin's conjecture, recast into two clean inputs.**

Combining the two threads:

* `MartinDichotomy` (`MartinDichotomy.lean`) — the *determinacy* input: every set
  contains a pointed perfect tree or its complement contains a cone (its invariant
  case is proved; the general case is Martin's Lemma 2.3).
* **no escaping invariant function is incomparable to a fixed degree on a cone**
  (`EscapingDichotomy.lean`) — the *class-specific* input, which by
  `escapingMP_iff_no_fixedIncomparable` is exactly "escaping ⟹ measure-preserving".

Part 1 follows from these two.  This is the sharpest current statement of what
Part 1 rests on: one determinacy dichotomy, and one incomparability-avoidance
property of escaping functions.
-/
import MartinsConjecture.MartinDichotomy
import MartinsConjecture.EscapingDichotomy

open scoped Computability
open Cantor

namespace Martin

/-- **Under `MartinPPT`, measure-preservation is exactly above-the-identity** for
invariant functions (Theorem 3.4 and its converse).  So the "not above the
identity" clause of the counterexample profile (`escaping_nonMP_profile`) is
equivalent to failing measure-preservation — the profile is tight. -/
theorem mp_iff_aboveId_of_martinPPT (hM : MartinPPT) {F : (ℕ → Bool) → ℕ → Bool}
    (hF : TuringInvariant F) :
    MeasurePreserving F ↔ AboveIdOnCone F :=
  ⟨fun hmp => measurePreservingAboveId_of_martinPPT hM hF hmp, aboveId_measurePreserving⟩

/-- **Part 1 from the two inputs.**  The perfect-set dichotomy (determinacy) and
the incomparability-avoidance of escaping functions (class-specific) together give
Part 1: every Turing-invariant function is constant on a cone or above the
identity on a cone. -/
theorem partI_of_dichotomy_noFixedIncomparable
    (h : MartinDichotomy) (hTD : TuringDeterminacy fun _ => True)
    (hni : ∀ F, TuringInvariant F → Escaping F → ∀ Z, ¬ IncomparableToFixed F Z) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_dichotomy_escaping h hTD
    ((escapingMP_iff_no_fixedIncomparable hTD).mpr hni)

#print axioms partI_of_dichotomy_noFixedIncomparable

end Martin
