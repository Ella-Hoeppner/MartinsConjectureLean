/-
**The order-preserving branch of Part 1 rests on exactly ONE open lemma.**

`OrderPreservingCase.lean` reduces Part 1 for order-preserving functions to two named hypotheses:
`MeasurePreservingAboveId` (Theorem 3.4) and `AvoidingImpliesConstant` (the Groszek–Slaman value-side
perfect-set coding).  The first is now discharged from determinacy via `MartinPPT`
(`measurePreservingAboveId_of_martinPPT`).  Here we show the second is **equivalent** (under Turing
determinacy) to the isolated coding statement `OrderPreservingUncountableCofinal`
(`CounterexampleConstraints.lean`): an order-preserving invariant function with uncountable range has
cofinal range.  So the two names are one lemma, and the entire order-preserving case of Part 1 rests on
exactly this single, transparently-open coding statement.

(Confirms — on `main`, against the current `MartinPPT`-discharged machinery — the finding of the
order-preserving-coding investigation: order-preservation + uncountability are provably insufficient by
themselves; the coding genuinely needs invariance + perfect-set forcing.  See `ATTACK.md`.)
-/
import MartinsConjecture.CounterexampleConstraints

open scoped Computability
open Cantor

namespace Martin

/-- **`AvoidingImpliesConstant` and `OrderPreservingUncountableCofinal` are equivalent** (under Turing
determinacy).  Both are the Lutz–Siskind value-side coding step, stated dually: "an order-preserving
function whose range avoids a cone is constant" vs. "an order-preserving invariant function with
uncountable range is cofinal."  `→`: a non-constant such `F` has uncountable range
(`nonconstant_values_uncountable`), so is cofinal, so it cannot avoid any cone.  `←`: by the elementary
dichotomy `F` is measure-preserving (⟹ cofinal) or avoiding; avoiding ⟹ constant ⟹ countable range,
contradicting uncountability. -/
theorem uncountableCofinal_iff_avoiding (hTD : TuringDeterminacy fun _ => True) :
    OrderPreservingUncountableCofinal ↔ AvoidingImpliesConstant := by
  constructor
  · intro hUC F hop havoid
    by_contra hnc
    have huncount := nonconstant_values_uncountable hTD hop.turingInvariant hnc
    have hcof := hUC F hop hop.turingInvariant huncount
    obtain ⟨Z₀, hZ₀⟩ := havoid
    obtain ⟨X, hX⟩ := hcof Z₀
    exact hZ₀ X hX
  · intro hAvoid F hop hinv huncount Z
    rcases orderPreserving_measurePreserving_or_avoids hop with hmp | havoid
    · exact (orderPreserving_mp_iff_rangeCofinal hop).mp hmp Z
    · exfalso
      obtain ⟨C, hC⟩ := hAvoid F hop havoid
      exact huncount (fun _ => C) (hC.imp fun _ hb X hX => ⟨0, hb X hX⟩)

/-- **The order-preserving case of Part 1 rests on exactly one open lemma.**  Given `MartinPPT` (which
discharges Theorem 3.4) and the single coding statement `OrderPreservingUncountableCofinal`, Part 1 holds
for every order-preserving function — and by `uncountableCofinal_iff_avoiding` that coding statement is
interchangeable with `AvoidingImpliesConstant`, so there is genuinely only one remaining open ingredient
in this branch. -/
theorem partI_orderPreserving_of_uncountableCofinal (hTD : TuringDeterminacy fun _ => True)
    (hM : MartinPPT) (hcoding : OrderPreservingUncountableCofinal) :
    ∀ F, OrderPreserving F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_orderPreserving_of_lemmas
    (fun _ hF hmp => measurePreservingAboveId_of_martinPPT hM hF hmp)
    ((uncountableCofinal_iff_avoiding hTD).mp hcoding)

#print axioms uncountableCofinal_iff_avoiding
#print axioms partI_orderPreserving_of_uncountableCofinal

end Martin
