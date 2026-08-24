/-
**End-to-end capstones for the Martin-game branch: `MartinPPT` discharged.**

`MartinGameCode.gameCodeBelow` proves `codeGame σ ≤ᵀ σ`, so `martinPPT_of_gameDeterminacy`
supplies `MartinPPT` from *only* determinacy of the Martin games.  Feeding that into the
sharpest open-content statements (`partI_iff_escapingMP_of_martinPPT`,
`partI_iff_pushforward_of_martinPPT`) removes the `MartinPPT` hypothesis from them, leaving
statements of Part 1 that rest on just two inputs: **determinacy** (a standard set-theoretic
hypothesis, threaded explicitly — never axiomatized) and the single genuinely-open
implication **escaping ⟹ measure-preserving**.
-/
import MartinsConjecture.MartinGameCode
import MartinsConjecture.MeasurePreservingFilter
import MartinsConjecture.CounterexampleConstraints

open scoped Computability
open Cantor

namespace Martin

/-- **Part 1 ⟺ `escaping ⟹ MP`, on determinacy alone.**  Combining the Martin game
(`martinPPT_of_gameDeterminacy`, which discharges `MartinPPT`) with
`partI_iff_escapingMP_of_martinPPT`: given determinacy of the Martin games and Turing
determinacy, Part 1 of Martin's conjecture is *equivalent* to "every escaping invariant
function is measure-preserving".  Everything else — Martin's Lemma 2.3, Theorem 3.4, the
whole reduction — is machine-checked; this pins the entire remaining content of Part 1 to
one implication. -/
theorem partI_iff_escapingMP_of_gameDeterminacy
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True) :
    (∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) ↔
      (∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :=
  partI_iff_escapingMP_of_martinPPT hTD (martinPPT_of_gameDeterminacy hdet)

/-- **Part 1 in Martin-measure language, on determinacy alone.**  With `MartinPPT`
discharged by the game, `partI_iff_pushforward_of_martinPPT` becomes: given determinacy of
the Martin games, Part 1 holds iff every invariant `F` pushes the Martin measure to a
principal degree-class (constant) or to a refinement of the measure (above the identity).
The machine-checked ultrafilter/Rudin–Keisler reading of Part 1, resting only on
determinacy. -/
theorem partI_iff_pushforward_of_gameDeterminacy
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    (∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F) ↔
      (∀ F, TuringInvariant F →
        (∃ C, {Y | Y ≡ₜ C} ∈ Filter.map F coneFilter) ∨
          Filter.map F coneFilter ≤ coneFilter) :=
  partI_iff_pushforward_of_martinPPT (martinPPT_of_gameDeterminacy hdet)

/-- **Lutz–Siskind's Theorem 3.4, from determinacy alone.**  A Turing-invariant
measure-preserving function is above the identity on a cone — now with *no* `MartinPPT` or
`GroszekSlaman` hypothesis: the Martin game supplies `MartinPPT` (`martinPPT_of_gameDeterminacy`),
which supplies the Groszek–Slaman inverting-tree construction (`groszekSlaman_of_martinPPT`),
which yields Theorem 3.4.  The entire §§2–3 pointed-perfect-tree pipeline of Lutz–Siskind is
machine-checked, resting only on determinacy of the Martin games. -/
theorem measurePreservingAboveId_of_gameDeterminacy
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) : MeasurePreservingAboveId :=
  measurePreservingAboveId_of_groszekSlaman'
    (groszekSlaman_of_martinPPT (martinPPT_of_gameDeterminacy hdet))

/-- **Part 1 for order-preserving functions, on determinacy + the coding step.**  With
`MartinPPT` discharged by the game, `partI_orderPreserving_of_coding` needs only determinacy of
the Martin games, Turing determinacy, and the Groszek–Slaman–Kihara perfect-set coding
(`OrderPreservingUncountableCofinal`): every order-preserving invariant function is constant on
a cone or above the identity on a cone.  So the order-preserving branch of Part 1 (Lutz–Siskind)
now rests on exactly determinacy plus that one atomic coding statement. -/
theorem partI_orderPreserving_of_gameDeterminacy
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hcoding : OrderPreservingUncountableCofinal) :
    ∀ F, OrderPreserving F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_orderPreserving_of_coding hTD (martinPPT_of_gameDeterminacy hdet) hcoding

#print axioms partI_iff_escapingMP_of_gameDeterminacy
#print axioms partI_iff_pushforward_of_gameDeterminacy
#print axioms measurePreservingAboveId_of_gameDeterminacy
#print axioms partI_orderPreserving_of_gameDeterminacy

end Martin
