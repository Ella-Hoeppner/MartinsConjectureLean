/-
First discharged instances of the Turing-determinacy hypothesis.

Everything in the attack files is conditional on `TuringDeterminacy Γ`.  Here
the hypothesis is *proved* for the bottom of the hierarchy: open and closed
invariant sets.  The reason is the topological triviality theorem
(`eq_univ_of_isOpen_turingInvariant`): an open invariant set is `∅` or
everything, and both extremes are trivially determined (player II wins the
empty payoff with any strategy; player I wins the full payoff with any
strategy).

These instances are degenerate — that is precisely the content of
topological triviality — but they make the framework's conditional theorems
unconditional at the clopen level, and they are the pattern for the real
future target: `TuringDeterminacy MeasurableSet` via (a formalization of)
Martin's Borel determinacy.
-/
import MartinsConjecture.MartinMeasure
import MartinsConjecture.TopologicalTriviality

open scoped Computability
open OracleCode Cantor

namespace Martin

theorem gameDetermined_empty : GameDetermined (∅ : Set (ℕ → Bool)) :=
  Or.inr ⟨fun _ => false, fun _ h => h⟩

theorem gameDetermined_univ : GameDetermined (Set.univ : Set (ℕ → Bool)) :=
  Or.inl ⟨fun _ => false, fun _ => Set.mem_univ _⟩

/-- **Turing determinacy holds for open sets** — via topological triviality:
an open invariant set is empty or everything. -/
theorem turingDeterminacy_isOpen : TuringDeterminacy IsOpen := by
  intro A hA hTI
  rcases A.eq_empty_or_nonempty with h | h
  · rw [h]
    exact gameDetermined_empty
  · rw [eq_univ_of_isOpen_turingInvariant hA hTI h]
    exact gameDetermined_univ

/-- **Turing determinacy holds for closed sets.** -/
theorem turingDeterminacy_isClosed : TuringDeterminacy IsClosed := by
  intro A hA hTI
  have hTIc : TuringInvariantSet Aᶜ := fun X Y h => not_congr (hTI X Y h)
  rcases Aᶜ.eq_empty_or_nonempty with h | h
  · have : A = Set.univ := by
      rw [← Set.compl_empty, ← h, compl_compl]
    rw [this]
    exact gameDetermined_univ
  · have : A = ∅ := by
      rw [← compl_compl A,
        eq_univ_of_isOpen_turingInvariant hA.isOpen_compl hTIc h, Set.compl_univ]
    rw [this]
    exact gameDetermined_empty

#print axioms turingDeterminacy_isOpen
#print axioms turingDeterminacy_isClosed

end Martin
