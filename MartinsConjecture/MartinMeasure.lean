/-
Martin measure as a countably complete ultrafilter, and the σ-pigeonhole.

`TuringInvariantSet` packages the invariance hypothesis of the cone theorem;
`TuringDeterminacy` is the determinacy-of-all-invariant-games hypothesis
(true under AD; its restriction to Borel sets is a ZFC theorem by Martin's
Borel determinacy, not yet formalized — see LEDGER).  Under it, "contains a
cone" behaves like a countably complete ultrafilter on invariant sets:

* dichotomy (`cone_theorem`, from `ConeTheorem.lean`),
* closure under countable intersection (`onCone_forall`), and — the workhorse —
* **the σ-pigeonhole** (`exists_onCone_of_cover`): if countably many
  invariant determined sets cover a cone, one of them contains a cone.

The pigeonhole is the standard first move of every known attack on Martin's
conjecture (index stabilization, comparability trichotomy, …); see
`Reduction.lean`.
-/
import MartinsConjecture.RegularChain
import MartinsConjecture.ConeTheorem

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- A set of reals is Turing invariant if membership depends only on the
Turing degree. -/
def TuringInvariantSet (A : Set (ℕ → Bool)) : Prop :=
  ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A)

/-- **Turing determinacy** (for a class of sets given by a predicate `Γ`):
every Turing-invariant set in the class is determined.  With `Γ := fun _ => True`
this follows from AD (inconsistent with choice, so only ever a *hypothesis*
here); with `Γ := MeasurableSet` it is a ZFC theorem (Martin's Borel
determinacy) that is not yet formalized in Lean/Mathlib. -/
def TuringDeterminacy (Γ : Set (ℕ → Bool) → Prop) : Prop :=
  ∀ A : Set (ℕ → Bool), Γ A → TuringInvariantSet A → GameDetermined A

/-- **The σ-pigeonhole for Martin measure.**  If countably many
Turing-invariant determined sets cover a cone, then one of them contains a
cone.  (Countable completeness + dichotomy of the cone filter.) -/
theorem exists_onCone_of_cover {Γ : Set (ℕ → Bool) → Prop}
    (hTD : TuringDeterminacy Γ) {A : ℕ → Set (ℕ → Bool)}
    (hΓ : ∀ n, Γ (A n)) (hA : ∀ n, TuringInvariantSet (A n))
    {W : ℕ → Bool} (hcover : cone W ⊆ ⋃ n, A n) :
    ∃ n, OnCone (· ∈ A n) := by
  by_contra hno
  have hno' : ∀ n, ¬ OnCone (· ∈ A n) := fun n h => hno ⟨n, h⟩
  -- No `A n` contains a cone, so each complement contains a cone.
  have hcompl : ∀ n, ∃ Y, cone Y ⊆ (A n)ᶜ := by
    intro n
    rcases cone_theorem (A n) (hA n) (hTD (A n) (hΓ n) (hA n)) with ⟨Y, hY⟩ | h
    · exact absurd ⟨Y, fun X hX => hY hX⟩ (hno' n)
    · exact h
  choose Y hY using hcompl
  -- A single point above `W` and above every `Y n`.
  set X₀ : ℕ → Bool := join W (bigJoin Y) with hX₀
  have hXW : X₀ ∈ cone W := left_le_join W (bigJoin Y)
  have hXn : ∀ n, X₀ ∈ cone (Y n) :=
    fun n => (le_bigJoin Y n).trans (right_le_join W (bigJoin Y))
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hXW)
  exact hY n (hXn n) hn

end Martin
