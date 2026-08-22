/-
**A new decomposition of the regressive core, by jump-distance.**

The regressive core (`F X <ᵀ X` on a cone ⟹ constant) is exactly the statement that
the cone measure is *normal* with respect to `≥ᵀ`-regression.  The standard Fodor
argument fails because `≥ᵀ` is **not well-founded**.  But every Turing degree has only
**countably many predecessors**, which lets a σ-pigeonhole run on the *jump-distance*
`n(X) = least n with X ≤ᵀ (F X)^(n)`.  This function is degree-invariant and
`ℕ ∪ {∞}`-valued, so it partitions any cone into countably many invariant pieces, and
`exists_onCone_of_cover` forces one to contain a cone:

* **Case B** (`n = k` finite): `X ≤ᵀ (F X)^(k)` on a cone.  Since also `F X ≤ᵀ X`
  (regressive), `X` and `F X` are **arithmetically equivalent** — `F` preserves the
  arithmetic degree while dropping the Turing degree.  This is the *finitary* case the
  σ-pigeonhole reaches.
* **Case A** (`n = ∞`): `X ≰ᵀ (F X)^(n)` for every `n` on a cone — `F X` is
  arithmetically *strictly* below `X`.  Iterating drops the arithmetic degree, entering
  the transfinite `ω₁^x` regime that Lutz (2024) handles on the *hyperarithmetic*
  degrees; there the levels are uncountable and the σ-pigeonhole cannot reach.

So this cleanly isolates *which* part of the open regressive core is finitary vs
Lutz-hyperarithmetic-hard.  The decomposition holds for **any** Turing-invariant `F`
(the regressive hypothesis only enters the arithmetic-equivalence reading of Case B).
-/
import MartinsConjecture.CantorLimit
import MartinsConjecture.MartinMeasure

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- Transport `≤ᵀ` across `≡ᵀ` on both sides. -/
private theorem transport_le {X Y A B : ℕ → Bool}
    (hXY : X ≡ₜ Y) (hAB : A ≡ₜ B) (h : X ≤ₜ A) : Y ≤ₜ B :=
  (hXY.2.trans h).trans hAB.1

/-- The `k`-th jump of an invariant function is invariant. -/
private theorem jumpIter_comp_invariant (hF : TuringInvariant F) (k : ℕ) :
    ∀ X Y, X ≡ₜ Y → Cantor.jump^[k] (F X) ≡ₜ Cantor.jump^[k] (F Y) := by
  intro X Y hXY
  exact (uniformlyTuringInvariant_jumpIterate k).turingInvariant _ _ (hF X Y hXY)

/-- **Jump-distance decomposition of the regressive core.**  For any Turing-invariant
`F`, under determinacy, on a cone *either* `X` is never below any finite jump of `F X`
(the arithmetically-far, Lutz-hyperarithmetic case), *or* there is a fixed `k` with
`X ≤ᵀ (F X)^(k)` on a cone (the arithmetically-close, finitary case).  Proof: the
`ℕ ∪ {∞}`-valued jump-distance is degree-invariant, so its level sets are countably
many invariant sets covering every cone; `exists_onCone_of_cover` selects one. -/
theorem regressive_jump_dichotomy (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) :
    OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (F X)) ∨
    ∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (F X)) := by
  -- countable family: `g 0` = arithmetically-far set, `g (k+1)` = `{X | X ≤ᵀ (F X)^(k)}`
  set g : ℕ → Set (ℕ → Bool) := fun n => Nat.casesOn n
    {X | ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (F X)}
    (fun k => {X | X ≤ₜ Cantor.jump^[k] (F X)}) with hg
  have hinv : ∀ n, TuringInvariantSet (g n) := by
    intro n
    cases n with
    | zero =>
      intro X Y hXY
      constructor
      · intro hX k hk
        exact hX k (transport_le hXY.symm (jumpIter_comp_invariant hF k Y X hXY.symm) hk)
      · intro hY k hk
        exact hY k (transport_le hXY (jumpIter_comp_invariant hF k X Y hXY) hk)
    | succ k =>
      intro X Y hXY
      exact ⟨fun hX => transport_le hXY (jumpIter_comp_invariant hF k X Y hXY) hX,
             fun hY => transport_le hXY.symm (jumpIter_comp_invariant hF k Y X hXY.symm) hY⟩
  have hcover : cone (fun _ => false) ⊆ ⋃ n, g n := by
    intro X _
    rw [Set.mem_iUnion]
    by_cases hex : ∃ k, X ≤ₜ Cantor.jump^[k] (F X)
    · obtain ⟨k, hk⟩ := hex
      exact ⟨k + 1, hk⟩
    · refine ⟨0, ?_⟩
      push_neg at hex
      exact hex
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hinv hcover
  cases n with
  | zero => exact Or.inl hn
  | succ k => exact Or.inr ⟨k, hn⟩

#print axioms regressive_jump_dichotomy

end Martin
