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

/-- **Dual jump-distance dichotomy** (`F X` vs `X`'s jumps).  For any invariant `F`, on
a cone either `F X ≰ᵀ X^(n)` for all `n` (`F X` is arithmetically *not below* `X`) or there
is a fixed `k` with `F X ≤ᵀ X^(k)` on a cone (`F X` is arithmetic in `X`).  Together with
`regressive_jump_dichotomy` this two-dimensionally locates `F X` relative to `X` in the
finite jump hierarchy — the structural map for the incomparable core (`F X ⊥ᵀ X`, where
both `X ≰ᵀ F X` and `F X ≰ᵀ X`, so both raw comparisons fail and only the jump-distances
carry information). -/
theorem jump_dichotomy_dual (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) :
    OnCone (fun X => ∀ k, ¬ F X ≤ₜ Cantor.jump^[k] X) ∨
    ∃ k, OnCone (fun X => F X ≤ₜ Cantor.jump^[k] X) := by
  set g : ℕ → Set (ℕ → Bool) := fun n => Nat.casesOn n
    {X | ∀ k, ¬ F X ≤ₜ Cantor.jump^[k] X}
    (fun k => {X | F X ≤ₜ Cantor.jump^[k] X}) with hg
  have hjinv : ∀ (k : ℕ) X Y, X ≡ₜ Y → Cantor.jump^[k] X ≡ₜ Cantor.jump^[k] Y :=
    fun k X Y hXY => (uniformlyTuringInvariant_jumpIterate k).turingInvariant _ _ hXY
  have hinv : ∀ n, TuringInvariantSet (g n) := by
    intro n
    cases n with
    | zero =>
      intro X Y hXY
      exact ⟨fun hX k hk => hX k (transport_le (hF Y X hXY.symm) (hjinv k Y X hXY.symm) hk),
             fun hY k hk => hY k (transport_le (hF X Y hXY) (hjinv k X Y hXY) hk)⟩
    | succ k =>
      intro X Y hXY
      exact ⟨fun hX => transport_le (hF X Y hXY) (hjinv k X Y hXY) hX,
             fun hY => transport_le (hF Y X hXY.symm) (hjinv k Y X hXY.symm) hY⟩
  have hcover : cone (fun _ => false) ⊆ ⋃ n, g n := by
    intro X _
    rw [Set.mem_iUnion]
    by_cases hex : ∃ k, F X ≤ₜ Cantor.jump^[k] X
    · obtain ⟨k, hk⟩ := hex; exact ⟨k + 1, hk⟩
    · exact ⟨0, by push_neg at hex; exact hex⟩
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hinv hcover
  cases n with
  | zero => exact Or.inl hn
  | succ k => exact Or.inr ⟨k, hn⟩

#print axioms jump_dichotomy_dual

/-! ### Packaging as a core-reduction

The dichotomy reduces the open regressive core to two sharper sub-cores, exactly
parallel to `partI_iff_cores`.  A future proof need only settle each: `CaseBConstant`
(the finitary, arithmetic-preserving case) and `CaseAConstant` (the transfinite,
Lutz-`ω₁^x` case). -/

/-- The regressive core: a regressive invariant function is constant on a cone. -/
def RegressiveConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X <ₜ X) → ConstantOnCone F

/-- **Case B sub-core** (finitary): a regressive invariant `F` that, on a cone, has
`X ≤ᵀ (F X)^(k)` for some fixed `k` (so `F` preserves the arithmetic degree) is
constant on a cone. -/
def CaseBConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X <ₜ X) →
    (∃ k, OnCone (fun X => X ≤ₜ Cantor.jump^[k] (F X))) → ConstantOnCone F

/-- **Case A sub-core** (Lutz-`ω₁^x` regime): a regressive invariant `F` that, on a
cone, has `X ≰ᵀ (F X)^(n)` for every `n` (so `F X` is arithmetically strictly below
`X`) is constant on a cone. -/
def CaseAConstant : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    OnCone (fun X => F X <ₜ X) →
    OnCone (fun X => ∀ k, ¬ X ≤ₜ Cantor.jump^[k] (F X)) → ConstantOnCone F

/-- **The regressive core reduces to its two jump-distance sub-cores.**  If both the
finitary Case B and the Lutz-hyperarithmetic Case A sub-cores hold, the full open
regressive core follows — by `regressive_jump_dichotomy`, every regressive invariant
`F` lands in one case on a cone.  This is the proof-directed payoff of the
decomposition: it splits the open problem into a piece the elementary cone-measure
method can reach (B) and the piece that genuinely needs `ω₁^x` (A). -/
theorem regressiveCore_of_cases (hTD : TuringDeterminacy fun _ => True)
    (hA : CaseAConstant) (hB : CaseBConstant) : RegressiveConstant := by
  intro F hF hreg
  rcases regressive_jump_dichotomy hTD hF with hcaseA | ⟨k, hcaseB⟩
  · exact hA F hF hreg hcaseA
  · exact hB F hF hreg ⟨k, hcaseB⟩

#print axioms regressiveCore_of_cases

end Martin
