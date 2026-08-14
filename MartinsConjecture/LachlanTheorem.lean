/-
**Lachlan's theorem for r.e. operators**, globalized to a cone.

Assembling the two branches of the local dichotomy — the continuous case
(`OracleCode.continuous_case`, determinacy-free) and the discontinuous case
(`OracleCode.Coding.discontinuous_case_complete`, the coding-family construction
built in full) — with Martin's cone theorem (`Martin.cone_theorem_onCone`) gives
the global statement:

  a computably-uniformly-invariant r.e. operator `W` (index `e`) that is above
  the identity on a cone satisfies, **on a cone**, either `Wˣ ≡ᵀ X` or
  `Wˣ ≡ᵀ X′` — and is therefore never a solution to Post's problem.

The globalization pivots on the Turing-invariant set `{X | Wˣ ≤ᵀ X}`: the cone
theorem splits it into a cone (where `Wˣ ≤ᵀ X`, so with above-identity `Wˣ ≡ᵀ X`)
or a complementary cone (where `Wˣ ≰ᵀ X`, so `W` is discontinuous at every such
`X` and the coding family forces `Wˣ ≡ᵀ X′`).

Determinacy is threaded explicitly (`TuringDeterminacy`); nothing is axiomatized.
This is Lachlan's 1975 theorem [JSL 40.3], in the form of Lutz's thesis Cor 3.11,
with the coding construction fully formalized.  The one classical input left
external is Bard's Lemma 3.8 (bare uniform invariance ⟹ *computable* uniform
invariance), which is why the hypothesis here is computable uniformity.
-/
import MartinsConjecture.CodingFamilyCode
import MartinsConjecture.MartinMeasure

open scoped Computability
open OracleCode OracleCode.Coding Cantor

namespace Martin

/-- **Lachlan's local dichotomy, complete form** (Lutz Cor 3.11): for a
computably-uniform r.e. operator `W` (index `e`) and any `X ≥ᵀ 0′`, *either*
`Wˣ ≤ᵀ X` (continuous case) *or* `Wˣ ≡ᵀ X′` (discontinuous case).  Both branches
are fully proved: continuity via `continuous_case`, discontinuity via the coding
family `discontinuous_case_complete`.  No hypothesis about the coding family is
needed — it is built from the discontinuity witness. -/
theorem local_dichotomy_complete (e : ℕ) (X : ℕ → Bool)
    (hu : ComputablyUniformlyTuringInvariant (reReal e))
    (hX : Cantor.jump (fun _ : ℕ => false) ≤ₜ X) :
    reReal e X ≤ₜ X ∨ reReal e X ≡ₜ Cantor.jump X := by
  rcases local_dichotomy X e with hcont | ⟨n₀, hn₀⟩
  · exact Or.inl (hcont.trans (Cantor.join_le (Cantor.le.refl X) hX))
  · exact Or.inr
      (discontinuous_case_complete e n₀ X (fun ℓ => (hn₀ ℓ).1) (fun t => (hn₀ t).2) hu)

/-- **Lachlan's theorem, global form** (modulo Bard 3.8): a computably-uniform
r.e. operator `W` (index `e`) that is above the identity on a cone satisfies, on
a cone, `Wˣ ≡ᵀ X` *or* `Wˣ ≡ᵀ X′`.  Determinacy of the pivot set is an explicit
hypothesis. -/
theorem lachlan_dichotomy_cone (e : ℕ)
    (hu : ComputablyUniformlyTuringInvariant (reReal e))
    (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy (fun _ => True)) :
    MartinEquiv (reReal e) (fun X => X) ∨ MartinEquiv (reReal e) (fun X => Cantor.jump X) := by
  have hinv : TuringInvariant (reReal e) := hu.toUniformly.turingInvariant
  -- The pivot set `{X | Wˣ ≤ᵀ X}` is Turing-invariant (from invariance of `W`).
  have hTIS : TuringInvariantSet {X | reReal e X ≤ₜ X} := by
    intro Y Z hYZ
    have hF := hinv Y Z hYZ
    exact ⟨fun hY => hF.2.trans (hY.trans hYZ.1), fun hZ => hF.1.trans (hZ.trans hYZ.2)⟩
  rcases cone_theorem_onCone {X | reReal e X ≤ₜ X} hTIS (hTD _ trivial hTIS) with hle | hnle
  · -- Cone where `Wˣ ≤ᵀ X`; with above-identity, `Wˣ ≡ᵀ X`.
    left
    obtain ⟨Y1, hY1⟩ := hle
    obtain ⟨Y2, hY2⟩ := habove
    exact ⟨Cantor.join Y1 Y2, fun X hX =>
      ⟨hY1 X ((Cantor.left_le_join Y1 Y2).trans hX),
        hY2 X ((Cantor.right_le_join Y1 Y2).trans hX)⟩⟩
  · -- Cone where `Wˣ ≰ᵀ X`; discontinuous, so `Wˣ ≡ᵀ X′`.
    right
    obtain ⟨Y1, hY1⟩ := hnle
    refine ⟨Cantor.join Y1 (Cantor.jump (fun _ : ℕ => false)), fun X hX => ?_⟩
    have hnot : ¬ (reReal e X ≤ₜ X) := hY1 X ((Cantor.left_le_join _ _).trans hX)
    rcases local_dichotomy_complete e X hu ((Cantor.right_le_join _ _).trans hX) with h | h
    · exact absurd h hnot
    · exact h

/-- **No r.e.-operator solution to Post's problem** (Lachlan 1975, modulo Bard
3.8): a computably-uniform r.e. operator above the identity is *never* strictly
between `X` and `X′` on a cone.  This is the payoff of Lachlan's theorem — the
degree-invariant analogue of the fact that r.e. operators cannot uniformly
produce intermediate degrees. -/
theorem lachlan_no_post_solution_cone (e : ℕ)
    (hu : ComputablyUniformlyTuringInvariant (reReal e))
    (habove : AboveIdOnCone (reReal e))
    (hTD : TuringDeterminacy (fun _ => True)) :
    ¬ OnCone (fun X => X <ₜ reReal e X ∧ reReal e X <ₜ Cantor.jump X) := by
  rintro ⟨B, hB⟩
  rcases lachlan_dichotomy_cone e hu habove hTD with ⟨B', hB'⟩ | ⟨B', hB'⟩
  · -- `Wˣ ≡ᵀ X` on a cone contradicts `X <ᵀ Wˣ`.
    exact absurd (hB' _ (Cantor.right_le_join B B')).1
      (hB _ (Cantor.left_le_join B B')).1.2
  · -- `Wˣ ≡ᵀ X′` on a cone contradicts `Wˣ <ᵀ X′`.
    exact absurd (hB' _ (Cantor.right_le_join B B')).2
      (hB _ (Cantor.left_le_join B B')).2.2

#print axioms local_dichotomy_complete
#print axioms lachlan_dichotomy_cone
#print axioms lachlan_no_post_solution_cone

end Martin
