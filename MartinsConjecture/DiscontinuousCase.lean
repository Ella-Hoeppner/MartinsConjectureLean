/-
The discontinuous case of Lachlan's local dichotomy (Lutz Thm 3.10), reduction half.

`ContinuousCase.lean` proved the continuous branch (`Wˣ ≤ᵀ X ⊕ 0′`).  Its partner —
if the r.e. operator `W` (index `e`) is *discontinuous* at `X`, then `X′ ≤ᵀ Wˣ` —
is the pure-diagonalization direction.  The classical proof (Lachlan 1975; Bard;
Lutz thesis Thm 3.10) has three moving parts:

1. **the coding reals** `y_c ≡ᵀ X` with `n₀ ∈ W^{y_c} ⟺ Φ_c^X(c)↓` — built by
   splicing a marker-witnessing extension after the halting-stage prefix, so that
   the operator's value at the discontinuity marker `n₀` reads off the jump of `X`;
2. **s-m-n**: computable index witnesses `(r c, s c)` for `X ≡ᵀ y_c` (`curryEnc`);
3. **computable uniformity** (Bard's Lemma 3.8): a *computable* transformer of
   equivalence-witnesses for the operator, turning `(r c, s c)` into an index
   computing `W^{y_c}` from `Wˣ`.

This file proves the **reduction that assembles (1)–(3) into `X′ ≤ᵀ Wˣ`**, fully and
sorry-free, isolating the two genuinely-hard ingredients as named hypotheses:
`HasCodingFamily` (the coding reals + s-m-n witnesses) and
`ComputablyUniformlyTuringInvariant` (Bard's Lemma 3.8).  Given these, the reduction
is exactly a use of the universal machine `eval_universal` at the fixed marker `n₀`,
composed with the computable index map — the recursion-theoretic core, which is what
the whole file delivers.

(The remaining content — discharging `HasCodingFamily` from bare discontinuity, and
`ComputablyUniformlyTuringInvariant` from bare uniform invariance via Bard's Lemma —
is the multi-session r.e.-operator project flagged in `ATTACK.md`.  The universal
code is *not* a blocker: `eval_universal`/`exists_fixedPoint` are proved.)
-/
import MartinsConjecture.ContinuousCase
import MartinsConjecture.Universal
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.Martin

open scoped Computability
open OracleCode Cantor

namespace OracleCode

/-- **The coding-family hypothesis** for the discontinuous case at marker `n₀`.
There are *computable* index maps `r, s` and, for every `c`, a real `Y ≡ᵀ X`
witnessed by `(r c, s c)` such that the operator `W` (index `e`) at the marker
`n₀` reads off whether `c ∈ X′`: `n₀ ∈ W^Y ⟺ Φ_c^X(c)↓`.  This packages the
coding-real construction (splicing) together with its s-m-n witnesses. -/
def HasCodingFamily (e : ℕ) (X : ℕ → Bool) (n₀ : ℕ) : Prop :=
  ∃ r s : ℕ → ℕ, Computable r ∧ Computable s ∧
    ∀ c : ℕ, ∃ Y : ℕ → Bool,
      Martin.EquivVia X Y (r c) (s c) ∧
      (reReal e Y n₀ = true ↔ Cantor.jump X c = true)

/-- **The discontinuous-case reduction** (Lutz Thm 3.10, discontinuous branch,
reduction half).  If the operator `W` (index `e`) is computably uniformly
invariant and admits a coding family at some marker `n₀`, then the jump of `X`
is Turing-below `Wˣ`.  Fully proved: the recursion-theoretic assembly of the
coding reals, s-m-n, and computable uniformity via the universal machine. -/
theorem discontinuous_reduction (e : ℕ) (X : ℕ → Bool) (n₀ : ℕ)
    (hu : Martin.ComputablyUniformlyTuringInvariant (reReal e))
    (hcode : HasCodingFamily e X n₀) :
    Cantor.jump X ≤ₜ reReal e X := by
  classical
  obtain ⟨u, hu_comp, hu_spec⟩ := hu
  obtain ⟨r, s, hr, hs, hfam⟩ := hcode
  set W : ℕ → Bool := reReal e X with hWdef
  -- the computable index map: query the universal machine at the transformed,
  -- diagonalized index, on the fixed marker `n₀`.
  set idx : ℕ → ℕ := fun c => Nat.pair (u (r c, s c)).1 n₀ with hidxdef
  have hfst : Computable fun c => (u (r c, s c)).1 :=
    Computable.fst.comp (hu_comp.comp (Computable.pair hr hs))
  have hidx_comp : Computable idx :=
    ((Primrec₂.natPair.comp Primrec.id (Primrec.const n₀)).to_comp).comp hfst
  have hidx_rec : Nat.RecursiveIn {toPFun W} (fun c => ((idx c : ℕ) : Part ℕ)) :=
    (Partrec.nat_iff.mp (Computable.partrec hidx_comp)).recursiveIn
  -- assemble via the universal machine
  rw [Cantor.le_iff_bitg]
  refine (Nat.RecursiveIn.comp (eval_universal W) hidx_rec).of_eq fun c => ?_
  rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  -- the coding real for `c` and the transported operator value
  obtain ⟨Y, hEV, hcodeC⟩ := hfam c
  have hspec := congrFun (hu_spec X Y (r c) (s c) hEV).1 n₀
  simp only [hidxdef, Nat.unpair_pair]
  rw [← hWdef] at hspec
  rw [hspec, toPFun_eq_bitg]
  -- read off: `bitg (reReal e Y) n₀ = bitg (jump X) c`
  have hbiteq : bitg (reReal e Y) n₀ = bitg (Cantor.jump X) c := by
    simp only [bitg]
    rcases Bool.eq_false_or_eq_true (Cantor.jump X c) with hjc | hjc
    · rw [hjc, hcodeC.mpr hjc]
    · have hYf : reReal e Y n₀ = false := by
        rcases Bool.eq_false_or_eq_true (reReal e Y n₀) with h | h
        · exact absurd (hcodeC.mp h) (by rw [hjc]; decide)
        · exact h
      rw [hYf, hjc]
  rw [Part.coe_some, hbiteq]

#print axioms discontinuous_reduction

/-- **Local dichotomy with both conclusions**, modulo the coding hypothesis.
For every r.e. operator `W` (index `e`) and every `X`: either `W` is continuous
at `X`, giving `Wˣ ≤ᵀ X ⊕ 0′`, or `W` is discontinuous at `X` (a marker `n₀`
witnesses it) and — *if* `W` is computably uniformly invariant and has a coding
family there — `X′ ≤ᵀ Wˣ`.  This sharpens `local_dichotomy` by supplying the
discontinuous branch's Turing-degree conclusion (its reduction half). -/
theorem local_dichotomy_sharp (e : ℕ) (X : ℕ → Bool)
    (hu : Martin.ComputablyUniformlyTuringInvariant (reReal e)) :
    reReal e X ≤ₜ Cantor.join X (Cantor.jump (fun _ : ℕ => false))
    ∨ (∃ n₀, (∀ ℓ, ¬ haltsOn (graphOf (bitg X) ℓ) e n₀
        ∧ extHaltsFrom (graphOf (bitg X) ℓ) e n₀)
        ∧ (HasCodingFamily e X n₀ → Cantor.jump X ≤ₜ reReal e X)) := by
  rcases local_dichotomy X e with h | ⟨n₀, hn₀⟩
  · exact Or.inl h
  · exact Or.inr ⟨n₀, hn₀, fun hcode => discontinuous_reduction e X n₀ hu hcode⟩

#print axioms local_dichotomy_sharp

end OracleCode
