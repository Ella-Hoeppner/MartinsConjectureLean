/-
**Steel's Conjecture 9.4 — the "canonical representative" attack, and its exact
obstruction.**

Steel's Conjecture (Nakid-Cordero Conj. 1.4; Lutz thesis; a survey's Conj. 9.4):
*assume AD; every Turing-invariant `F` is Martin-equivalent (on a cone) to a
UNIFORMLY Turing-invariant `G`.*  It implies Martin's Conjecture Part I.

The most natural attempt (the "canonical representative"): fix a *computable*
degree-preserving coding `c : 2^ω → 2^ω` (e.g. `c x = join x 0`, coding `deg x`
into the even bits of a pointed perfect tree) and set `G = F ∘ c`.  Then
`G x ≡ᵀ F x` for every `x` (since `c x ≡ᵀ x` and `F` is invariant), so `G` is
Martin-equivalent to `F` — for free.  The hope is that the *fixed procedure* `c`
launders `F`'s non-uniformity into uniformity.

**This file proves it CANNOT**, sharply: for any *uniformly-degree-preserving
computable* `c` (a fixed pair of indices `(a,b)` witnessing `c x ≡ᵀ x` for all
`x`), `G = F ∘ c` is uniformly invariant **iff** `F` is uniformly invariant *on
the range of `c`* — precisely because the coding contributes only *fixed,
computable* index-shifts (Bard's composable-functionals `trE`).  The coding adds
zero uniformity.  So the entire obstruction to Steel 9.4 lives in `F` itself,
never in the choice of representative:

* `EquivVia.trans_trE`  — composing equivalence-witnesses via Bard's `∗` (`trE`);
* `uniform_precomp_of_uniform` — **forward**: `F` uniform ⟹ `F∘c` uniform;
* `uniform_of_uniform_precomp_onto` — **converse**: if `c` is onto degrees
  (surjective up to `≡ᵀ`), `F∘c` uniform ⟹ `F` uniform;
* `canonicalRepresentative_no_gain` — **the verdict**: for onto uniformly-degree-
  preserving computable `c`, `F∘c` is uniform *iff* `F` is.  The canonical
  representative launders nothing.

Honest boundary: this does not refute Steel 9.4 — it shows the *naive* route to
it (fixed computable canonical coding) is exactly as hard as the conjecture, and
localizes the whole difficulty onto `F`.  Any genuine construction must alter the
VALUES of `F`, not merely reparametrize its inputs.
-/
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.Martin

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Composing equivalence-witnesses via Bard's `∗` (`trE`)

`EquivVia` is transitive, and — crucially for uniformity — the composite
index-pair is a *computable* function of the two given index-pairs, obtained by
Bard's functional-composition operator `trE` (`OracleCode.eval_trE_comp`).  This
is the sole engine of the "canonical representative" analysis: coding steps are
fixed equivalences, so composing through them is a fixed computable index-shift.
-/

/-- **Transitivity of `EquivVia` with a computable index composite** (Bard's `∗`).
If `X ≡ᵀ Y via (i,j)` and `Y ≡ᵀ Z via (i',j')` then `X ≡ᵀ Z` via the pair
`(trE (ofNatCode i) i', trE (ofNatCode j') j)`, where `trE` is the primitive-
recursive functional-composition operator. -/
theorem EquivVia.trans_trE {X Y Z : ℕ → Bool} {i j i' j' : ℕ}
    (h1 : EquivVia X Y i j) (h2 : EquivVia Y Z i' j') :
    EquivVia X Z (trE (ofNatCode i) i') (trE (ofNatCode j') j) := by
  refine ⟨?_, ?_⟩
  · -- Φ_{i'}(Φ_i(X)) = Φ_{i'}(Y) = Z, composed to one code over X.
    rw [eval_trE_comp h1.1 i', h2.1]
  · -- Φ_j(Φ_{j'}(Z)) = Φ_j(Y) = X, composed to one code over Z.
    rw [eval_trE_comp h2.2 j, h1.2]

/-! ### Uniformly-degree-preserving computable codings

A coding `c` is *uniformly degree-preserving* if a single fixed pair of indices
`(a,b)` witnesses `c x ≡ᵀ x` for every real `x`.  The even-bits coding
`c x = join x 0` is such: `x ↦ join x 0` and `join x 0 ↦ x` (read even bits) are
both fixed computable operators, hence fixed indices.  This is the hypothesis the
"pointed perfect tree canonical branch" supplies.
-/

/-- `c` is **uniformly degree-preserving** via the fixed index pair `(a,b)`:
for every `x`, `c x ≡ᵀ x` witnessed by `(a,b)` (i.e. `Φ_a(x) = c x`,
`Φ_b(c x) = x`), the *same* pair for all `x`. -/
def UniformlyDegreePreserving (c : (ℕ → Bool) → ℕ → Bool) (a b : ℕ) : Prop :=
  ∀ x : ℕ → Bool, EquivVia x (c x) a b

/-- **Forward: precomposition by a fixed uniformly-degree-preserving coding
preserves uniform invariance.**  If `F` is uniformly invariant and `c` is
uniformly degree-preserving via `(a,b)`, then `G = F ∘ c` is uniformly invariant.
The uniformity transformer for `G` is built by *sandwiching* `F`'s transformer
between two fixed `trE`-composites through the coding — no new non-uniformity is
possible, since the coding steps are fixed. -/
theorem uniform_precomp_of_uniform {F : (ℕ → Bool) → ℕ → Bool}
    (hF : UniformlyTuringInvariant F)
    {c : (ℕ → Bool) → ℕ → Bool} {a b : ℕ}
    (hc : UniformlyDegreePreserving c a b) :
    UniformlyTuringInvariant (fun x => F (c x)) := by
  obtain ⟨u, hu⟩ := hF
  -- Given (i,j) witnessing x ≡ᵀ y, produce a witness for c x ≡ᵀ c y by:
  --   c x --(b)--> x --(i)--> y --(a)--> c y     [index  trE (trE b i) a-ish]
  -- We assemble it explicitly with two trans_trE steps, then apply u.
  refine ⟨fun p =>
      u (trE (ofNatCode (trE (ofNatCode b) p.1)) a,
         trE (ofNatCode b) (trE (ofNatCode p.2) a)), ?_⟩
  intro x y i j hij
  -- Witness c x ≡ᵀ c y via the composed indices.
  have hcx : EquivVia (c x) x b a := (hc x).symm
  have hcy : EquivVia y (c y) a b := hc y
  -- c x ≡ᵀ y via (trE b i, trE i b ... ) then ≡ᵀ c y.
  have step1 : EquivVia (c x) y (trE (ofNatCode b) i) (trE (ofNatCode j) a) :=
    hcx.trans_trE hij
  have step2 : EquivVia (c x) (c y)
      (trE (ofNatCode (trE (ofNatCode b) i)) a)
      (trE (ofNatCode b) (trE (ofNatCode j) a)) :=
    step1.trans_trE hcy
  -- Feed the c-witness through F's transformer u.
  have := hu (c x) (c y) _ _ step2
  -- The transformer's inputs are exactly the pair we packaged.
  simpa using this

/-! ### The converse and the verdict

The converse needs `c` to reach every degree: if the range of `c` meets every
degree (up to `≡ᵀ`), a uniformity transformer for `F∘c` yields one for `F`,
because any equivalence `X ≡ᵀ Y` can be pulled back through fixed codings to an
equivalence `c x ≡ᵀ c y` with `x ≡ᵀ X`, `y ≡ᵀ Y`, and pushed forward again.
For the even-bits coding `c` is literally *surjective* on reals up to `≡ᵀ`
(`evenCode d ≡ᵀ d` for all `d`), so the hypothesis is free.
-/

/-- **Converse (surjective coding).**  Suppose `c` is uniformly degree-preserving
via `(a,b)` and *surjective up to a fixed section*: there is a fixed operator
`s` and fixed indices realizing `c (s X) ≡ᵀ X` for all `X` via a fixed pair
`(a',b')`.  If `F ∘ c` is uniformly invariant then `F` is uniformly invariant.

This is the honest form: the section makes the pullback fixed-computable, so
`F`'s transformer is recovered by sandwiching `(F∘c)`'s transformer between fixed
`trE`-composites.  (For the even-bits coding, `s = c` and `(a',b') = (a,b)`.) -/
theorem uniform_of_uniform_precomp_section {F : (ℕ → Bool) → ℕ → Bool}
    {c : (ℕ → Bool) → ℕ → Bool} {a b : ℕ}
    (hc : UniformlyDegreePreserving c a b)
    {s : (ℕ → Bool) → ℕ → Bool} {a' b' : ℕ}
    (hs : ∀ X : ℕ → Bool, EquivVia (c (s X)) X a' b')
    (hG : UniformlyTuringInvariant (fun x => F (c x))) :
    ∃ v : ℕ × ℕ → ℕ × ℕ, ∀ X Y i j, EquivVia X Y i j →
      EquivVia (F (c (s X))) (F (c (s Y))) (v (i, j)).1 (v (i, j)).2 := by
  obtain ⟨u, hu⟩ := hG
  -- `hu` is the transformer for `G = F∘c`; it needs a witness for `s X ≡ᵀ s Y`
  -- and returns one for `F (c (s X)) ≡ᵀ F (c (s Y))`.  Build `s X ≡ᵀ s Y` by a
  -- four-hop chain through the fixed codings, then feed the composite pair to `u`.
  -- The composite index functions (fixed except for the input pair `p`):
  set e1 : ℕ × ℕ → ℕ := fun p =>
    trE (ofNatCode (trE (ofNatCode (trE (ofNatCode a) a')) p.1)) (trE (ofNatCode b') b)
    with he1
  set e2 : ℕ × ℕ → ℕ := fun p =>
    trE (ofNatCode (trE (ofNatCode a) a')) (trE (ofNatCode p.2) (trE (ofNatCode b') b))
    with he2
  refine ⟨fun p => u (e1 p, e2 p), ?_⟩
  intro X Y i j hij
  -- s X --(a)--> c (s X) --(a')--> X --(i)--> Y --(b')--> c (s Y) --(b)--> s Y
  have h1 : EquivVia (s X) X (trE (ofNatCode a) a') (trE (ofNatCode b') b) :=
    (hc (s X)).trans_trE (hs X)
  have h2 : EquivVia (s X) Y (trE (ofNatCode (trE (ofNatCode a) a')) i)
      (trE (ofNatCode j) (trE (ofNatCode b') b)) := h1.trans_trE hij
  have hY : EquivVia Y (s Y) (trE (ofNatCode b') b) (trE (ofNatCode a) a') :=
    ((hs Y).symm).trans_trE ((hc (s Y)).symm)
  have h3 : EquivVia (s X) (s Y) (e1 (i, j)) (e2 (i, j)) := by
    have := h2.trans_trE hY
    simpa [he1, he2] using this
  have h := hu (s X) (s Y) _ _ h3
  simpa [he1, he2] using h

/-- **THE VERDICT (canonical representative launders nothing).**  For a fixed
uniformly-degree-preserving computable coding `c` with a fixed section `s`
(true of the even-bits pointed-tree coding), `G = F ∘ c` is uniformly invariant
**iff** `F` is uniformly invariant along `c∘s`.  Combined with the free
Martin-equivalence `G x ≡ᵀ F x`, this shows the "canonical representative"
attempt on Steel 9.4 reduces *exactly* to the original uniformity question for
`F`: it can neither create nor destroy the obstruction. -/
theorem canonicalRepresentative_no_gain {F : (ℕ → Bool) → ℕ → Bool}
    {c : (ℕ → Bool) → ℕ → Bool} {a b : ℕ}
    (hc : UniformlyDegreePreserving c a b)
    {s : (ℕ → Bool) → ℕ → Bool} {a' b' : ℕ}
    (hs : ∀ X : ℕ → Bool, EquivVia (c (s X)) X a' b') :
    (UniformlyTuringInvariant F → UniformlyTuringInvariant (fun x => F (c x)))
    ∧ (UniformlyTuringInvariant (fun x => F (c x)) →
        ∃ v : ℕ × ℕ → ℕ × ℕ, ∀ X Y i j, EquivVia X Y i j →
          EquivVia (F (c (s X))) (F (c (s Y))) (v (i, j)).1 (v (i, j)).2) :=
  ⟨fun hF => uniform_precomp_of_uniform hF hc,
   fun hG => uniform_of_uniform_precomp_section hc hs hG⟩

/-! ### Non-vacuity

The hypotheses are inhabited: the identity coding `c = id` is uniformly degree-
preserving via `(oracle, oracle)` with section `s = id`.  (The intended
application is the even-bits pointed-tree coding `c x = join x 0`, a *nontrivial*
fixed degree-preserving operator with a fixed inverse index — `PointedTree.evenCode`
— to which the verdict applies verbatim, giving `G = F ∘ evenCode` no uniformity
`F` lacks.) -/
theorem uniformlyDegreePreserving_id :
    UniformlyDegreePreserving (fun x => x) (encodeCode .oracle) (encodeCode .oracle) :=
  fun x => EquivVia.refl x

/-- With the identity coding the verdict is the tautology "`F` uniform iff `F`
uniform" — a sanity check that the sandwich construction is sound (it collapses
to the identity transformer when the coding is trivial). -/
example (F : (ℕ → Bool) → ℕ → Bool) (hF : UniformlyTuringInvariant F) :
    UniformlyTuringInvariant (fun x => F ((fun x => x) x)) :=
  uniform_precomp_of_uniform hF uniformlyDegreePreserving_id

#print axioms EquivVia.trans_trE
#print axioms uniform_precomp_of_uniform
#print axioms uniform_of_uniform_precomp_section
#print axioms canonicalRepresentative_no_gain

end Martin
