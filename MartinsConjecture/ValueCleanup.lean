/-
**Steel's Conjecture — the "value-cleanup" attack, and its exact obstruction
(the VALUE-side companion to `CanonicalRepresentative.lean`).**

`CanonicalRepresentative.lean` proves the INPUT-side no-go: precomposing `F` with
a fixed uniformly-degree-preserving computable coding `c` (i.e. `G = F ∘ c`) is
uniformity-*neutral* — `F ∘ c` is uniformly invariant iff `F` is.  So the whole
obstruction to Steel's Conjecture lives in `F`'s VALUES, and any genuine
construction of a uniform `G` Martin-equivalent to `F` must alter the *values*
`F x`, using `x`.

This file settles the natural VALUE-side attempt and shows it too is neutral.
The natural *fixed, uniform* form of a "value-cleanup that preserves
Martin-equivalence" is: pick a fixed binary operation `Ψ : 2^ω → 2^ω → 2^ω` and
set `G x = Ψ x (F x)`.  (This is not literally every Martin-equivalence-preserving
cleanup — a non-uniform or degree-changing `Ψ` escapes these hypotheses; the
verdict's trichotomy below accounts for exactly those escape routes.)
For `G` to be Martin-equivalent to `F` we need `Ψ x (F x) ≡ᵀ F x` — i.e. `Ψ` is
*value-preserving in its second argument*.  The hope: `Ψ` uses `x` to supply the
reduction data that `F`'s non-uniformity withholds.

**We prove it CANNOT** (`valueCleanup_no_gain`): for a **fixed** binary
uniformly-invariant, value-preserving `Ψ` (witnessed by fixed index data), the
cleaned function `G x = Ψ x (F x)` is uniformly invariant **iff** `F` is.  The
mechanism is the exact dual of the input-side result:

* **Forward** (`uniform_valueCleanup_of_uniform`): if `F` is uniform via `u`, then
  the second-argument equivalence witness `(k,l) = u(i,j)` is available as a
  *computable function of `(i,j)`*, so `Ψ`'s binary transformer composed with `u`
  uniformizes `G`.  Ψ can only ever *forward* `F`'s witness — it cannot create one.
* **Converse** (`uniform_of_uniform_valueCleanup`): if `Ψ` is *faithful* — its
  value `Ψ x y` recovers `y` by a fixed index (value-preserving with a fixed
  section on the second coordinate) — then a uniformity transformer for `G` yields
  one for `F`, because `F x ≡ᵀ G x` via fixed indices and `EquivVia` composes
  computably (`EquivVia.trans_trE`).

**The conceptual payoff (the honest verdict on value-cleanup).**  Preserving
Martin-equivalence forces `Ψ x (F x) ≡ᵀ F x`, so the forward reduction
`Ψ x (F x) ≤ᵀ F x` means *`x` contributes nothing to the degree of the value* —
`Ψ` is, degree-theoretically, a fixed reprocessing of `F x` alone.  Hence it can
carry no reduction data that `F x` (with its non-uniform witness) does not already
carry.  To supply the missing witness, `Ψ` would have to raise the degree using
`x` (e.g. the join `x ⊕ F x`), which *breaks* Martin-equivalence precisely in the
open incomparable case (`x ⊕ F x >ᵀ F x` when `F x ⊥ᵀ x`).  So a fixed
degree-preserving value-cleanup is provably neutral, and the only remaining
"value-cleanup" is a non-uniform / degree-changing one — i.e. one that already
solves the uniformization problem.  This localizes the obstruction sharply:
neither input reparametrization nor fixed value reprocessing can help; the cleanup
itself must be as non-uniform as `F`.
-/
import MartinsConjecture.CanonicalRepresentative
import MartinsConjecture.UniformJoin

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Binary uniformly-invariant, value-preserving operations

A binary operation `Ψ` is **binary uniformly invariant** if index witnesses for
`x ≡ᵀ x'` and `y ≡ᵀ y'` transform (by a fixed `w`) into a witness for
`Ψ x y ≡ᵀ Ψ x' y'`.  It is **value-preserving** (in the second coordinate) if
`Ψ x y ≡ᵀ y` via a *fixed* pair of indices for all `x, y` — this is exactly what
makes `G x = Ψ x (F x)` Martin-equivalent to `F` (indeed pointwise `≡ᵀ`). -/

/-- `Ψ` is **binary uniformly invariant** via the transformer `w`. -/
def BinaryUniformlyInvariant (Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool)
    (w : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ) : Prop :=
  ∀ x x' y y' i j k l, EquivVia x x' i j → EquivVia y y' k l →
    EquivVia (Ψ x y) (Ψ x' y') (w ((i, j), (k, l))).1 (w ((i, j), (k, l))).2

/-- `Ψ` is **value-preserving** via the fixed index pair `(p, q)`: for all `x, y`,
`Ψ x y ≡ᵀ y` witnessed by `(p, q)` (i.e. `Φ_p(Ψ x y) = y` and `Φ_q(y) = Ψ x y`),
the *same* pair for all `x, y`.  This makes `x ↦ Ψ x (F x)` pointwise `≡ᵀ F`. -/
def ValuePreserving (Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool) (p q : ℕ) : Prop :=
  ∀ x y : ℕ → Bool, EquivVia (Ψ x y) y p q

/-! ### Martin-equivalence of the value-cleanup is automatic -/

/-- A value-preserving cleanup is pointwise `≡ᵀ` to `F`, hence Martin-equivalent. -/
theorem martinEquiv_valueCleanup {F : (ℕ → Bool) → ℕ → Bool}
    {Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool} {p q : ℕ}
    (hΨ : ValuePreserving Ψ p q) :
    MartinEquiv (fun x => Ψ x (F x)) F :=
  ⟨fun _ => false, fun X _ => (hΨ X (F X)).equiv⟩

/-! ### Forward: a fixed binary-uniform cleanup preserves uniformity

If `F` is uniformly invariant, the missing second-coordinate witness `(k,l)` is
`u (i,j)` — a computable function of `(i,j)` — so composing `w` with `u` gives a
transformer for `G`.  `Ψ` merely *forwards* `F`'s witness. -/

theorem uniform_valueCleanup_of_uniform {F : (ℕ → Bool) → ℕ → Bool}
    (hF : UniformlyTuringInvariant F)
    {Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool} {w : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ}
    (hΨ : BinaryUniformlyInvariant Ψ w) :
    UniformlyTuringInvariant (fun x => Ψ x (F x)) := by
  obtain ⟨u, hu⟩ := hF
  refine ⟨fun p => w (p, u p), ?_⟩
  intro x x' i j hxx'
  -- `F x ≡ᵀ F x'` via `u (i,j)` (uniform invariance of `F`).
  have hFF : EquivVia (F x) (F x') (u (i, j)).1 (u (i, j)).2 := hu x x' i j hxx'
  -- Feed both witnesses through `Ψ`'s binary transformer.
  have := hΨ x x' (F x) (F x') i j (u (i, j)).1 (u (i, j)).2 hxx' hFF
  simpa using this

/-! ### Converse: a faithful cleanup cannot destroy uniformity either

If `Ψ` is value-preserving via fixed `(p,q)`, then `F x ≡ᵀ G x` via fixed indices,
so a transformer for `G` is conjugated by these fixed indices — through the
computable composition `EquivVia.trans_trE` — into a transformer for `F`. -/

/-- **Converse, explicit transformer.**  The uniformity transformer for `F` is the
conjugation of `G`'s transformer `u` by the fixed value-preserving indices
`(p, q)`, assembled by two computable `trE`-composites via `EquivVia.trans_trE`.
Given `x ≡ᵀ x' via (i,j)`, chain
`F x --(q)--> Ψ x (F x) --(u (i,j))--> Ψ x' (F x') --(p)--> F x'`. -/
theorem uniform_of_uniform_valueCleanup {F : (ℕ → Bool) → ℕ → Bool}
    {Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool} {p q : ℕ}
    (hΨ : ValuePreserving Ψ p q)
    (hG : UniformlyTuringInvariant (fun x => Ψ x (F x))) :
    UniformlyTuringInvariant F := by
  obtain ⟨u, hu⟩ := hG
  refine ⟨fun r =>
      (trE (ofNatCode (trE (ofNatCode q) (u r).1)) p,
       trE (ofNatCode q) (trE (ofNatCode (u r).2) p)), ?_⟩
  intro x x' i j hxx'
  have hAx : EquivVia (F x) (Ψ x (F x)) q p := (hΨ x (F x)).symm
  have hB : EquivVia (Ψ x (F x)) (Ψ x' (F x')) (u (i, j)).1 (u (i, j)).2 :=
    hu x x' i j hxx'
  have hCx' : EquivVia (Ψ x' (F x')) (F x') p q := hΨ x' (F x')
  have hAB : EquivVia (F x) (Ψ x' (F x'))
      (trE (ofNatCode q) (u (i, j)).1) (trE (ofNatCode (u (i, j)).2) p) :=
    hAx.trans_trE hB
  exact hAB.trans_trE hCx'

/-! ### The verdict -/

/-- **THE VERDICT (value-cleanup launders nothing).**  For a **fixed** binary
uniformly-invariant, value-preserving operation `Ψ` (with fixed witness data
`w`, `(p,q)`), the value-cleanup `G x = Ψ x (F x)` is:
* Martin-equivalent to `F` (`martinEquiv_valueCleanup`), and
* uniformly invariant **iff** `F` is uniformly invariant.

So — exactly like the input-side canonical-representative attempt — a fixed
degree-preserving value reprocessing can neither create nor destroy the uniformity
obstruction.  Combined with `canonicalRepresentative_no_gain`, this shows that
*neither* reparametrizing inputs *nor* fixed value-preserving reprocessing can
produce Steel's uniform `G`; the cleanup would have to be as non-uniform as `F`
itself (or degree-changing, breaking Martin-equivalence in the incomparable
case). -/
theorem valueCleanup_no_gain {F : (ℕ → Bool) → ℕ → Bool}
    {Ψ : (ℕ → Bool) → (ℕ → Bool) → ℕ → Bool}
    {w : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ} {p q : ℕ}
    (hΨw : BinaryUniformlyInvariant Ψ w) (hΨpq : ValuePreserving Ψ p q) :
    MartinEquiv (fun x => Ψ x (F x)) F ∧
    (UniformlyTuringInvariant F ↔ UniformlyTuringInvariant (fun x => Ψ x (F x))) :=
  ⟨martinEquiv_valueCleanup hΨpq,
   ⟨fun hF => uniform_valueCleanup_of_uniform hF hΨw,
    fun hG => uniform_of_uniform_valueCleanup hΨpq hG⟩⟩

/-! ### Non-vacuity: the trivial value-preserving cleanup `Ψ x y = y`

The second projection `Ψ x y = y` (ignore `x`) is binary uniformly invariant (its
transformer just reads off the `y`-witness `(k,l)`) and value-preserving via the
oracle-query pair.  With it the verdict is the tautology "`F` uniform iff `F`
uniform" — the sanity check that the conjugation machinery is sound.  It also makes
explicit *why* one wants a nontrivial `Ψ` (to use `x`), and why a value-preserving
one cannot (it degree-collapses onto `y = F x`). -/

theorem binaryUniformlyInvariant_snd :
    BinaryUniformlyInvariant (fun _ y => y) (fun r => r.2) :=
  fun _ _ _ _ _ _ _ _ _ hyy' => hyy'

theorem valuePreserving_snd :
    ValuePreserving (fun _ y => y) (encodeCode .oracle) (encodeCode .oracle) :=
  fun _ y => EquivVia.refl y

/-- Sanity: the trivial cleanup gives back exactly `F`'s uniformity. -/
example (F : (ℕ → Bool) → ℕ → Bool) :
    (UniformlyTuringInvariant F ↔
      UniformlyTuringInvariant (fun x => (fun _ y => y) x (F x))) :=
  (valueCleanup_no_gain (F := F) binaryUniformlyInvariant_snd valuePreserving_snd).2

/-! ### The join cleanup provably breaks Martin-equivalence on the incomparable core

The natural *degree-using* cleanup is the join `Ψ x y = x ⊕ y` (which genuinely
uses `x` and could carry `x`'s reduction data).  But it is **not value-preserving**
exactly where it would matter: if `x ⊕ F x ≡ᵀ F x` then `x ≤ᵀ x ⊕ F x ≡ᵀ F x`, so
`x ≤ᵀ F x` — impossible when `F x ⊥ᵀ x` (the open incomparable core).  So the join
cleanup fails the `ValuePreserving` hypothesis on precisely the region of interest;
it changes the degree there, breaking Martin-equivalence.  This closes the
dichotomy: a value-cleanup either is fixed-degree-preserving (neutral,
`valueCleanup_no_gain`) or degree-changing (breaks Martin-equivalence in the
incomparable case, below), or non-uniform (as hard as Steel's conjecture). -/

/-- On the incomparable core, the join cleanup is **not** Martin-equivalent to `F`:
`x ⊕ F x ≢ᵀ F x` whenever `F x ⊥ᵀ x`.  (If `x ⊕ F x ≡ᵀ F x`, then
`x ≤ᵀ x ⊕ F x ≡ᵀ F x` forces `x ≤ᵀ F x`, contradicting incomparability.) -/
theorem join_cleanup_breaks_equiv {F : (ℕ → Bool) → ℕ → Bool} {X : ℕ → Bool}
    (hinc : ¬ X ≤ₜ F X) :
    ¬ (Cantor.join X (F X) ≡ₜ F X) := by
  intro hEq
  exact hinc (Cantor.le.trans (Cantor.left_le_join X (F X)) hEq.1)

/-- Consequently, **no** value-preserving witness pair `(p,q)` can exist for the
join on the incomparable core: `ValuePreserving (join)` fails at any `X` with
`F X ⊥ᵀ X`.  This is the precise sense in which the degree-using cleanup escapes
`valueCleanup_no_gain`'s hypotheses — by violating them. -/
theorem join_not_valuePreserving_on_incomparable {X Y : ℕ → Bool}
    (hinc : ¬ X ≤ₜ Y) (p q : ℕ) :
    ¬ EquivVia (Cantor.join X Y) Y p q := by
  intro h
  exact hinc (Cantor.le.trans (Cantor.left_le_join X Y) h.equiv.1)

#print axioms martinEquiv_valueCleanup
#print axioms uniform_valueCleanup_of_uniform
#print axioms uniform_of_uniform_valueCleanup
#print axioms valueCleanup_no_gain
#print axioms join_cleanup_breaks_equiv
#print axioms join_not_valuePreserving_on_incomparable

end Martin
