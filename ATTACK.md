# Attack log: Martin's conjecture, Part I

Session 3 (2026-08-13 afternoon). This file records the *direct* attack on the open
content of Martin's conjecture: what was proved, what was attempted on the open cores,
and precisely where each attempt failed. Companion code: `MartinMeasure.lean`,
`Reduction.lean`, `BoundedCase.lean`, `OrderPreservingCase.lean` (all sorry-free).

## What the attack achieved (proved, sorry-free)

Under the explicit hypothesis `TuringDeterminacy` (all Turing-invariant games determined
— the AD-style hypothesis; its Borel restriction is a ZFC theorem of Martin not yet in
Lean):

1. **σ-pigeonhole** (`exists_onCone_of_cover`): countably many invariant determined sets
   covering a cone ⟹ one contains a cone. Martin measure is a countably complete
   ultrafilter, formally.
2. **Comparability trichotomy** (`comparability_on_cone`): every invariant `F` is, on a
   cone, ≡ id, > id, < id, or ⊥ id.
3. **The reduction** (`partI_of_cores`): Part I ⟸ the two open cores:
   - `RegressiveImpliesConstant` (`F < id` on a cone ⟹ constant on a cone),
   - `IncomparableImpliesConstant` (`F ⊥ id` on a cone ⟹ constant on a cone).
   In the other two regimes Part I is proved outright.
4. **Index stabilization** (`exists_uniform_index_on_cone`): a regressive invariant `F`
   is computed by a *single fixed* oracle machine on a representative of every degree on
   a cone.
5. **Boundedness lemma** (`bounded_implies_constant`): values below a fixed `Z` on a cone
   ⟹ constant on a cone (countably many `Z`-computable reals + pigeonhole).
6. **Escape theorem** (`counterexample_escapes`) and the sharpened cores
   (`regressive_core_iff_escaping`, `incomparable_core_iff_escaping`): any counterexample
   escapes every fixed degree on a cone.
7. **Order-preserving skeleton** (`orderPreserving_measurePreserving_or_avoids`,
   determinacy-free; `partI_orderPreserving_of_lemmas`): Lutz–Siskind's theorem reduced
   to its two main lemmas, with the elementary dichotomy fully proved.
8. **Counterexample profile** (`counterexample_profile`): the conjunction of 2 & 6.

Items 1–6 constitute, to our knowledge, the first machine-checked formalization of the
standard structural analysis surrounding Martin's conjecture. The open problem is now
formally *isolated*: it is exactly the two escaping cores.

## Direct attempts on the escaping cores, and where they died

**Attempt A — join-limit coding (regressive/avoiding case).** Given escaping `F`, build
`X₀ ≤ X₁ ≤ ⋯` where `X_{n+1}` escapes `Z_n := ⊕_{k≤n} F(X_k) ⊕ Z₀`, and pass to
`X_ω := ⊕ X_n`. Order preservation gives `F(X_ω) ≥ F(X_n)` for each `n`. **Failure
point**: to contradict "range avoids `cone Z₀`" one needs `F(X_ω) ≥ ⊕_n F(X_n)` (the
*ω-join*, into which `Z₀` could be coded), but an upper bound of each column need not
compute the join *uniformly* — this is precisely the non-uniformity gap that makes
Spector exact pairs exist. The argument establishes nothing beyond directedness.

**Attempt B — topological/Baire arguments.** Every degree-class is dense, and `F` is
constant-mod-≡ on each class; for continuous or Borel `F` one hopes density + continuity
collapse the values. **Failure point**: the value-classes are themselves dense, so
"`F(X_n) → F(Y)` with `F(X_n) ∈ D₁`" gives `F(Y) ∈ closure(D₁) = 2^ω` — no information.
Category-theoretic strengthening founders on the standard mismatch: cones are neither
comeager nor null; Martin measure and Baire category are orthogonal largeness notions.

**Attempt C — Posner–Robinson leverage (incomparable case).** With `F X ⊥ X`, the join
`H(X) = X ⊕ F X` is invariant and strictly above the identity; relativized
Posner–Robinson (`A ≰ X ⟹ ∃ G ≥ X, A ⊕ G ≡ G′`) is the classical tool to convert
"incomparable information" into jump-computations and drive a contradiction against
part II-type structure. **Failure point**: Posner–Robinson itself (Kumabe–Slaman
forcing) is a major unformalized theorem, and the surrounding argument (Slaman–Steel)
additionally needs the pointed-perfect-tree machinery. Both are genuine formalization
projects, not session-scale steps.

**Attempt D — after stabilization (uniform-machine case).** Index stabilization gives a
fixed `e` computing `F` on a representative of every degree on a cone. Steel's proof
(for uniformly invariant `F`) proceeds by comparison games along *pointed perfect
trees* to show the value degree stabilizes. **Failure point**: the representative
produced by stabilization varies with the degree, and controlling `Φ_e` across
*different representatives of the same degree* is exactly the content of Steel's
game analysis. Without pointed trees there is no handle.

## Assessment

The mathematical wall is real and precisely located: all four attempts die at one of
three missing pillars — (i) pointed perfect trees and the "measure-one sets contain
pointed trees" refinement of the cone theorem, (ii) Posner–Robinson / Kumabe–Slaman
forcing, (iii) Steel's comparison-game analysis. These are the same pillars the human
proofs of the *known* partial results rest on. No shortcut around them was found, and
(honestly) none was expected: the escaping cores as isolated here are exactly the
50-year-open content.

## Next formal milestones (in dependency order)

1. **Pointed perfect trees**: definition, `[T] ∋` branch computability lemmas, and the
   refinement "invariant determined set containing a cone contains a pointed tree"
   (this is a cone-theorem-style game argument — plausibly within a session or two on
   top of the existing game infrastructure).
2. With pointed trees: **Steel's uniform case** of the cores (first real conquest of a
   named Martin's-conjecture partial result beyond skeletons).
3. **Posner–Robinson** (Kumabe–Slaman forcing) — a large standalone formalization.
4. With 1–3: the Slaman–Steel and Lutz–Siskind theorems in full, i.e. every known
   partial result of Part I.
