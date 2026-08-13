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

## Exact analysis of the cores (added at session end)

`CoreAnalysis.lean`: the incomparable core is an *impossibility statement*
(`incomparable_core_iff_never` — its hypothesis and conclusion are jointly
contradictory), and the reduction of Part I to the two cores is an **exact
equivalence** (`partI_iff_cores`).  So the formal isolation of the open content is
lossless: Part I (AD-style, mod Turing determinacy) *is* the conjunction
"regressive ⟹ constant" ∧ "invariant functions are never ⊥-with-id on a cone".

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

## Progress on pillar (i) after this log was first written

`UniformJoin.lean` (sorry-free) lays the foundation of the pointed-tree pillar in the
"uniformly pointed join-cone" formulation, which avoids tree combinatorics entirely:

* `join_realizes` — above the base, canonical representatives `join W X` realize every
  degree;
* `equivVia_join_uniform` — **controlled congruence**: a computable index
  transformation, independent of `W, X, X'`, turning witnesses for `X ≡ₜ X'` into
  witnesses for `join W X ≡ₜ join W X'` (proved by explicit code construction: a fixed
  even/odd mixer code, the right-projection code, and the `trOracle` splice of the given
  index through the projection);
* `uniformlyTuringInvariant_comp_join` — composing a uniformly invariant function with
  the canonical-representative map preserves uniform invariance, with a computed
  uniformity function.

This is precisely the mechanism by which Steel-style arguments control a function
across representatives of the same degree.  What remains for Steel's uniform case is
the comparison-game analysis itself (pillar iii).

## Assessment

The mathematical wall is real and precisely located: all four attempts die at one of
three missing pillars — (i) pointed perfect trees and the "measure-one sets contain
pointed trees" refinement of the cone theorem, (ii) Posner–Robinson / Kumabe–Slaman
forcing, (iii) Steel's comparison-game analysis. These are the same pillars the human
proofs of the *known* partial results rest on. No shortcut around them was found, and
(honestly) none was expected: the escaping cores as isolated here are exactly the
50-year-open content.

## Attempt E — Steel's dichotomy game, formulated in this framework

The last direct attempt of the session was to formulate Steel's
boundedness-or-domination game for a uniformly invariant `F` inside the game
framework of `ConeTheorem.lean` (players alternate bits; II's real codes a triple
`(k, l, Y)`; payoff: *if* `Y ≡ₜ X` via `(k, l)` *then* `X ≤ₜ F Y`), aiming at:

* II wins ⟹ `F ≥ id` on a cone — this direction is executable with existing tools:
  the play is computable from the players' data (`gamePlay_le`), and uniformity
  transports `X ≤ₜ F Y` to `X ≤ₜ F X` via `u (k, l)`;
* I wins ⟹ `F` is bounded on a cone (⟹ constant, by the boundedness lemma).

**Failure point, and a structural discovery.**  The "I wins" analysis requires II to
play indices `(k, l)` witnessing `Y ≡ₜ X` where `X` is I's response *to that very
play*: the honest-play indices are a fixed point of a computable index
transformation.  This is exactly the **Kleene recursion theorem for oracle codes**
(`∀ computable g, ∃ c, ∀ O, eval O (g c) = eval O c`), whose proof requires the
self-application `Φ_x(x)` — i.e. the **step-indexed universal machine** (`evaln`),
the one infrastructure layer this project deliberately skipped.

The same missing artifact blocks Attempt D (Steel's comparison analysis), Lachlan's
theorem (recursion-theorem trickery), and the effective refinement of Kleene–Post.
**Conclusion: every remaining path — all three pillars — funnels through a single
missing artifact: the universal machine for `OracleCode`.**  It is a large mechanical
port (Mathlib's `evaln` + `evaln_prim` development, relativized, est. 300–600 lines
of hard primrec proofs) but requires no new ideas.  It is unambiguously the next
target; with it, Steel's uniform case per the blueprint above becomes a concrete,
fully-specified formalization plan rather than research.

## Next formal milestones (in dependency order)

1. ~~Pointed perfect trees~~ **Done in the join-cone formulation** (`UniformJoin.lean`:
   realization, controlled congruence, `exists_pointed_family_of_onCone`).
2. **The universal machine for `OracleCode`** (`evaln` + its primitive recursiveness,
   relativized) — the single funnel identified in Attempt E.  Mechanical but large.
3. With 2: the **oracle recursion theorem**, then **Lachlan's theorem**, then
   **Steel's uniform case** via the Attempt-E game blueprint — the first genuine
   partial results of Martin's conjecture, machine-checked.
4. **Posner–Robinson** (Kumabe–Slaman forcing) — the remaining pillar for the
   Slaman–Steel and Lutz–Siskind theorems in full.
