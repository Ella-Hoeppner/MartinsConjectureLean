# The Marks route to Part 1's open core, and the shape of the Q3/Q4 disproof targets

*Session 2026-08-26g. Machine-checked (std axioms, full build green). New files: `MarksBridge.lean`,
`DIWitness.lean`; engine `Lemma210.lean`, `Lemma211.lean`.*

## The reduction (all in the repo now)

Part 1's sole open content is the **incomparable core**: no invariant `F` has `F X ⊥ᵀ X` on a cone.
By Lutz–Siskind Thm 5.15 this is the **RK-rigidity of the Martin measure `U_M`**, which the repo
splits into (via `DominatedInvertible F := ∃` invariant `g`, `X ≤ᵀ g(F X)` on a cone):

- **Q3 / strict half** — every non-constant invariant `F` is dominated-invertible (`U_M ≤_RK F_*U_M`);
- **Q4 / equivalence half** — `DominatedInvertible F ⟹ MeasurePreserving F`.

`no_incomparable_of_marksConjecture_and_equivHalf`: Q3-via-Marks + Q4 ⟹ **no incomparable `F`**.

## Prop 5.37 (Marks ⟹ strict half), machine-checked — `MarksBridge.lean`

`MarksTree F` = a pointed perfect tree (`PPT`) on whose branch-degrees `F` is constant-or-injective.
- `constantOrDominatedInvertible_of_marksTree`: a Marks tree ⟹ `ConstantOnCone F ∨ DominatedInvertible F`.
  The bridge is `PPT.realizes` (the tree realizes a cone above its code); constancy/injectivity on the
  branches transports to the cone by invariance, and the injective case feeds
  `dominatedInvertible_of_injectiveOnCone`.
- `strictHalf_of_marksConjecture`, `partI_of_marksConjecture_and_equivHalf` (with the equivalence half).
- **The wall, pinned:** `marksTree_of_injectiveOnCone` — Marks holds whenever `F` is injective on a cone
  (any pointed tree in that cone is a Marks tree). So the *only* open content of Marks's conjecture is `F`
  injective on **no** cone: making a globally-non-injective `F` injective on a *pointed* tree. That is
  Lutz's tree-thinning **Lemma 2.7**, which requires `F` to be a **Turing functional** — precisely what
  the incomparable core is not (the `ℕ`-range wall: `MartinsConjecture/DIWitness` and the
  `uniformization-engine-wall` memory).

## The shape of a counterexample — `DIWitness.lean`

A Part-1 counterexample is `¬DI` (Q3 target) or DI-incomparable (Q4 target). New constraints:

**Q4 target (DI-incomparable `F`): the witness `g` is a jump-type operator.**
- Regressive witness (`g c ≤ᵀ c`) ⟹ `X ≤ᵀ g(F X) ≤ᵀ F X` ⟹ above-identity ⟹ MP
  (`aboveId_of_regressive_diWitness`; positive Q4: `measurePreserving_of_regressive_diWitness`).
- So an incomparable `F` has **no regressive witness** (`not_regressive_diWitness_of_incomparable`); its
  witness lifts `F`'s values cofinally, `g(F X) ≰ᵀ F X` (`diWitness_liftsValues_of_incomparable`).
- WLOG inflationary (`dominatedInvertible_inflationary`); then `F` is *strictly* Martin-below its
  invariant MP dominator `g∘F` (`incomparableDI_strictlyBelow_mp`).
- Honesty: "below an MP function" is **universal** (`everyInvariant_below_mp`, via `H X=(X⊕F X)′`); the
  real content is the dominator **factoring through `F X`** (`dominatedInvertible_mpFactorsThroughF`).
- Reading: a Q4 counterexample recovers `X` from an invariant *jump-type lift* of `deg(F X)` — matching
  `X ≤ᵀ (F X)′` while `F X ⊥ᵀ X`. `MP ⟹ DI` uses the *identity* (regressive) witness, blocked here.

**Q3 target (`¬DI` `F`): loses `X` below all jumps.**
- `notDominatedInvertible_escapes_jump`: since the jump is invariant, `X ≤ᵀ (F X)′` on a cone would
  witness DI; so `¬DI ⟹ X ≰ᵀ (F X)′` on every cone, and iterating, `X` escapes **every** jump-iterate of
  `F X`. A strong information-loss demand.

## Why no elementary contradiction (honest limit)

Both targets survive elementary attack, consistent with the problem's inner-model status:
- A DI-incomparable `F` could even have a *bounded* witness `g c = c ⊕ p` (fixed real `p`): then
  `X ≤ᵀ F X ⊕ p` while `F X ⊥ᵀ X` — countable-fibered on the cone. So the "dual escapes"
  `¬OnCone(X ≤ᵀ F X ⊕ p)` is **not** a theorem; the witness need only be non-regressive, not
  param-escaping. `incomparable_escapes_params` (known) constrains the *other* side (`¬ F X ≤ᵀ X ⊕ q`).
  The two sides never meet elementarily.
- The Q4 config `X ≤ᵀ (F X)′`, `F X ⊥ᵀ X`, fibers `⊆ {≤ᵀ (F X)′}` (countable), each `⊥ᵀ deg(F X)`, is a
  legitimate degree configuration; the open question is whether an **invariant** `F` realizes it on a
  cone — a genuine construction/forcing question, the inner-model frontier.

**Net:** the reduction of Part 1 to Q3/Q4 and to Marks's conjecture is now fully machine-checked, and
both disproof targets are sharply characterized (jump-type witness / jump-escaping value). The residue is
exactly the inner-model content — the RK-rigidity of `U_M` — open even under AD⁺.
