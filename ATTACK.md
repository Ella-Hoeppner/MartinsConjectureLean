# Attack log — the open core of Martin's conjecture

Living record of the direct attack on the **open** content of Part 1: the constraints a
counterexample must satisfy, prior proof attempts + exactly where they died, and a running
log of new counterexample-construction attempts. See `STATUS.md` for the codebase map.

## The open problem, precisely

Part 1 ⟺ two cores (`partI_iff_cores`), each open on the Turing degrees:
- **Regressive:** `F` invariant, `F X <ᵀ X` on a cone ⟹ `F` constant on a cone.
- **Incomparable:** `F` invariant, `F X ⊥ᵀ X` on a cone ⟹ `F` constant on a cone.

Equivalent single formulation (via the measure-preserving route): **escaping ⟹ MP**, i.e.
every escaping invariant `F` reaches every degree from above on a cone. Recast as an
incomparability statement (`escapingMP_iff_no_fixedIncomparable`): *no escaping invariant `F`
is Turing-incomparable to a fixed degree on a cone.*

`escaping F := ∀ Z, F X ≰ᵀ Z on a cone` (`= ¬ ConstantOnCone F` for invariant `F`).
Under determinacy a counterexample **cannot exist** (that *is* the conjecture, believed true),
so "construct a counterexample" is really a probe: under the `TuringDeterminacy` hypothesis it
must collapse, and *understanding the collapse* is where a proof idea would hide. A genuine
construction would need to drop determinacy (ZFC-only), which proves the weaker "AD is
necessary" — not a disproof of the AD conjecture.

## What a counterexample MUST look like (machine-checked constraints)

For invariant `F` under `TuringDeterminacy (fun _ => True)`:
- **Escaping = nonconstant** (`escaping_iff_not_constant`): a counterexample avoids every fixed
  degree from below on a cone.
- **Bounded ⟹ constant** (`bounded_implies_constant`): so a counterexample is *unbounded* — its
  kernel ideal `{Z : Z ≤ᵀ F X on a cone}` (a downward-closed, join-closed **Turing ideal**,
  `belowF_join`) is **not cofinal**; `mp_iff_belowF_cofinal` ⟹ it is bounded by some `W₀`.
- **Incomparable to a cone** (`counterexample_incomparable_cone`, needs `MartinPPT`): a
  counterexample (nonconstant, not-above-id) is escaping, non-MP, and Turing-**incomparable to
  every fixed degree ≥ᵀ W₀** on a cone. It is neither constant, nor above id — genuinely
  "sideways."
- **Ultrapower reading:** its class `[F]` in the cone ultrapower is a nonstandard degree with
  `W₀ < [F]`, yet `[F] ⊥ᵀ Z` for every standard `Z >ᵀ W₀`. Part 1 asserts no such `[F]` exists.

## Prior proof attempts and where they died

(A–C hit genuine mathematical walls still standing; D/E funneled through the universal machine,
which has **since been built** — those may be worth revisiting.)

- **A — join-limit coding (regressive).** Build `X₀ ≤ X₁ ≤ …` with `X_{n+1}` escaping
  `Z_n = ⊕_{k≤n} F(X_k)`, pass to `X_ω = ⊕ X_n`. Order-preservation gives `F(X_ω) ≥ F(X_n)`.
  **Died:** to contradict "range avoids `cone Z₀`" needs `F(X_ω) ≥ ⊕_n F(X_n)` (the ω-join), but
  an upper bound of each column need not compute the join *uniformly* — the Spector-exact-pair
  non-uniformity gap. Establishes only directedness.
- **B — Baire/topology.** Degree-classes and value-classes are all dense; `F(X_n) → F(Y)` gives
  `F(Y) ∈ closure(dense) = 2^ω` — no info. Martin measure ⊥ Baire category (cones are neither
  comeager nor null).
- **C — Posner–Robinson (incomparable).** `H(X) = X ⊕ F X` is invariant, strictly above id;
  relativized P–R converts incomparable info into jump-computations. **Died:** P–R itself
  (Kumabe–Slaman forcing) is unformalized and large; the surrounding Slaman–Steel argument also
  needs pointed perfect trees.
- **D — after index stabilization (uniform case).** A fixed `e` computes `F` on a representative
  of every degree on a cone. **Died (at the time):** controlling `Φ_e` across different
  representatives of the *same* degree is Steel's comparison-game analysis, which needed the
  universal machine. (Universal machine now exists; comparison-game analysis still to build.)
- **E — Steel's dichotomy game.** Payoff: II codes `(k,l,Y)`; if `Y ≡ᵀ X` via `(k,l)` then
  `X ≤ᵀ F Y`. II-wins ⟹ `F ≥ id` on a cone (executable via `gamePlay_le` + uniformity);
  I-wins ⟹ `F` bounded ⟹ constant. **Died (at the time):** the honest-play indices are a fixed
  point of a computable index map = the oracle Kleene recursion theorem, which needed `evaln`.
  (Now built — `exists_fixedPoint`. This attempt may be revivable for the uniform case, though
  the open problem is the *non-uniform* case where there is no single `e`.)

**Assessment (still true for the non-uniform open core):** the walls are non-uniformity
(A: no uniform ω-join / exact pairs), measure⊥category (B), and unformalized forcing (C). The
non-uniform core has no single index to grip, which is exactly why the human proofs (uniform,
hyperarithmetic) do not transfer.

---

## New counterexample-construction attempts (running log)

Format per attempt: **candidate F**, **why it might be sideways**, **what forces it to
collapse** (constant/above-id/contradiction), **insight extracted**.

*(none yet — begins with the next work session)*
