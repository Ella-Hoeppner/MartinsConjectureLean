# Breakthrough attempt on the incomparable core (2026-08-26, "try to invent the machinery")

*Goal: genuinely try to prove the incomparable core — no Turing-invariant `F` has `F X ⊥ᵀ X` on a cone —
inventing whatever machinery is needed. This logs the ideas tried, why each fails, and the precise
obstruction structure that emerged. Honest: not a solve; a tested map of the wall.*

The target is razor-sharp (repo's `incomparable_core_of_uniformization`): the entire open content is
**Steel's Conjecture 9.4** — every Turing-invariant `F` is Martin-equivalent to a *uniformly*-invariant `G`
(Slaman–Steel already prove Part 1 for the uniform class: `SteelUniformKernel`). Every equivalent form
(uniformity / RK-rigidity of `U_M` / `DominatedInvertible⟹MP` / Marks's dichotomy) reduces to this.

## The six walls (every elementary idea dies at one of these)

- **W1 — cone-orthogonality.** The cone filter is orthogonal to Lebesgue measure and Baire category: a cone
  is *meager and null*. So any regularity of `F` from AD (Baire property, measurability ⟹ continuity on a
  comeager/conull set) lives on a set that can (and for the incomparable core, *provably does*) miss the cone.
  **Proved here:** an incomparable `F` is *nowhere topologically continuous on the cone* — if `F` were
  continuous on a cone-realizing set then `F X ≤ᵀ X ⊕ code_F ≡ᵀ X`, i.e. regressive, contra incomparable. So
  the cone is forced into `F`'s discontinuity set; measure/category cannot see it.
- **W2 — fat fibers.** Any rank `r : D_T → Ord` (e.g. `X ↦ ω₁ˣ`) is non-injective; a rank with thin fibers
  would well-order `ℝ` (AD-false). So ordinal tools (strong partition relations on `ω₁`, `δ¹_{2n+1}`, normal
  measures) do **not descend** from the ordinals to sub-cones of degrees. (Confirmed against Jackson's
  partition theory: the strong partition relations are real, but the pullback through `X ↦ ω₁ˣ` fails on fat
  fibers.)
- **W3 — definable ≠ computable.** OD-from-a-real / membership in a generic extension `M[g]` / ∞-Borel-code
  membership do **not** bound Turing degree. (Reflection: `F g ∈ M[g]` for a cone-generic `g`, but `M[g]` has
  reals incomparable to `g`, so `F g ⊥ g` survives — no contradiction.)
- **W4 — countability.** Slaman–Woodin coding (the only degree-level definability engine) codes only
  **countable** relations by parameters; an invariant `F` is an uncountable relation on a cone. Making `F`
  parameter-definable on a cone would *prove Steel 9.4 for free* — confirmed impossible by the countability
  hypothesis of the Coding Theorem. (Thm 7.3.3 needs definability as *input*, not output.)
- **W5 — invariance mismatch.** A Turing-invariant `F` has outputs determined only up to `≡ᵀ`, not `≡_m`
  (or any finer/coarser reducibility). So `F` is **not** m-invariant, and Kihara–Montalbán's proven m-degree
  Martin's conjecture does **not** transfer (the near-miss "m-bootstrap" dies exactly here). Symmetrically no
  coarser-reducibility result applies.
- **W6 — circularity.** Every reformulation (uniformity, RK-rigidity, `DI⟹MP`, Marks's constant-or-injective
  dichotomy, "no injective incomparable `F`") is *equivalent* to the core. Proving any = proving the core.

## Ideas tried and where each dies

1. **Slaman–Woodin coding ⟹ `F` parameter-definable ⟹ uniform.** Dies at **W4** (codes only countable data).
2. **Reflection: `F g ∈ M[g]` for cone-generic `g` ⟹ `F g ≤ᵀ g`.** Dies at **W3** (`M[g]` has `⊥g` reals);
   minimal-generic patch fails (minimality bounds degrees *below* `g`, not `F g`).
3. **2-dimensional cone partition relation** (color pairs, homogeneous sub-cone, set `X=Y`). The relation is
   *false* for degrees: `c(X,Y)=[Y ≤ᵀ X']` has no homogeneous sub-cone. Ordinal partition relations don't
   pull back (**W2**).
4. **Least/simplest counterexample + scales / complexity descent.** Base case (hyp/Borel) is done, but the
   descent mechanism reduces to controlling definable reals' degrees (**W3**); counterexample is non-Borel
   (non-projective, per the frontier), living where fine structure is needed.
5. **Baire property: `F` continuous on comeager ⟹ pointed tree inside ⟹ `F` regressive on its cone.** Dies
   at **W1** (proved: incomparable `F` is nowhere-continuous on the cone; comeager set misses the cone).
6. **Canonical representative via a pointed perfect tree** (`G X = F(code_T X)`). `code_T X` depends on the
   *real* `X` not its degree, so `G` inherits `F`'s non-uniformity. Composing with the uniform "code" map
   does not uniformize `F` (**W6**).
7. **Uniformity game** (II blind to `X`, produces the reduction index). II wins ⟺ `F` uniform; determinacy
   lets I win (⟺ non-uniform) with no contradiction — matches Marks's "determinacy doesn't work for
   non-uniform" (**W6**).
8. **m-degree bootstrap** (Kihara–Montalbán). Dies at **W5** (Turing-invariant ⇏ m-invariant).
9. **Lawvere / diagonal fixed-point** (universal invariant function ⟹ fixed point `F X ≡ᵀ X`). Dies at
   cardinality: `2^𝔠` invariant functions, only `𝔠` real-parameters — no point-surjection (**W4**-flavored).
10. **∞-Borel code of `F`'s graph ⟹ extract a reduction.** The code is a set of *ordinals*; transferring it
    onto a cone is Steel's conjecture (**W6**), and the ordinal code has fat fibers (**W2**).

11. **Pointed-tree lemma on the reduction-index coloring.** `h_{i,j}(X) = least index reducing `F(Φ_i^X)` to
    `F X`` is **ℕ-valued** — so I hoped Martin's pointed-tree lemma (countable-range coloring ⟹ constant on a
    pointed tree) would give uniformity on a cone. Dies at **W1/non-invariance**: `h_{i,j}` is *not
    degree-invariant* (the least reduction index depends on the real `X`), so the pieces `{h_{i,j}=k}` are not
    invariant and cone-completeness gives no cone-large piece. (If it worked it would prove Steel's conjecture,
    which is open — confirming the flaw.) *This is the crisp form of the whole difficulty: the reduction
    indices are not degree-invariant.*
12. **Canonical/degree-representative reparametrization** (`G X = F(rep of deg X)`). Machine-checked dead by
    the parallel agent: `canonicalRepresentative_no_gain` (`CanonicalRepresentative.lean`) — for any fixed
    computable degree-preserving coding `c`, `F∘c` is uniformly invariant **iff** `F` is. A *degree*-canonical
    rep (constant on ≡ᵀ-classes) would make `G` trivially uniform, but it is not computable-from-`X` (it is
    `ω₁↪ℝ`). So input-reparametrization is provably **uniformity-neutral**: the obstruction is entirely in
    `F`'s *values*, and altering values uniformly = canonical value-selection = `ω₁↪ℝ` (blocked).

## Frontier facts pinned by the deep-dives (sourced)

- The proved/open boundary is **structural, not by pointclass** (Lutz thesis §1.7): uniform, regressive,
  order-preserving, measure-preserving are done (ZF+AD, some +DC_ℝ); **arbitrary non-uniform is open even for
  Borel `F`**. So there is no "level `n`" to induct on — complexity descent is not the lever.
- **No `T`-invariant function is known that is not uniformly `T`-invariant** (Nakid-Cordero). Consistent with
  "every invariant `F` is uniform" (⟹ Part 1), but no proof — and I proved `incomparable ⟹ ¬uniform`, so a
  non-uniform example ⟺ (essentially) a counterexample.
- Target label fix: it is **Steel's Conjecture 1.4** (Marks–Slaman–Steel), not "9.4". Open for every class
  incl. Borel; its Borel form is *equivalent* to Borel Martin's Conjecture (Marks) — a genuine reframing, not
  a shortcut (**W6**).
- Under full AD in `L(ℝ)` there is **provably no counterexample within `L(ℝ)`**; the RK-rigidity of `U_M`
  (Lutz–Siskind Thm 5.15) is the un-stratified equivalent, open even with current inner-model theory.

## The actual open mathematical content (what a real breakthrough must deliver)

Stripped of reformulations, the one thing needed is **cone-specific fine control of the Turing degrees of an
arbitrary AD-invariant object**, in one of these equivalent forms:
- **Kill case-2 of the Siskind trichotomy** (thesis Thm 1.5.8): no nonprincipal `V ≤_RK U_M` on `D_T`
  concentrates on complements of cones. Prop 5.24 is the *only* known `V = U_M` tool and needs the
  concentration hypothesis, which RK-equivalence doesn't supply. Siskind: *"a complete analysis of the
  countably-complete ultrafilters on `D_T` would decide Part 1 … may be a site of more tractable problems"* —
  the honest frontier, open even under AD⁺ / AD+V=L(𝒫ℝ).
- **Prove Steel's Conjecture 1.4** for one invariant `F` at a time via *value*-cleanup (input-side is
  machine-checked neutral). No canonical value-selection exists without `ω₁↪ℝ`.
- **Prove Marks's conjecture** (constant-or-injective on a *pointed* perfect tree) — the strict half; the open
  step is a pointedness-preserving Silver/Galvin–Prikry fusion.

All three need the **fine-structural / ultrafilter-theoretic** machinery of Steel–Siskind–Goldberg on `L(ℝ)`
(iterated ultrapowers of `HOD`, the Ketonen/Rudin–Keisler order), and even there the RK-rigidity of `U_M` is
open. This is not an elementary gap; it is at the edge of what set theory currently knows.

**The precise inner-model target (derived this session).** `V ≤_RK U_M` via `f` gives a factor map
`k : Ult(V) → Ult(U_M)` elementary, with `k([id]_V) = [f]_{U_M}`; `V = U_M ⟺ k = id`. By
Goldberg–Sargsyan–Siskind, `Ult(U_M)` is an iterate of `HOD` (`AD + V=L(𝒫ℝ)`), and iterates are linearly
ordered (Ketonen). So **RK-rigidity ⟺ `U_M`'s `HOD`-iterate is minimal/isolated among the iterates arising
from countably-complete ultrafilters *on `D_T`***. A case-2 `V` yields a *proper* iteration `k` (critical
point moves `[id]` to the sideways `[f]`) — internally consistent, no contradiction — so the rigidity is
exactly the (open) statement that no such proper factor map from a `D_T`-ultrafilter into `Ult(U_M)` exists.
This is Siskind's "classify the countably-complete ultrafilters on `D_T`", which he flags as *possibly* more
tractable but which no one has done. That is the sharp target for a genuine breakthrough.

## Convergence (the routes are one wall)

A refinement from this attempt's parallel probes: the two routes I earlier called "different walls" are the
**same** wall. The **Marks / pointed-tree (combinatorial)** route: building a pointed tree on which invariant
`f` is *injective* requires a **computable injective witness** to thin against (pointedness comes from
tree-thinning à la Sacks/Spector, *not* Groszek–Slaman coding — a corrected attribution); such a witness
exists iff `f` has a **modulus** iff `f` is **measure-preserving**. So the strict-half (Marks) route bottoms
out at exactly the **measure/RK-rigidity** content, not a separate combinatorial gap. Every route — measure,
Marks, coding, games, partition, reflection, ultrafilter — converges on the single statement: *there is no
invariant control of an arbitrary invariant function's Turing-value-distribution on a cone.* That statement is
RK-rigidity of `U_M` / Steel's Conjecture 1.4, and it is open even with current inner-model theory.

## Honest structural conclusion (so far)

The incomparable core is equivalent to **cone-specific regularity of `F`** (uniformity / continuity on a
cone), which is *orthogonal* to every AD-available regularity (measure, category — W1) and every
ordinal/coding tool (W2, W4), cannot be extracted from definability (W3) or a finer reducibility (W5), and
every reformulation is circular (W6). The one tool that overcomes W1–W5 — **fine-structural control of the
Turing degrees of definable reals inside `L(ℝ)`** (Steel–Siskind mouse/ultrapower theory) — is exactly what
the community uses, and even there the RK-rigidity of `U_M` is *open*. So the problem is open *even with*
inner model theory, not merely beyond an elementary attack.

## Second round (2026-08-26, parallel frontier probes) — two sharpenings, two hard no-gos

Two independent deep-dives against the sharpest target (kill Siskind case-2 / prove Steel 1.4), each reading
fresh primary sources. Both bottomed out at the *same* wall from opposite sides, but each produced a genuine,
machine-checked contribution and a genuine no-go that removes a route.

**(A) Ultrafilter / inner-model side — `CountableKernel.lean`, `MARTIN_COUNTABLE_KERNEL.md`.**
- **Hard no-go (verified verbatim against Goldberg's book):** the Ketonen order / UA / Dodd-sound comparison
  machinery is defined *only for ultrafilters on a wellordered set* (Def 3.5.10). Under AD, `D_T` is not
  wellorderable, so this apparatus **does not even type-check for `U_M`** — the "obvious" inner-model weapon
  is inapplicable. GSS iteration trees reach `Ult(HOD, U_M)` but represent a *single* ultrapower with **no
  comparison/rigidity theory between two `D_T`-ultrafilters**. Commutativity/Fubini is RK-*downward* closed,
  so it constrains ultrafilters *above* `U_M` and gives nothing about predecessors below.
- **Machine-checked sharpening:** for a case-2 predecessor `V = F_*U_M`, the Prop-5.24 concentration set
  `{d | Cone(d) ∈ V}` **equals** the repo kernel `BelowF F` exactly, and (Prop 5.24 + PSP + Cor 4.5) it is
  **countable — bounded by a single real `r_K`** (`case2_kernel_bounded_of_countable`; the "countable ⟹ one
  real" step is now fully in-repo via `Cantor.joinFam`, no `DC_ℝ`). Strictly sharper than the prior "kernel
  avoids a cone."

**(B) Value-cleanup / independence side — `ValueCleanup.lean`, `MARTIN_VALUE_CLEANUP_AND_INDEPENDENCE.md`.**
- **Machine-checked value-side no-go:** the input-side neutrality (`canonicalRepresentative_no_gain`) now has a
  value-side twin. A *fixed, binary-uniformly-invariant, value-preserving* cleanup `G x = Ψ x (F x)` is
  Martin-equivalent to `F` and **uniform iff `F` is** (`valueCleanup_no_gain`) — `Ψ` can only *forward* `F`'s
  witness. The degree-changing join cleanup `x ⊕ F x` provably **breaks** Martin-equivalence on the
  incomparable core (`join_cleanup_breaks_equiv`). **Trichotomy:** a value-cleanup is neutral, or breaks
  equivalence, or is itself as non-uniform as Steel 1.4. This sharpens W6 (circularity) to the value side.
- **Independence verdict — NO (and why):** the two known ways Part 1 *fails* both need structure `D_T` lacks.
  The ZFC failure (Lutz Thm 5.27) needs a wellorder of the degrees — refuted by AD. The enumeration-degree
  failure (Nakid-Cordero, arXiv:2510.19147, a ZF theorem and the exact `e`-analogue of the incomparable core)
  needs **nontrivial Kalimullin pairs + non-total (quasiminimal) degrees**, both **ZF-provably absent in
  `D_T`** (semicomputable pair-halves `{A, Ā}` are Turing-*equal*; every Turing degree is total). So the
  `e`-failure exploits precisely what `D_T` lacks — evidence *for* the Turing conjecture. No AD-model failure
  is known or conjectured; the working verdict is Part 1 is **true under AD**, open content = RK-rigidity.
- **Sourced correction (flag, not yet reconciled across memory):** (B) reports Lutz–Siskind order-preserving
  Part 1 as a theorem of **ZF + AD + DC_ℝ** (Thm 3.7), *not* requiring Uniformization_ℝ. This contradicts the
  older memory note ("under AD+Unif_ℝ"). Recorded as the agent's source-read; I did **not** independently
  re-verify the citation, so both are flagged rather than one silently overwritten.

## Synthesis: the sharpened profile of a minimal counterexample ("thin-below, sideways-valued")

Combining the two machine-checked sides, a case-2 / escaping counterexample `F` (if one exists) is pinned
between two provable facts:
- **Thin below:** its entire domination kernel `BelowF F` is bounded by a *single* real `r_K`
  (`case2_kernel_bounded_of_countable`) — `F X` cofinally computes no fixed real above `r_K`.
- **Sideways valued:** yet `¬(F X ≤ᵀ X ⊕ r_K)` on every cone (`no_regressivity_relative_to_kernel_bound`,
  from the KNOWN Slaman–Steel escaping theorem) — the value is not computed by the argument-plus-`r_K` either.

So `F X` is a "generic-looking" degree: it dominates essentially nothing fixed, and is computed by essentially
nothing fixed relative to `X`. This is the exact machine-stated shape of the obstruction — the per-`X`,
per-degree `{0,1}` fact `F X ⊥ᵀ d` that no countably-complete / ordinal / measure tool can aggregate (doing so
would embed `ω₁ ↪ ℝ`). Both sides converge here; neither can cross.

**The one live lead (not through Goldberg's inapplicable apparatus):** Lutz thesis §5.11 — if the
`I`-positive-set forcing `P_I` for the dual ideal `I = {A | A ∉ V}` is *proper* (does not collapse `𝔠`), then
`V ⋠_RK U_M`. The new "kernel bounded by one real `r_K`" fact makes `P_I` a highly constrained, single-real-
parametrized forcing — exactly the regime where a properness argument has a foothold. Turning "case-2 ⟹ `P_I`
proper" into a theorem would close RK-rigidity. That is the concrete next target; it is genuinely inner-model /
forcing-theoretic but does **not** require the (AD-inapplicable) Ketonen/UA machinery.
