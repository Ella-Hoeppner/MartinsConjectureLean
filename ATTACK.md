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

## BOTTOM LINE (the barrier — read this first)

Explored ~a dozen angles (index stabilization, Steel's game, Posner–Robinson, descending
chains, RK/pushforward order, measure⊥category, continuity-on-comeager, the cone ultrapower,
normality/Fodor, biinterpretability, definability). **They all funnel to ONE barrier:** no
determinacy tool extracts a *Turing code* (`Φ_e`) from an arbitrary invariant `F`. Sharpest
form: AD supplies **definable** uniformization (a selection), but Martin's conjecture needs
**Turing** uniformization (`F = Φ_e` on a cone) — and definable ≠ Turing-uniform. Equivalently:
the good-representative set `G_e = {Y : F Y = Φ_e^Y}` is non-invariant, so `cone_theorem` can't
show it contains a cone; index stabilization gives one good rep per degree but selecting them
uniformly needs uniformizing an `F`-defined (non-definable) relation. The known proofs (uniform,
Borel, hyperarithmetic) all inject a definability/uniformity hypothesis the general case lacks.

**The barrier as THREE walls (root cause).**  Every formalizable technique needs one of three
things about `F`, and an arbitrary invariant `F` denies all three:
1. *Effectiveness* — recursion-theoretic / self-reference / coding arguments (incl. Posner–Robinson,
   Steel's game, the recursion theorem `exists_fixedPoint`) need `F` as an **oracle/code**.  But `F`
   is a function on *all* reals, not a single real — it cannot be oracle-ized.  (Fixing a countable
   restriction loses invariance.)
2. *Effective selection* — determinacy (AD) gives **definable** uniformization of the good-rep
   relation `G_e`, never a **Turing** functional.  Definable ≠ Turing-uniform.
3. *Cone-compatible regularity* — AD's measure / Baire regularity lives on comeager/conull sets,
   which are **orthogonal** to Turing cones (cones are meager AND null); regularity never transfers
   to a cone.
The three known proofs each *supply* a missing wall by hypothesis: uniform/Borel give (1)+(2)
(a code), hyperarithmetic gives an ordinal-effective handle.  The general case has none.  A crossing
must manufacture one of the three for non-definable `F` — no formalizable route does.

**Progress made:** the counterexample profile is now machine-checked and sharp (below), and the
barrier is precisely located. **Not found:** any crossing. A genuine crossing needs a *new idea*
to get Turing-uniformity from AD for non-definable functions — or the two unformalized classical
inputs (Steel's game / Posner–Robinson forcing). Correct partial constraints are all we have.

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

### Session 2026-08-21 (constraint-pushing + construction probes)

**Reformulation (conceptual).** Part 1 ⟺ **`[id]` is the least *nonstandard* degree in the
cone ultrapower** `D^ω/U` (constant-on-cone = `[F]` standard; above-id = `[F] ≥ [id]`; so Part 1
= "every nonstandard `[F] ≥ [id]`"). Regressive core = "no nonstandard `[F] < [id]`"; incomparable
core = "no `[F] ⊥ [id]`". Suggests a minimality/descending-chain proof — but the degrees are not
well-founded and the ultrapower isn't either, so descending `[id] > [F] > [F²] > …` gives no
contradiction (exact pairs). Not yet formalized (needs the ultrapower object).

**Why counterexamples exist in ZFC (construction probe #0).** An AC-choice function `g(d) < d`
on the (non-minimal) degrees of a cone is a regressive non-constant invariant `F` — a genuine
ZFC counterexample. It is non-measurable / not determined; under `TuringDeterminacy` it cannot
exist. **Confirms**: the conjecture's whole content is that determinacy forbids this choice; a
"disproof" is only possible by dropping AD (proving AD necessary), not against the AD conjecture.

**Diagonal against a counterexample — deep failure analysis.** Want a contradiction from
`F X ⊥ Z` (all fixed `Z ≥ᵀ W₀`). Natural move: `Z := F A ⊕ W₀ ≥ᵀ W₀`, then `F A ⊥ Z` but
`F A ≤ᵀ Z` — contradiction *iff* `A` lies in the (Z-dependent) incomparability cone `C_Z`. **Dies**
on circularity: `C_Z`'s base depends on `Z = F A ⊕ W₀`, i.e. on `A`. A limit/fixed-point
construction `A_ω = ⊕ A_n` (with `A_{n+1} ∈ C` growing) still dies: `F(A_ω)` is a *fresh
incomparable* value `⊥ ⊕_n F(A_n)` — F escapes even the ω-join of its own values. This is exactly
the exact-pair / non-uniformity wall (= old Attempt A). **Structural fact behind it:** there is
*no uniform incomparability base* — for any `X`, `F X` is comparable to `F X ⊕ W₀ (≥ᵀ W₀)`, so
"F X ⊥ all Z ≥ W₀ on one cone" is self-contradictory; the non-uniformity is essential.

**Index-stabilization + Steel's game — precise gap (revisiting Attempt D/E now that the
universal machine + recursion theorem exist).** `exists_uniform_index_on_cone`: a regressive
invariant `F` has a *fixed* code `e` with `F Y = Φ_e^Y` on a *representative* `Y` of every degree
on a cone (uniform-on-reps). Steel's game (II codes a rep, payoff via `Φ_e`) needs, in the
**I-wins ⟹ F bounded** direction, to bound `F` on the plays — but I cannot force a play to be a
*good representative* (where `F = Φ_e`), and off reps `F ≠ Φ_e`. **Precise open gap:** bridging
uniform-on-reps to controllable-on-plays. This is exactly why Steel's uniform proof does not
transfer; the recursion theorem removes the *old* blocker but not this one.

**Formalized this session (`CounterexampleConstraints.lean`):**
- `nonMP_incomparable_interval` — degrees `≤ᵀ W₁` are countable, so countable completeness of
  the cone filter upgrades the per-Z incomparability to: a counterexample is `⊥` **every** degree
  in `[W₀, W₁]` on a *single* cone, for each fixed `W₁`. Still doesn't close (F escapes any fixed
  `W₁`: `F X ⊥ W₁ ⟹ F X ∉ [W₀,W₁]`), but a real sharpening.

**Kernel structure (correction).** `mp_iff_belowF_cofinal` gives: `¬MP ⟹` kernel is **not
cofinal** ⟹ `∃ W₀`, kernel `⊆ {Z : W₀ ≰ᵀ Z}` (kernel is *disjoint from `cone W₀`*, downward+join
closed). NOT "`⊆ {≤W₀}`" (an earlier miscalc) — the kernel may contain `W₀`-incomparable degrees.
So the clean incomparability is exactly `Z ≥ᵀ W₀` (`nonMP_incomparable_cone`); "Z ≰ᵀ W₀" does
**not** follow.

**META-INSIGHT (why strategy 2 has a hard ceiling).** A counterexample must be **non-definable**:
any Borel/definable invariant `F` is *uniform* on a cone (Slaman–Steel) hence satisfies Part 1
(`partI_uniform`). So *no concrete `F` can ever be a counterexample* — every writable candidate
collapses to constant-or-above-id or fails to be invariant. Construction probes (below) only teach
us *why* concrete regressive attempts collapse.

**META-INSIGHT (the real gap, measure-level vs function-level).** Determinacy gives *set*-level and
*measure*-level cone-regularity: `cone_theorem` (invariant set ⊇ cone or ⊆ complement) and
`pushCone_dichotomy` (`[F]=F_*U` is an ultrafilter). Part 1 needs *function*-level regularity: `F`
**uniform on a cone**. AD's own regularity (measurable / Baire property) is w.r.t.
measure/category, which are **orthogonal to the cone filter** (Attempt B). So AD does not *directly*
hand us cone-uniformity; bridging `F_*U`-is-an-ultrafilter → `F`-uniform-on-a-cone is the
irreducible open content (= the `partI_of_uniformization` hypothesis). Every attempt funnels here.

**Construction probes (strategy 2), all collapse:**
- **#0 AC-choice** `g(d)<d` on a cone: a genuine ZFC regressive counterexample; non-measurable,
  gone under AD. (Confirms AD-necessity, not an AD-disproof.)
- **#1** `F X = 0'` if `X ≥ᵀ 0'` else `X`: definable, regressive-looking; **collapses to the
  constant `0'`** on `cone 0'`. Pattern: a definable "floor" is eventually a fixed floor = constant.
- **#2** `F X =` largest degree `≤ᵀ X` in a fixed countable ideal `I`: on `cone (⊕I)` it is the
  constant `⊕I`. Same collapse. Any definable regressive rule has a fixed "target" on a cone.

**The reps→all-X gap, made precise (multiple angles all agree).** `exists_uniform_index_on_cone`
gives a *single* code `e` with `F Y = Φ_e^Y` on a *representative* `Y` of each degree. For any `X`,
picking a good rep `Y_X ≡ᵀ X` (so `Y_X = Φ_{b_X}^X`) gives `F X ≡ᵀ Φ_e^{Y_X} = Φ_{e∘b_X}^X`
(via `eval_trE_comp`) — a *per-X* code `c_X = e∘b_X`. A *single* code on all `X` (⟹ the uniform
case, `regressive_uniform`, done) needs a **uniform** `b` computing a good rep. But:
- verifying "`Y` is a good rep" needs `F` (non-computable) ⟹ can't *search* for `Y_X`;
- selecting `Y_X` uniformly is a **uniformization of the relation "`Y` good rep of `X`"**, which is
  *defined via `F`* ⟹ non-definable ⟹ AD-uniformization doesn't apply.

So the single unclosable gap = **uniform selection of a good representative**, blocked because `F`
is non-definable. Every route (measure→function bridge, reps→all-X, good-rep uniformization) is the
*same* barrier: no determinacy tool extracts a code from an arbitrary invariant function. This is
why the known proofs all require a definability/uniformity input the general case lacks.

**Assessment of this session.** Formalized 3 correct new constraints (`nonMP_incomparable_interval`,
`counterexample_full_profile`, + the earlier `nonMP_incomparable_cone` family). Located the barrier
precisely and confirmed it from 4 independent angles. No crossing found — none expected; a genuine
crossing would be Steel's game (multi-session, and even then only bridges reps with the above gap)
or Posner–Robinson (unformalized forcing). The constraint profile is now sharp enough that a future
attempt should target the **uniform-good-rep-selection** gap directly (or accept Steel's game as the
formalization target for the *uniform-on-reps* fragment).

**Pushforward-action / RK-descent idea (partial, `pushCone_comp` formalized).** The pushforward
`F ↦ F_*U` is a monoid action: `(F∘G)_*U = F_*(G_*U)`, so `[Fⁿ] = F_*ⁿ U`. A regressive `F` would
give a candidate descending sequence `[F] > [F²] > …`. **Two obstructions:** (a) the *descent isn't
established* — `[F²] <ₘ [F]` needs `F X` to land back in the regressive cone, which fails because `F`
escapes its own domain (same non-uniformity wall); (b) even granting descent, well-foundedness of
the descent is either RK-well-foundedness of the cone ultrafilter (uncertain / possibly open) or the
**Martin order well-foundedness = Part 2** (also OPEN) — so it's circular. If (a) were fixed and RK
were well-founded, one would get "a regressive counterexample is *injective* on a cone" (injective ⟹
`F_*U ≡_RK U`, no strict descent) — but injective-regressive (`[F] ≡_RK U` yet `[F] <ₘ [id]`) is
still consistent-looking (RK-order ≠ Martin-order). Net: interesting structure (`pushCone_comp` is a
clean correct fact), no crossing.

**Descending chain (FORMALIZED, `regressive_conePreserving_descending_chain`) — and a CORRECTION.**
A regressive *cone-preserving* invariant `F` (on `cone base`: `F X <ᵀ X` **and** `base ≤ᵀ F X`) has
iterates `F ≻ₘ F² ≻ₘ …` strictly Martin-descending. **I initially claimed this refutes Part 2 — that
is WRONG.** `DescendingChainCore` (Part 2 as formalized) forbids descending chains of `Regular`
(= `Measurable ∧ TuringInvariant ∧ AboveIdOnCone`) functions; these iterates are *below* id, a region
the conjecture does NOT claim to well-order. So the chain is a structural fact about the below-id part
of the Martin order, **not** a cross-half contradiction. (Below-id descending chains are expected;
they don't contradict anything.) The theorem is correct; its significance is smaller than I first
stated. Two independent wounds: (a) the cone-preserving hypothesis is generally false (cone-escape
wall), and (b) even granting it, no Part-2 contradiction (wrong region). Net: no leverage.

**Attempt to remove the cone-preserving hypothesis via `G := F ⊕ base` — FAILS (same wall).** `G X =
F X ⊕ base` is trivially `≥ᵀ base`. Splitting via `cone_theorem` on `{X : X ≤ᵀ G X}`: either
`X ≤ᵀ G X` on a cone (special form `F X ⊕ base ≡ᵀ X`) or `X ≰ᵀ G X` on `cone Y`, making `G`
regressive on `cone(Y⊕base)`. But `regressive_conePreserving_descending_chain` needs a *single* base
that is both the regressive base (`Y⊕base`, for strictness) **and** `≤ᵀ G X` (cone-preserving). `G` is
cone-preserving only above `base`, regressive only above `Y⊕base`, and `Y ≰ᵀ G X` (no reason `Y ≤ᵀ
F X`). So `G(G X)` is again uncontrolled — the regressive base `Y` isn't below `G`'s values. The
non-uniformity/cone-escape wall reappears exactly. So the cone-preserving hypothesis is *not* removable
this way; `regressive_conePreserving_descending_chain` stays genuinely conditional.

**Live ideas still untried:** (ii) formalize the ultrapower/Martin-order object
to state "[id] least nonstandard" first-class (≈ the existing Martin order; likely no new leverage).
(iii) forcing-free Posner–Robinson via `cone_contains_PPT` (unclear trees replace Kumabe–Slaman).
(iv) Steel's game for the uniform-on-reps fragment (hits the good-rep gap; recursion theorem now
available).
