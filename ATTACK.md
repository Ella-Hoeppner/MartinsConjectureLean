# Attack log — the open core of Martin's conjecture

Living record of the direct attack on the **open** content of Part 1. See `STATUS.md` for the map.

> **⚠️ MAJOR CORRECTION (2026-08-23).** The **regressive core is NOT open** — it is a KNOWN
> Slaman–Steel theorem (Part 1 holds for all regressive functions on the *Turing* degrees;
> Lutz–Siskind Thm 1.4).  The **sole genuinely-open content of Part 1 is the incomparable core.**
> Almost everything below (the ω₁^x machinery, the jump-distance decomposition, the "reduction of
> the regressive core to the ω₁-preserving case", the whole "regressive is 50-year-open" framing)
> was built on the mistaken premise that the *Turing* regressive core is open — it isn't; that was a
> conflation with Lutz's **hyperarithmetic-degrees** regressive result (`arXiv:2306.05746`, a
> different degree structure).  The ω₁^x formalization is still valid mathematics, but it was aimed
> at an already-solved problem.  Read the rest of this file with this correction in mind; the genuine
> open target is the incomparable core.  See `Reduction.lean`: `RegressiveSlamanSteel`,
> `regressiveImpliesConstant_of_slamanSteel`, `partI_of_slamanSteel_incomparable`.

## The open problem, precisely

Part 1 ⟺ two cores (`partI_iff_cores`):
- **Regressive:** `F X <ᵀ X` on a cone ⟹ constant.  **KNOWN (Slaman–Steel), not open.**
- **Incomparable:** `F X ⊥ᵀ X` on a cone ⟹ constant.  **The sole open core.**

### Why the "contradictory constraint-set" strategy is BOUNDED (2026-08-22 finding)

Goal of that strategy: pile up machine-checked constraints on a counterexample until they conflict
(a conflict = a proof).  I pushed this hard and found a *structural reason it cannot succeed with
cone-theorem-level tools alone*:

> Every constraint derived from `cone_theorem`/σ-pigeonhole is satisfiable by a **consistent
> descending model**, because `≤ᵀ` (and `≤ₐ`, and `≤_h`) is **ill-founded**.

Concretely: the constraints say the counterexample's values escape every fixed bound (`escaping`,
`arithmetically_bounded_implies_constant`), are incomparable to cones of fixed degrees, and either
preserve or drop the arithmetic degree (`regressive_jump_dichotomy`).  Iterating `F` gives
`X >ᵀ FX >ᵀ F²X >ᵀ …` (or `>ₐ`), all escaping every *fixed* `c`.  An infinite `≤ᵀ`-descending chain
whose members are all incomparable to a fixed `c` **exists** (ill-foundedness), so no finite
combination of these constraints is contradictory.  A genuine contradiction needs a **well-founded
rank** that `F` must strictly decrease — and the only such rank on the degrees is the *ordinal*
`ω₁^x`, which lives at the transfinite hyperarithmetic level and is not delivered by the cone theorem
(this is exactly Lutz's `Σ¹₁`-bounding, hyp-only).  So the constraint-tightening strategy tops out
precisely at the `ω₁^x` barrier — it sharpens the *shape* of a counterexample but cannot close it.

(A different angle with the *same* ceiling: `≡ᵀ` is Lebesgue-**ergodic** — cones are Lebesgue-null,
Sacks — so a measurable invariant `F` has `F_*Leb` a `{0,1}`-measure on invariant sets.  But
`F_*Leb` concentrates on Lebesgue-conull sets, *orthogonal* to the (null) cones; and "regressive
⟹ `F_*Leb` principal" needs the same well-founded rank.  Measure-ergodicity is not the cone measure.)

### NEW (2026-08-22): jump-distance decomposition of the regressive core (`RegressiveJumpDecomp.lean`)

The regressive core = *"the cone measure is normal w.r.t. `≥ᵀ`-regression."*  Standard Fodor
fails because `≥ᵀ` is not well-founded.  **New idea:** every Turing degree has only *countably
many* predecessors, so a σ-pigeonhole runs on the degree-invariant, `ℕ∪{∞}`-valued jump-distance
`n(X) = least n with X ≤ᵀ (F X)^(n)`.  `regressive_jump_dichotomy` (machine-checked, std axioms):
on a cone, **either**
- **Case B** `X ≤ᵀ (F X)^(k)` for a fixed `k` — with `F X ≤ᵀ X` this is `F X ≡ₐ X`, i.e. `F`
  *preserves the arithmetic degree* while dropping the Turing degree (the finitary case), **or**
- **Case A** `X ≰ᵀ (F X)^(n)` for all `n` — `F X` arithmetically *strictly* below `X`.

This cleanly isolates the finitary part (Case B) from the transfinite part (Case A = Lutz's `ω₁^x`
hyperarithmetic regime; the levels there are `ω₁^x`-many, X-varying, so the fixed-countable
σ-pigeonhole cannot reach — this is exactly Lutz's `Σ¹₁`-bounding difficulty).

**Where both cases stall (honest):** *the same core barrier survives in each.*
- *Case B:* the reduction `X ≤ᵀ (F X)^(k)` has a code `e(X)` between the *reals* `X` and
  `(F X)^(k)`, non-degree-invariant, so no second σ-pigeonhole stabilizes it; and `F X ≡ₐ X` only
  says `F` descends *within one arithmetic degree*, which is **not** well-founded under `≤ᵀ` (so no
  Fodor there either).  Iterating `F` gives a descending chain inside an arithmetic degree — consistent,
  no contradiction.  Routing through Part 2's finite `[id, J_k]` interval structure is circular (Part 2
  also open).
- *Case A:* iterating `F` gives an *arithmetically*-descending chain `X >ₐ FX >ₐ F²X >ₐ …`; the
  arithmetic degrees are **not** well-founded under `≤ₐ`, so this descends forever with no
  contradiction unless one imports `ω₁^x` well-foundedness (Lutz, hyp-only).

So the decomposition is a genuine new *reduction of the open core to two sharper sub-cores*, and it
pinpoints that the sole obstruction is the **absence of a well-founded rank on the Turing degrees**
(the `ω₁^x` rank that resolves it exists only on the hyperarithmetic degrees).  Not a proof; a precise
map of exactly what a proof must supply.

**The resolution mechanism (what a proof of Case A must use).**  Under AD the cone measure `U`
pushes forward to the **club filter on `ω₁`** via `X ↦ ω₁^x` (the Lutz connection), and the club
filter *is* normal (Fodor on `ω₁`).  Split Case A by cone theorem on `{X : ω₁^{F X} < ω₁^X}`:
- *strict* (`ω₁^{F X} < ω₁^X` on a cone): `X ↦ ω₁^{F X}` is a **strictly regressive** function on
  `ω₁` mod the club filter, so **Fodor on `ω₁`** pins `ω₁^{F X} = γ₀` *fixed* on a cone.  (But `F X`'s
  *degree* stays unbounded — reals with a fixed `ω₁` are cofinal — so this is not yet constancy;
  Lutz's finer coding closes it.)
- *preserving* (`ω₁^{F X} = ω₁^X`): `F` preserves `ω₁^x`; this is the delicate heart of Lutz's
  hyperarithmetic argument.

**SHARPER FRAMING (2026-08-22, a correction).**  A regressive `F` splits via `regressive_omega1_dichotomy`
into **hyp-decreasing** (`ω₁^{F X} < ω₁^X`, i.e. `F X <_h X`) and **hyp-preserving** (`ω₁^{F X} = ω₁^X`,
i.e. `F X ≡_h X` since `F X ≤_h X`).  Crucially, the **hyp-decreasing case is killed by the engine**
(`no_omega1_decreasing_conePreserving`): iterating a cone-preserving such `F` gives a strictly
`≺`-descending `ω₁^x` sequence, impossible by countable completeness — *no Σ¹₁-bounding needed*.  And
hyp-decreasing is *all* of Lutz's `D_h` regressive setting (on `D_h`, `F X <_h X` always strictly drops
`ω₁`).  So the engine gives a clean, novel handling of the "Lutz-hard" case on the Turing degrees
(modulo cone-preservation).  The genuinely-open residual is the **hyp-preserving Turing case**
(`F X ≡_h X`, `F X <ᵀ X`, nonconstant) — a *Turing-specific* phenomenon that is **vacuous on `D_h`** (so
Lutz's method never sees it) and admits no ordinal rank (the Turing degrees inside a single hyperarithmetic
degree are ill-founded).  This is the precise, corrected open content — NOT "port Lutz's Σ¹₁-bounding",
but a new phenomenon needing a new idea (or the cone-escaping cases, the cone-preservation caveat).

**NOW PARTLY FORMALIZED (2026-08-22, `OrdinalUltrapower.lean` + `ChurchKleene.lean`).** The *engine*
is machine-checked: `no_descending_ordinal_cone` (the cone measure's ordinal ultrapower is well-founded
— countable completeness) and `no_regressive_of_ordinal_rank` (regressive core ⟸ a degree-invariant
ordinal rank `F` strictly decreases).  And the rank itself: `churchKleene` = relativized `ω₁^X` (sup of
order types of `X`-computable well-orders, guarded `≤ᵀ X`), with `churchKleene_mono` + `churchKleene_invariant`
proven; `no_omega1_decreasing_conePreserving` + `regressive_omega1_dichotomy` then give: **a
cone-preserving regressive counterexample is `ω₁`-preserving** (`ω₁^{F X} = ω₁^X` on a cone) — the
`ω₁`-decreasing case is killed by the engine.  So the reduction *to the `ω₁`-preserving case* is now
machine-checked.  What remains unformalizable here (the genuinely open residual) is the `ω₁`-preserving
case itself:

This is the exact path a Turing-degree proof would need — but it requires the `ω₁^x`/admissible-ordinal
machinery and the AD pushforward-to-club theorem, none of which is formalized here (a multi-file
hyperarithmetic development).  The finite-jump decomposition above is the *elementary shadow* of this
transfinite picture: it reaches the finite-jump boundary (Case B) with only the countable σ-pigeonhole,
and stops exactly where the `ω₁`-Fodor step would take over.

**Why Lutz's hyperarithmetic theorem does NOT reduce the Turing case (a correction of a natural
confusion, and the real reason it's open).**  Lutz proves Martin's conjecture for *hyp-invariant*
functions on the **hyperarithmetic degrees** `D_h`.  A Turing-invariant `F` is generally **not**
hyp-invariant: `X ≡_h Y` (hyp-equivalent, weaker than `≡ᵀ`) does not give `X ≡ᵀ Y`, so Turing-invariance
does not force `F X ≡_h F Y`, and `F` induces no well-defined function on `D_h`.  So Lutz's theorem is
about a *different invariance notion* and simply does not apply to the Turing regressive core — that
invariance mismatch, not just the ordinal machinery, is why the Turing case is genuinely separate and open.

*Bounded cases are the easy ones, not the residual.*  Both Turing-bounded (`F X ≤ᵀ Z`,
`bounded_implies_constant`) **and** hyp-bounded (`F X ≤_h c`) force constancy: there are only *countably
many* hyperarithmetic-in-`c` reals, so hyp-bounded values are countable and `nonconstant_values_uncountable`
kills them.  So the difficulty is **not** boundedness.

*So the open content is the escaping/preserving cases.*  A genuine counterexample has values that are
*unbounded* — arithmetically escaping (`CaseBConstant` = arithmetic-*preserving* `F X ≡ₐ X`, values track
`X` and are unbounded) — while dropping the Turing degree.  The obstruction is a `≤ᵀ`-normality
(pressing-down) argument that works when the fiber is uncountable and the argument-tracking values escape
every countable bound; neither the countable σ-pigeonhole (needs a countable value-set) nor Lutz's `D_h`
Fodor (needs hyp-invariance) supplies it.  This is the exact gap.

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

*Concrete disproof-side target (scoped, not yet attempted — the only accessible "disproof"
result).* Formalize a **ZFC/AC counterexample** ⟹ "Part 1 is not a theorem of ZF+AC; determinacy
is necessary." Recipe: a representative-choice `rep : ℝ→ℝ` with `rep X ≡ᵀ X`, constant on degrees
(`Classical.choice` on the `≡ᵀ`-quotient); an injective `g` on degrees `≥ᵀ 0′` with `0 <ᵀ g(d) <ᵀ d`
(intermediate degrees exist — the project has `EffectiveKP`: `∅ <ᵀ A <ᵀ 0′` relativizes; injectivity
by AC since each `d` has continuum-many intermediates); then `F X = g(rep X)` is invariant, regressive,
nonconstant. The subtle part is *provable* nonconstancy (needs the injective choice, a cardinality
argument). ~50-100 lines; genuine but "known" (everyone knows AC breaks Part 1), and it does **not**
touch the AD-frontier — it only delineates the role of determinacy. Left as a documented future target.

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
The known proofs each *supply* a missing wall by hypothesis: uniform / order-preserving / measure-
preserving (the proven Borel *sub-classes*) give (1)+(2) (a code / structural effectiveness),
hyperarithmetic-regressive gives an ordinal-effective handle.  The general case (general Borel and
general Turing, both open) has none.  A crossing must manufacture one of the three for `F` — no
formalizable route does.

**How the walls tie together (a clean reformulation, and a correction of my own earlier notes).**
There are TWO distinct "uniformities", and conflating them is a trap:
- (A) `F X = Φ_e^X` on a cone (a *single functional*; = "`F` is **continuous on a cone**").  Only
  meaningful when `F X ≤ᵀ X` (regressive/below).
- (B) `UniformlyTuringInvariant` = the Slaman–Steel notion: `∃u`, `EquivVia X Y i j ⟹
  EquivVia (F X) (F Y) (u(i,j))` — reductions *between* `F X` and `F Y`, uniform in the witnesses.
  This is what `regressive_uniform` / `partI_uniform` actually consume.

(A) does **not** directly imply (B) for regressive `F`: to get `F X → F Y` you'd need `X` (to recompute
`Y`), but `F X <ᵀ X` means `F X` can't recover `X`.  The only bridge (A)→(B) is *through* Slaman–Steel's
"Borel ⟹ uniform on a cone" (a single functional is Borel).  So the whole open problem collapses to:

> **Part 1 for `F` ⟸ `F` is continuous (a single `Φ_e`) on a cone** ⟹ Borel-on-cone ⟹ (B) via S–S ⟹ Part 1.

and the barrier is precisely: **AD gives continuity on a *comeager* set, never on a *cone*** (wall 3 —
cones are meager & null, orthogonal to category/measure).  So walls (1)/(2) [no code / definable-not-
Turing] are *the same wall* as (3) [continuity lives on comeager, not cones], viewed through the
"continuous-on-a-cone" reformulation.  This is the single sharpest statement of the obstruction.

**Why AD's free measurability does NOT apply Slaman–Steel (a tempting shortcut, refuted).**  Under
AD every set of reals is Lebesgue-measurable, so *every* invariant `F` is measurable — one is tempted
to say "S–S proves Part 1 for measurable `F`, and AD makes everything measurable, QED."  This FAILS:
S–S needs `F` **Borel** (or ∞-Borel with a code), and *measurable = Borel modulo a null set*.  But
**Turing cones are null** (and meager).  So a measurable `F` may differ from its Borel approximant on
an *entire cone* — measurability is null-blind exactly where the cone measure lives.  AD hands you
regularity (measure, Baire, perfect-set) for free, but all of it is null/meager-modulo, hence
**invisible to the cone filter**.  This is the crispest form of wall 3, and the reason "AD ⟹ Part 1"
is not a two-line corollary.

**Capstone (dichotomy vs uniformization).**  Determinacy's *only* cone-native tool is the cone
**dichotomy** — `cone_theorem`: an invariant set contains a cone or its complement does.  Part 1
needs cone **uniformization** — an effective (Turing, on a cone) *selection* from an invariant
multifunction (e.g. `X ⇉ {codes e : Φ_e^X ≡ᵀ F X}`).  AD's *definable* uniformization (Moschovakis)
applies to *definable* relations; the relation here is `F`-defined hence non-definable, so it doesn't
apply.  And a general "cone uniformization" principle is *not* known to follow from AD — it is
essentially **as hard as Part 1 itself**.  So the whole 50-year gap = **the distance between cone
dichotomy (have) and cone uniformization (need)**.  Every attempt in this log is a failed attempt to
manufacture uniformization from dichotomy; none succeeds, and there is a principled reason none can
using only the tools determinacy is known to provide.

**No stronger determinacy axiom escapes this.**  One might hope AD_ℝ (or AD⁺) helps — AD_ℝ gives
uniformization for *all* relations on reals (Solovay), not just definable ones.  But that uniformizing
object is still a *choice/definable function*, never a *Turing functional* (a code `Φ_e`).  The
barrier is **definable-selection vs computable-selection**, and that is *orthogonal to the strength of
the determinacy axiom*: determinacy manufactures definability, never computability.  So the "just
assume more determinacy" escape is closed — the gap is not about how much selection you have, but
about selection being *effective*, which no determinacy hypothesis provides.

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

**NOW FORMALLY BRACKETED (2026-08-22, `Reduction.lean`, std axioms).** The gap is pinned by two
machine-checked theorems around it: `exists_uniform_index_on_cone` (HAVE — code on one *representative*
per degree, non-invariant selection) and `continuousOnCone_of_invariantIndex` (NEW — an *invariant*
index `idx` with `F X = Φ_{idx X}^X` yields **continuity on a cone**, `F X = Φ_e^X`, via σ-pigeonhole on
the invariant level sets `{idx=n}`). Capstone `regressiveCore_of_invariantIndex`: `RegressiveImpliesConstant
⟸ ContinuousRegressiveConstant` (KNOWN — a continuous `F` is a *recursive* function, and Slaman–Steel
proved Part 1 for recursive functions via rates-of-convergence; NOT via "Borel⟹uniform", which is open) `∧
HasInvariantGoodIndex` (the OPEN crux, = invariant good-index = cone uniformization). So of the two named
inputs, one is known mathematics and the other is exactly the barrier above — now a formal `Prop`, not
just prose. (Full Part I likewise ⟸ Steel's conjecture: `partI_general_of_steelBridge`, `MartinResults.lean`.)

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

**Triage of remaining targets (honest — most are KNOWN cleanup, not the open frontier):**

*Status of the natural (Borel/`Measurable`) class (CORRECTED 2026-08-22).* Part 1 for **general Borel**
functions is **OPEN**, not published cleanup — it is known only for the uniform (Slaman–Steel),
order-preserving, and measure-preserving (Lutz–Siskind) sub-classes. Currently proven here: `partI_uniform`
(uniform sub-class) and `partI_of_bounded`. `PartI_Borel` is NOT proven, and the bridge to it
(`Borel ⟹ uniform`) is itself open (≈ Steel's conjecture for Borel); `escaping ⟹ MP` is proven for NO
nontrivial class (only stated as the reduction hypothesis).
- **`Measurable/Borel invariant F ⟹ UniformlyTuringInvariant on a cone`** — the missing bridge; with
  it, `partI_uniform` upgrades to `partI_Borel` (the actual Slaman–Steel theorem). Substantial (a
  core S–S lemma), fully classical, but a well-defined bounded target.
- **Posner–Robinson (original finite-extension construction, not Kumabe–Slaman forcing)** — the input
  Slaman–Steel use for the *incomparable* core. Elementary-ish, formalizable, but only cracks the
  *uniform* incomparable core (already done); does NOT help the general frontier (still needs a code).
- **Steel's game for the uniform-on-reps fragment** — recursion theorem now available; hits the
  good-rep gap concretely.

*Genuine frontier (the OPEN problem).* Blocked by the THREE WALLS above; no formalizable route found.
A crossing needs a NEW idea to manufacture effectiveness / effective-selection / cone-regularity for
a non-definable invariant `F`. This is the ~50-year-open content; do not expect a Lean-tractable
proof without a mathematical breakthrough. The value delivered here is the *sharp machine-checked
counterexample profile* + the *precise localization of the barrier*, not a crossing.

**Capstones FORMALIZED (`MartinResults.lean`, std axioms).** `partI_general_of_uniformity`: full
(AD-general) Part I ⟸ the single implication "`TuringInvariant F ⟹ UniformlyTuringInvariant F`" —
everything downstream (`partI_uniform_general`, the trichotomy + the two Steel cores) is machine-checked.
`partI_Borel_of_uniformity_bridge`: same for the natural (`Measurable`) class — but the bridge is OPEN
for general Borel `F` (Part 1 for general Borel is open; only uniform/order-preserving/measure-preserving
sub-classes are known), so this isolates OPEN content, not a published theorem.
`escapingMP_of_uniformity_bridge`: the bridge subsumes the `escaping ⟹ MP` route (so it's the stronger
of the two open sufficient conditions).  **Honesty caveat:** the bridge is *sufficient, not necessary*
— Part I (constant-or-above-id) does not imply uniformity, so this is a natural strengthening (the Borel
route), not a reformulation; Part I could in principle hold even where the bridge fails.  It is the
cleanest *sufficient* condition, now a single named Lean hypothesis `bridge`.

**Probe: try to PROVE the bridge with the project's own σ-pigeonhole — dies at non-invariance (the
sharpest tool-level localization).**  Fix witnesses `(i,j)`.  For `X` with `EquivVia X (Φ_i^X) i j`,
the reduction `F X → F(Φ_i^X)` exists (`F X ≡ᵀ F(Φ_i^X)` by invariance); let `g(X) = least code p`
realizing it.  `g` has *countable* range (`p ∈ ℕ`).  IF `g` were degree-invariant, `bounded_implies_constant`
/ the σ-pigeonhole would force `g` **constant on a cone** — i.e. a single `p = u(i,j).1` works cone-wide
= the bridge!  It fails at exactly one point: `g(X)` is the least reduction between the *specific reals*
`F X` and `F(Φ_i^X)`, which depends on the reals, not their degrees, so `g` is **not degree-invariant**
(and there is no degree-invariant choice of a real-to-real reduction).  So the cone theorem / σ-pigeonhole
— the only cone-native tools — cannot stabilize it.  This is wall 2 (non-invariant selection) pinned to
the precise line where the formalized machinery breaks: *the bridge is one σ-pigeonhole away, blocked
solely by the non-invariance of the reduction-code function.*

---

## Session 2026-08-25 (7-hour autonomous run) — plan

State at start: Martin's Lemma 2.3 / MartinPPT now PROVED modulo determinacy (`martinPPT_of_gameDeterminacy`,
this session's predecessor). So Thm 3.4, Part 1 ⟺ escaping⟹MP, order-preserving Part 1 all rest on
determinacy + at most one named hypothesis. The barrier for the *general* open core (escaping⟹MP /
incomparable core) is unchanged and exhaustively documented above (cone dichotomy vs cone uniformization).

Two-track plan for the session:
- **Track A (concrete formalization, subagents):** discharge the remaining named "known" hypotheses.
  Highest value = `OrderPreservingUncountableCofinal` (the Groszek–Slaman–Kihara coding = order-preserving
  Part 1). Now that MartinPPT (pointed perfect trees) is a theorem, the coding may be reachable through it.
- **Track B (original research, main thread):** genuinely new angles on the open core; formalize new
  constraints / sub-cases / reductions; document all findings (even inconclusive). Running log below.

### Track B running log (2026-08-25)

Fresh angles tried on escaping⟹MP (the open core), all documented honestly:

**(B1) Iterated-cone / Fubini on pairs.** Analyze `F(X⊕Y)` for a `U×U`-generic pair via an iterated
cone argument (available: `U` is countably complete). Any Fubini-style contradiction needs
`F(X⊕Y) ≥ᵀ F X` (to "accumulate" values), which requires MONOTONICITY. A counterexample is not
order-preserving (`counterexample_not_orderPreserving`), so `F(X⊕Y)` is a *fresh* value unrelated to
`F X`. **Dies on non-monotonicity** — same wall as old Attempt A (exact pairs), now seen at the pair level.

**(B2) Kernel-growth by joining fixed reals.** From a non-MP `F` (kernel bounded by `W₀`), form
`φ = F ⊕ c` for fixed `c` to enlarge the kernel toward everything. `φ` is invariant and its kernel
gains `{Z ≤ᵀ c}`, but stays bounded: `F` escapes every fixed real (`escaping`), so `φ` escapes
`deg c` and remains non-MP. Taking an ω-join `⊕ₙ cₙ` is still a *single fixed real*, escaped by `F`.
**Dies on "escaping escapes every fixed bound"** — no fixed modification of `F` reaches MP. This is the
function-level shadow of "a single real has a fixed cone-below ideal, but `F`'s values escape it."

**(B3) RK-order is trivial on pushforwards — a crisp clarification (NEW, formalized).** In the cone
ultrapower, the Rudin–Keisler order on values `[F] = F_*U` is **trivial**: *every* `[F] ≤_RK [id]`
(witness `h = F`, since `map F U = map F (map id U)`). So `[id] = U` is RK-top among all pushforwards
and RK cannot distinguish them. This is the precise reason the "descend in RK: `[id] >_RK [F] >_RK …`"
idea (old pushforward-descent note) was doomed — **Part 1 is about the *Martin* (pointwise `≤ᵀ`-on-a-cone)
order, which is strictly finer than RK** (`[F] ≤_RK [G]` means `F ≡ h∘G` on a cone = "`F` factors through
`G`", orthogonal to `F X ≤ᵀ G X`). Formalized `pushCone_rkle_id` (`MeasurePreservingFilter.lean`).
Confirms: the pushforward/RK framework is a clean *reformulation* but the discriminating order is Martin,
which is exactly where the uniformity barrier lives (`[F] ≤_M [G]` + uniformity ⟹ `[F] ≤_RK [G]`).

Net: no crossing (none expected). One crisp new formalized clarification (B3) explaining why the
RK/pushforward-descent route cannot work. The barrier (dichotomy vs uniformization / Martin-order-not-RK)
stands.

**(B4) MartinPPT as a NEW cone-native tool — a tempting crossing, precisely refuted.** The attack log
above says "the dichotomy (`cone_theorem`) is determinacy's only cone-native tool." That is now OUT OF
DATE: **`MartinPPT` (cofinal ⟹ pointed perfect tree) is a strictly stronger cone-native tool**, proved
this session (`martinPPT_of_gameDeterminacy`). Does it cross the barrier? Tempting route:
- For a counterexample `F` (`F X ⊥ X` on a cone), `H X := X ⊕ F X` is **above the identity** (`X ≤ᵀ H X`),
  hence MP, hence `range(H)` is **cofinal**. So MartinPPT DOES apply to `range(H)`, giving a pointed
  perfect tree `T ⊆ range(H)` whose branches `y ≡ᵀ x ⊕ F x` realize a cone of degrees, and on which
  `F x = (second half of y)` is **computable from the branch `y`**. This looks like a uniformization of
  `F` (a pointed perfect set on which `F` is computed by projection!).
- **Refuted (sharpened reps→all-X gap).** The branch of degree `d` is `y = x ⊕ F x ≡ᵀ d`, but `deg(x)` is
  only `≤ᵀ d`, NOT `= d`: a branch can have a *low* `x` with a *high* `F x ≡ᵀ d`. So the "representative"
  `x` is not `≡ᵀ` the general degree-`d` real `X`, and `F(x) ≢ᵀ F(X)` (different degrees) — invariance
  does not transfer. To force `x ≡ᵀ d` one would need `F x ≤ᵀ x` (regressive), which is the very thing
  at issue (circular). So MartinPPT-on-`X⊕FX` reproduces the reps→all-X gap in an even sharper form (the
  reps can be low). **No crossing.**

Insight (updates the "only tool" statement): MartinPPT *is* a new, stronger cone-native tool, but it
grips only *cofinal* sets, and a counterexample's own range is precisely NOT cofinal (non-MP, kernel
bounded); the only cofinal set canonically built from `F` is `X⊕FX`, which is above-id and washes out
`F`'s incomparability (the join computes any `Z` the argument does). So the barrier survives the strongest
cone-native tool now available; the obstruction is confirmed to be the reps→all-X (uniform-good-rep)
gap, not a missing regularity principle.

### Status RESOLVED + regressive proof strategy (2026-08-25, literature check)

Web-confirmed (Lutz thesis "Results on Martin's Conjecture"; Marks–Slaman–Steel): **Slaman–Steel DID
prove Part 1 for all regressive functions on the *Turing* degrees** — a regressive Turing-invariant `f`
is constant-on-a-cone or above-id-on-a-cone. So the attack log's MAJOR CORRECTION stands:
`RegressiveSlamanSteel` is a KNOWN theorem (a real formalization target), and the **incomparable core is
the SOLE open Part-1 content**. Lutz's `D_h` result is the separate hyperarithmetic question.

**The S-S regressive proof strategy** (now a formalization target — pieces partly available):
1. Determinacy ⟹ a **pointed perfect tree** on which `f` is **computable and injective** (a coordinated
   tree + uniformization — STRONGER than plain `MartinPPT`, which gives a tree in a cofinal set not
   coordinated with `f`'s code; this coupling is the crux and is exactly why the *incomparable* core has
   no analogue: `f x ≰ᵀ x` gives no code to uniformize).
2. **Domination:** for `x` on the tree, every function `≤ᵀ x` is dominated by a function `≤ᵀ f x` — else
   `x` diagonalizes against `f x`.
3. **Coding:** code the bits of `x` into the relative growth rates of two fast-growing `f(x)`-computable
   functions ⟹ `f x ≥ᵀ x` on the tree. With `f x ≤ᵀ x` (regressive) ⟹ `f x ≡ᵀ x` ⟹ `f ≡ id` on the
   tree's cone (nonconstant case); constant otherwise.
The barrier for the incomparable core is precisely that step 1 fails there (no code from `f x ≤ᵀ x`).
Launching a subagent to attempt this (high value: discharges the regressive core).

### Frontier confirmed + new leads (2026-08-25, literature)

Confirmed current status (Lutz–Siskind JAMS 2025; Slaman–Steel; Marks–Slaman–Steel; Nakid-Cordero 2025):
- KNOWN: uniform (Slaman–Steel), regressive-Turing (Slaman–Steel), order-preserving & measure-preserving
  (Lutz–Siskind). Bard: uniform Part 1 ⟸ a LOCAL phenomenon (nonconstant invariant `x→y` ⟹ `x ≤ᵀ y`).
- OPEN: the **incomparable core** — functions "off to the side of the constants" (incomparable to the
  nonzero constants in the Martin order). No known technique.
- Cautionary analogue: in the ENUMERATION degrees there IS a definable function not equivalent to a
  uniformly-invariant one (Nakid-Cordero) — i.e. the definable≠uniform gap is *realized* there. That it
  does NOT transfer to the Turing degrees (Turing Part 1 believed true) is a Turing-specific phenomenon;
  understanding the non-transfer is a possible research handle (not pursued — requires the e-degree
  construction).

**New lead — the jump-bounded incomparable sub-case (`F X ≤ᵀ X'`).** A genuinely new potential sub-class:
if `F X ≤ᵀ X'` on a cone (values arithmetic-in-the-argument) AND `F X ⊥ X`, then `F X = Φ_{e(X)}^{X'}`
gives a CODE from the jump — so Slaman–Steel step 1 (coordinated tree + uniform code) has an analogue
*relative to the jump*, and the S-S domination/coding argument may run relativized, forcing `F X ≥ᵀ X`
(contra ⊥). This would be a new sub-case of the incomparable core (everything with jump-bounded values),
downstream of the regressive-theorem formalization (subagent C) via relativization to `'`. The general
incomparable core is exactly where NO such code exists (`F X ≰ᵀ X` and `F X ≰ᵀ X'` possible) — the
irreducible barrier. Noted as a follow-up once the regressive machinery lands.

**PR does not help the general incomparable core (re-confirmed).** Even with Posner–Robinson formalized
(subagent B) and pointed perfect trees available (MartinPPT), reviving Attempt C fails for the *general*
case: PR needs `F` as an oracle (wall 1), and the general incomparable `F` yields no code to feed it. PR's
value is as a library building block / the uniform case, not a frontier crossing.

### Subagent A result (order-preserving coding) — 2026-08-25

Attempted `OrderPreservingUncountableCofinal` via MartinPPT. Outcome (honest): NOT dischargeable from
determinacy — it is equivalent to `AvoidingImpliesConstant` = the Groszek–Slaman value-side perfect-set
coding (Lutz–Siskind Thm 4.3), a genuinely-open/substantial forcing lemma. Concrete witness that
OP+uncountable is INSUFFICIENT: the ideal of hyperarithmetic degrees is uncountable, downward-closed and
directed, yet not cofinal (misses Kleene's O). The MartinPPT/InvertingTree machinery is for the OPPOSITE
direction (MP ⟹ above-id; uniformizes an already-increasing F), so does not supply the value-side coding.
Captured on main as `OrderPreservingCore.uncountableCofinal_iff_avoiding` (the two OP hypotheses are one).
Net: the order-preserving case rests on exactly one open coding lemma; no crossing.

### Incomparable-core four-way decomposition — synthesis (2026-08-25)

The incomparable core is ALREADY decomposed four ways (`RegressiveJumpDecomp.incomparableCore_of_cases`,
applying both jump-distance dichotomies): by the arithmetic position of `F X` vs `X`, into
`(An/Bn)×(Am/Bm)` where `Bm`: `F X ≤ᵀ X^(k)` (F X arithmetic-in X), `Am`: `F X ≰ᵀ X^(n)` ∀n (F X
arithmetic-escapes X), dually for `An/Bn`. Assessed whether the now-confirmed-KNOWN *Turing* regressive
theorem (`RegressiveSlamanSteel`) discharges any case: **it does NOT.** The `Bm` cases (`F X ≤ᵀ X^(k)`)
are *arithmetic*-regressive, not Turing-regressive — they would need the **arithmetic-degrees** regressive
theorem (`F X ≤ₐ X ⟹ const or ≡ₐ id`), whose status is uncertain (Lutz did the *hyperarithmetic*
degrees; the arithmetic case is intermediate and not obviously in hand). The `Am/An` cases
(arithmetic-escaping) are the transfinite residual. And the naive "regressive-ification"
`G X = if F X ≤ᵀ X then F X else X` (regressive, invariant) collapses to `id` on the incomparable cone,
so `RegressiveSlamanSteel` gives no information about an incomparable `F`. Net: the four sub-cases are all
genuinely open; the known Turing regressive theorem does not crack any. The natural next reduction would
be an **arithmetic-degrees regressive theorem** (would kill the two `Bm` cases), leaving the
arithmetic-escaping cases — mirroring how the finite/transfinite split works for the regressive core.

**Precise localization at the level of the S-S proof (2026-08-25).** WHY the Slaman–Steel regressive
argument does not transfer to the incomparable core, pinned to a single step: the argument's **domination**
step ("every function `≤ᵀ x` is dominated by one `≤ᵀ f x`, else `x` diagonalizes against `f x`") requires
`x` to COMPUTE `f x` (to diagonalize against `f x = Φ_e^x`). For regressive `f` this holds (`f x ≤ᵀ x`);
for INCOMPARABLE `f`, `x ≰ᵀ f x`, so `x` cannot access `f x` to diagonalize — the domination step has no
purchase. So the incomparable core is not just "no code" (barrier wall 1) but specifically
"no domination handle": even granting a code for `f` on a tree, the growth-rate coding argument cannot
start because the argument needs the argument to dominate the value, and incomparability forbids exactly
that. This is the crispest proof-level statement of why the sole open core resists the one method that
settles the regressive case.

---

## Night synthesis (2026-08-25, 7-hour autonomous run)

**Concrete formalization delivered (all std axioms, machine-checked):**
- `MeasurePreservingFilter.lean`: functorial characterizations (MP/escaping/above-id/constant as
  Martin-measure-pushforward statements; Part 1 in ultrafilter language) + `RKle` with
  `pushCone_rkle_id` (RK order on pushforwards is trivial ⟹ RK-descent can't prove Part 1).
- `GraphFunction.lean`: the graph `X ↦ X ⊕ F X` (= `id ⊔ F`), why MartinPPT can't grip a counterexample,
  and the Martin order as an upper semilattice (`martinJoin_le`).
- `OrderPreservingCore.lean`: `uncountableCofinal_iff_avoiding` — the OP branch rests on exactly ONE open
  coding lemma (the two named OP hypotheses are equivalent).
- `PosnerRobinson.lean` (subagent): relativized PR (`A ⊕ G ≡ᵀ G'` on the cone above `0'`, via Friedberg).
- `RegressiveSkeleton.lean` (subagent): the KNOWN Slaman–Steel regressive theorem opened into its 3 steps
  (coordinated tree / branch domination / branch coding), assembly proved, discharging the regressive core
  outright given the 3 steps.

**Original-research findings on the OPEN incomparable core (no crossing — expected; barrier is deep):**
1. Every fresh angle (Fubini/iterated-cone B1, kernel-growth B2, RK-descent B3, MartinPPT-on-graph B4)
   funnels to the same barrier: a counterexample's range is not cofinal, its canonical cofinal-ification
   (the graph) is above-id and washes out incomparability, and no cone-native tool (not even the newly
   proved MartinPPT) extracts a Turing code from a non-definable invariant `F`.
2. **Sharpest proof-level localization (new):** the Slaman–Steel regressive method's *domination* step
   needs `x ≥ᵀ f x` (so `x` can diagonalize against `f x = Φ_e^x`); the incomparable core is exactly where
   `x ≱ᵀ f x`, so the one method that settles the regressive case has no purchase. The incomparable core
   is decomposed four ways by arithmetic position (`incomparableCore_of_cases`); the "Bm" (arithmetic-
   regressive) cases would need an *arithmetic-degrees* regressive theorem (reduces Bm→BnBm, not closed),
   the arithmetic-escaping cases are the transfinite residual.
3. Literature-confirmed: order-preserving/measure-preserving (Lutz–Siskind 2025) and regressive
   (Slaman–Steel) are KNOWN; the incomparable core ("functions off to the side of the constants") is the
   sole open Part-1 content, with no known technique; the crossing appears to need inner model theory
   (Siskind). Consistent with the machine-checked barrier here.

**Net:** the known Part-1 content is now fully structured/discharged-modulo-named-lemmas; the open core is
precisely mapped and shown robust against the strongest available tools. No disproof/crossing (none
expected under determinacy).

**(B5) Continuity-on-a-perfect-set via AD's Baire property — fresh angle, refuted by wall 3.** Under AD
every invariant `F` has the Baire property, hence is **continuous on a comeager set** `G`, which contains
a **perfect set** `P` on which `F` is continuous — and a continuous `F` on a perfect set has a code
(uniformization!). This LOOKS like a route to a code. **Refuted:** the comeager `G` (and its perfect
subset `P`) is *orthogonal to cones* — cones are meager, so `P` lives in the meager-complement region and
does NOT realize a cone; dually, a MartinPPT pointed perfect tree `T` (cone-realizing, hence meager) is
where AD's continuity says nothing, so `F` may be wildly discontinuous on `T`. There is no perfect set
that is both cone-realizing and Baire-continuous-for-`F`. This is wall 3 at the perfect-set level, and the
crispest refutation of the natural "AD gives continuity ⟹ a code" hope: AD's continuity and Martin's cones
occupy orthogonal (meager-vs-comeager) parts of `2^ω`. Confirms the barrier once more.

### Structural reduction of the open core (2026-08-25, `IncomparableArithReduction.lean`)

The four-way jump-distance decomposition of the incomparable core (`incomparableCore_of_cases`) is
refined: the **`AnBm` sub-case** (`F X <ₐ X` — arithmetically strictly below the identity, Turing-
incomparable) falls to `StrictArithRegressiveConstant`, the arithmetic-degrees analogue of the
Slaman–Steel regressive theorem (a strictly weaker input than the open core; Lutz proved the
*hyperarithmetic* case, the arithmetic case is intermediate/open). `incomparableCore_of_three_cases_and_arith`:
the open core ⟸ three sub-cases (AnAm/BnAm/BnBm) + this arithmetic lemma. So the open core is not four
independent problems but three plus one arithmetic-regressive theorem — the natural next target
(mirrors how the finite/transfinite split organizes the regressive core). The dual `BnAm` (`X <ₐ F X`)
would need an arithmetic *above-id* theorem; `BnBm` (`F X ≡ₐ X`) and `AnAm` (arithmetically incomparable)
are the genuinely transfinite residue.

### Sharpest structured reduction of Part 1 (2026-08-25, `IncomparableArithReduction.partI_of_three_cases_and_arith`)

The whole of Part 1 is now reduced to: `RegressiveSlamanSteel` (KNOWN) + `StrictArithRegressiveConstant`
(the arithmetic-degrees regressive theorem) + three jump-distance sub-cases (AnAm/BnAm/BnBm). Honest
assessment of this decomposition:
- **AnBm ↔ arithmetic-regressive theorem (a genuine classification, not a magic reduction).** The `AnBm`
  sub-case (`F X <ₐ X`, Turing-incomparable) is exactly the open content of the arithmetic-degrees
  regressive theorem. This is valuable *framing* — it identifies an ad-hoc sub-case with a recognizable
  target (the natural intermediate between Slaman–Steel/Turing and Lutz/hyperarithmetic), attackable by
  the same coordinated-tree + domination + coding method — but its difficulty equals AnBm's, not less.
- **It does NOT collapse to the known Turing theorem.** Induction on the arithmetic level fails: `F X ≤ᵀ
  X^(k+1) = (X')^(k)` would need `F` to be *jump*-invariant to apply level `k` relative to `X'`, but a
  Turing-invariant `F` is not jump-invariant (the jump is not degree-injective downward). So the
  arithmetic case is genuinely separate from the Turing one — as expected (it's why Lutz's hyperarithmetic
  result and Slaman–Steel's Turing result are distinct theorems, with the arithmetic level in between).
- The other three sub-cases resist even reframing: `BnAm` (arithmetic-above) has no strictly-weaker
  named target; `BnBm` (arithmetic-equivalent, Turing-incomparable) is the arith-preserving Turing-dropping
  phenomenon; `AnAm` (arithmetically incomparable) hits the ω₁-engine's cone-preservation caveat.
Net: a genuine finer *classification* of the sole open Part-1 content into four arithmetically-typed
pieces, one identified with a recognized open theorem — the sharpest structural map to date, honestly not
a crossing.

---

## Session 2026-08-25 (option-3 continuation, work-until-2pm) — plan

User directive: keep probing the open incomparable core with fresh ideas + write up the arithmetic
decomposition. Rigorous writeup done: `MARTIN_PART1_OPEN_CONTENT.md`. Now: fresh probing of the three
residue sub-cases (BnBm arith-preserving, BnAm arith-above, AnAm arith-incomparable) and the
arithmetic-regressive theorem (AnBm), formalizing any clean structural results, documenting all attempts.
Running probe log below.

### Probe log (option-3 continuation)

**(B7) Why the ω₁-engine's cone-preservation caveat is ESSENTIAL for the incomparable core (AnAm).**
The engine `no_omega1_decreasing_conePreserving` would kill the ω₁-decreasing part of AnAm (`ω₁^{F X} <
ω₁^X` on a cone) — but only for CONE-PRESERVING `F` (`base ≤ᵀ F X`). Can one manufacture cone-preservation?
- **Fixed base `G := F ⊕ base` floors the descent.** `G X = F X ⊕ base ≥ᵀ base` is cone-preserving, and
  `ω₁^{G X} = max(ω₁^{F X}, ω₁^{base})`. But then the ω₁-descent of the iterates `G, G², …` is BOUNDED
  BELOW by `ω₁^{base}` (a fixed countable ordinal): once `ω₁^{F(·)}` drops below `ω₁^{base}`, the join
  floors `ω₁^{G(·)}` at `ω₁^{base}` and the descent stalls. No *infinite* descent ⟹ no contradiction. So
  any fixed base introduces a floor and defeats the engine — this is precisely the attack log's
  "`G := F ⊕ base` fails," now explained ordinally.
- **A varying, unbounded base `≤ᵀ F X` would avoid the floor — but none exists.** For a counterexample
  `F` the kernel `{Z : Z ≤ᵀ F X on a cone}` is BOUNDED (`nonMP_kernel_avoids_cone`, formalized: non-MP ⟹
  proper kernel), so there is no unbounded family of degrees below `F X` to serve as a growing base.
So cone-preservation is genuinely UN-manufacturable for an incomparable `F`: a fixed base floors the
ω₁-descent, and incomparability (bounded kernel) forbids an unbounded base. This is the precise, structural
reason the ordinal-ultrapower engine — which handles the regressive-cone-preserving case cleanly — cannot
reach the incomparable core. (Ties `nonMP_kernel_avoids_cone` to the cone-preservation caveat: they are
the same obstruction viewed measure-theoretically vs ordinally.)

**(B8) BnBm sub-case ⟹ F preserves the ω-jump (a clean necessary condition).** If `F X ≡ₐ X` (BnBm:
arithmetically equivalent, Turing-incomparable), then `(F X)^(ω) ≡ᵀ X^(ω)`: from `F X ≤ᵀ X^(k)` we get
`(F X)^(n) ≤ᵀ X^(k+n)` so `(F X)^(ω) ≤ᵀ X^(ω)`, and dually. So on the BnBm cone `F` is the IDENTITY on the
ω-jump degrees (`X^(ω) ↦ (F X)^(ω) = X^(ω)`) while being Turing-incomparable to the identity BELOW the
ω-jump. Reframing: BnBm asserts an invariant `F` that is ω-jump-trivial yet Turing-nontrivial — a
"rigidity relative to the ω-jump" question. This is genuinely Turing-specific and sits below the
hyperarithmetic level Lutz reaches (it does NOT preserve `ω₁^x`, since finite jumps strictly increase
`ω₁^x`, so `X ≡ₐ F X` gives no `ω₁^x` control — confirming BnBm is invisible to the ω₁-engine, cf. B7).
No crossing, but a clean characterization of the hardest residue sub-case.

**Honesty correction (option-3 session).** The framing of `StrictArithRegressiveConstant` as "the
arithmetic-degrees regressive theorem" conflated two invariance notions. It is a *Turing*-invariant
statement (= the AnBm sub-case, `F X <ₐ X` for Turing-invariant `F`), which is *analogous to* but NOT
literally the `≡ₐ`-invariant arithmetic Martin conjecture on `D_a` — Turing-invariance does not imply
`≡ₐ`-invariance. So AnBm ↔ StrictArithRegressiveConstant is a *rephrasing in arithmetic-reducibility
terms* (suggesting the Slaman–Steel method relative to finite jumps), not an identification with a
recognized theorem. Corrected in `MARTIN_PART1_OPEN_CONTENT.md` §3-4 and the Lean docstring.

**(B9) The enumeration-degree contrast (a research direction, not a result).** Nakid-Cordero (2025)
proved that in the ENUMERATION degrees there IS a definable function not equivalent to a uniformly-
invariant one — i.e. the definable-vs-uniform gap (the exact obstruction of the Turing incomparable core)
is REALIZED there. So the e-degrees *allow* what the Turing incomparable core forbids (Turing Part 1
believed true). The genuine question: *why does the e-degree construction not transfer to the Turing
degrees?* The e-degrees are coarser (enumeration reducibility, `Σ⁰₂`-flavored) with a different global
structure; understanding precisely which Turing-degree feature blocks the analogous non-uniform definable
construction would be a concrete, positive handle on why the incomparable core should hold — a genuine
line distinct from the (barriered) determinacy-tool attacks. Not pursued here (needs the e-degree
construction details), but flagged as the most promising *positive* direction: contrast a structure where
the phenomenon occurs against the Turing degrees where it (conjecturally) cannot.

**(B10) BnBm as a fiber-rigidity question (the sole native face, documented probe — inconclusive).**
After the four-face map, the single sub-case native to neither known Martin regime is **BnBm**
(`F X ≡ₐ X`, `F X ⊥ᵀ X`): the Am region (BnAm∪AnAm) produces a transfinite-rank Part-2 object via the
graph (`am_graph_not_finite_jump`), and AnBm is the arithmetic regressive theorem. So the genuinely
Turing-specific heart is exactly BnBm. Precise restatement: **`F` is a Turing-invariant lift of the
identity on the arithmetic degrees** — it maps each `≡ₐ`-class into *itself* (`F X ≡ₐ X`) and permutes the
Turing degrees inside each class, moving every degree to a Turing-*incomparable* one (`F X ⊥ᵀ X`). BnBm ⟹
const is thus: *the fiber `{d : d ≡ₐ c}` (the Turing degrees in a fixed arithmetic degree), as a poset
under `≤ᵀ`, admits no nontrivial invariant self-map that displaces everything incomparably.* Probes that
FAIL to give an elementary handle: (i) **orbit/iteration** — `X, FX, F²X, …` all `≡ₐ`, but `F` is not
cone-preserving (`FX` need not be above the base), so the orbit escapes the cone and `F²X ⊥ᵀ FX` is not
available; (ii) **fiber rigidity** — `D_T` has no nontrivial *automorphisms* (Slaman–Woodin), but `F` is
not an automorphism (not order-preserving, not bijective) and the fiber is not the full degrees, so the
rigidity does not transfer; (iii) **relative cone measure** — cones are `≡ₐ`-heterogeneous (a cone meets
many arithmetic classes), so the Martin measure does not restrict to a single fiber. This is the CBER/MSS
locus (Marks, arXiv:1109.1875): a Borel-flavoured invariant selector within `≡ₐ`, blocked by non-smoothness
of `≡ᵀ`. No crossing; BnBm is genuinely the inner-model-theoretic residue. Value: a clean, self-contained
statement of the *one* remaining native piece.

**(B9+) The e-degree contrast, made concrete via the SKIP operator (2026-08-25, WebSearch).**
Nakid-Cordero (arXiv:2510.19147, Oct 2025) classify uniformly-invariant functions on the *enumeration*
degrees: they are "constant, increasing, or **above the skip operator**", AND there is a definable
e-function equivalent to a uniformly-invariant one on NO cone. The "wider spectrum" (a genuinely new
behavior class absent from the Turing degrees) hinges on the **skip** — the e-degree analogue of the jump —
which, unlike the Turing jump, is **not increasing**: on the Turing side `X ≤ᵀ X'` always (indeed
`X <ᵀ X'`), whereas the e-degree skip can drop below its argument ("above the skip" is a genuinely new,
regressive-flavoured behavior). This is a *concrete* handle on B9's question "why doesn't the phenomenon
transfer to Turing?": my formalized Part-2 leak `am_graph_not_finite_jump` — showing the whole `Am` region
produces a transfinite-rank Part-2 object — is proved from `self_le_jumpIter` (`A ≤ᵀ jump^[k] A`, the
**≤** direction = the jump is *increasing*). That exact property is what the e-degree skip lacks. So the Turing incomparable core's conjectural rigidity, and
specifically the Am-region-leaks-to-Part-2 mechanism, rest on the strict-increase of the jump; the
enumeration degrees, whose skip is not increasing, are precisely where the analogous rigidity
fails and non-uniform definable functions appear. (Honest scope: the paper's abstract gives the "above the
skip" classification and the wider spectrum; the identification of *jump-increase* (`A ≤ᵀ jump A`) as the
pivotal Turing-only property is my reading, grounded in that my own leak proof consumes exactly that
property. Not a crossing — a sharpened articulation of the positive direction: a Turing-side proof of the
`Am` region must exploit that the jump is increasing, in a way that has no e-degree analogue.)

**(B10-followup) BnBm is NOT structurally exotic — it reduces to the same skeleton as AnBm (verified).**
B10 framed BnBm as "the sole face native to neither regime / a fiber-rigidity question". `BnBmSkeleton.lean`
(machine-checked, `bnBm_of_cores`) REFINES this: BnBm reduces to the *same* relativized Slaman–Steel
coordinated-tree skeleton as AnBm. The AnBm assembly consumes its branch data through one channel only
(`arith_strict_branch` : `X ≰ₐ F X ⟹ ¬ x ≤ᵀ F x`), and BnBm's *incomparability* supplies `¬ x ≤ᵀ F x`
directly (branches on the incomparability cone). So step-3's `x ≤ᵀ F x` contradicts the branch-field
identically. The whole Bm region (AnBm∪BnBm) is thus uniformly "relativized-S-S step 1". The genuine
CBER/MSS difficulty of B10 is not gone — it is exactly the content of the *step-1 bracket*
`HasBnBmUniformTree` (a tree computing an arith-*preserving* injective `F` from `x^(k)`, branches on the
incomp cone), a distinct and plausibly harder bracket than AnBm's. So the honest statement is: BnBm needs
the *same method* (coordinated tree) with a *harder step-1 instance*, not a wholly new idea. The fiber-
rigidity/CBER framing of B10 is precisely what that step-1 bracket encapsulates.

**(B12) A unification conjecture: the coordinated-tree method at TRANSFINITE level (Am region).**
The `Bm` region reduces to a coordinated tree computing `F x = Φ_e^{x^(k)}` from a *finite* jump `x^(k)`
(machine-checked: `arithBelowHalf_of_all_tree_cores`). The `Am` region (`F X ≰ₐ X`) is *not* finite-jump
amenable — but the graph `X ⊕ F X` is a transfinite-rank Part-2 object. **Conjecture:** the whole
incomparable core reduces to a coordinated tree computing `F` from `x^(level)`, where `level` is *finite*
`k` on the `Bm` region and a *transfinite ordinal* `α` on the `Am` region; the primary `Bm`/`Am` divide is
then exactly *finite vs transfinite level*. Grounding: if Part 2 assigns the graph a fixed transfinite rank
`α` on a cone (`X ⊕ F X ≡ᵀ X^(α)`), then `F X ≤ᵀ X^(α)`, so a coordinated tree computing `F` from `x^(α)`
could run, with step-3's `x ≤ᵀ F x` again contradicting incomparability — the *same* assembly as `Bm`,
one level up. Two sub-regimes: (a) `α < ω₁^X` (graph is hyperarithmetic-in-`X`) — this is **Lutz's
territory** (he proved the regressive case on the hyperarithmetic degrees via "reduce to a continuous
function"); (b) `α ≥ ω₁^X` — genuinely beyond hyperarithmetic, the deepest residue. So the incomparable
core would be ONE method (coordinated tree from `x^(level)`) across all four faces, stratified by the
ordinal `level`: finite (`Bm`, relativized Slaman–Steel), `< ω₁^X` (Lutz), `≥ ω₁^X` (open). **Honest scope:
speculative.** It needs (i) Part-2 uniformity for the graph (open) to pin `α`, and (ii) the transfinite-jump
coordinated-tree construction (open, and the `ω₁`-level is exactly the project's blocked ordinal-ultrapower
engine). Not formalized. But it is a concrete, testable articulation of how the two known Martin-conjecture
methods (Slaman–Steel finite, Lutz hyperarithmetic) might be two levels of a single coordinated-tree
method — with the incomparable core the instance where the branch-field is Turing-incomparability.

**(B12-correction, later 2026-08-25)** B12 conjectured the coordinated-tree method as "one method
stratified by ordinal level (finite=S-S, <ω₁=Lutz, ≥ω₁=open)". **This is undermined by a later finding**
(`MARTIN_PART1_STRUCTURAL_AM.md` §2.6): the coordinated-tree method is **circular for the incomparable
core** at EVERY level — its domination bracket, combined with coding, yields `x ≤ᵀ F x`, which contradicts
`F x ⊥ᵀ X`; so proving domination ≡ proving the core, not an easier sub-problem. The uniform half of
domination is outright impossible (`incomparable_jump_not_below`). Slaman–Steel is inherently a
regressive-case tool (its engine derives `x ≤ᵀ F x`, consistent for regressive → "≡id", fatal for
incomparable). So B12's "coordinated tree at each level" does NOT reduce the incomparable core; the viable
route is measure-theoretic (`escaping ⟹ MP`, Groszek–Slaman engine, which does NOT derive `x ≤ᵀ F x`).
The whole earlier "four-face map / BnBmSkeleton reduces the core to coordinated trees" framing is corrected
by this: those are valid implications with circular (core-equivalent) hypotheses. Net honest state: the
incomparable core is a **value-distribution / ultrafilter** problem (`U`-preservation by invariant
pushforwards), NOT a coordinated-tree problem.

---

## SESSION 2026-08-26 — the DISPROOF direction, seriously investigated (could Part 1 be FALSE under ZF+AD?)

**Bottom line: construction and proof share the IDENTICAL wall, and that wall is now stated precisely with
literature receipts. The disproof direction is not "off the table" for a soft reason (AC counterexamples
vanish) — it is off the table for a SHARP reason: every AD-available construction tool for a sideways
invariant F, when made degree-invariant, is exactly `V ≤_RK U_M, V ≠ U_M` — the thing Part 1 asserts is
impossible. So a construction would BE a disproof of Part 1, and vice versa; there is no asymmetry.**

### The decisive comparative datum: the ZFC counterexample (Lutz thesis, Thm 5.27)
In **ZFC** there IS a measure-preserving Turing-invariant `F` with `F(x) ≱ᵀ x` for all uncomputable `x`
(so Part 1 is FALSE in ZFC on a cone; only the cofinal ZFC form survives, Slaman–Steel Thm 5.11). The
construction: wellorder `D_T` in order type `2^{ℵ₀}`; write `D_T = ⋃_α I_α` as a strictly increasing
tower of Turing ideals; set `F(x)` = a minimal upper bound (Spector exact pair) for `I_x = {y <ᵀ x : y`
enters a strictly earlier ideal than `x}`, chosen NOT to compute `x` (Lemma 5.26). This is genuinely
"sideways": `F(x)` computes everything below `x` that appeared "before" `x`, but not `x` itself.
**This is the honest disproof template.** It uses THREE ingredients, and pinpointing which one AD kills
is the whole question:
  1. a **wellorder of `D_T`** (to index the ideal tower and pick "least α with x ∈ I_α");
  2. a **per-degree choice** of a minimal-upper-bound / exact pair that avoids computing `x`;
  3. Spector exact pairs (this one is AD-safe — pure computability).
Ingredients (1) and (2) are `ω₁ ↪ ℝ` / `AC`-flavored: a wellorder of the degrees is exactly a
choice-of-representative per ordinal, and AD proves **no** wellorder of ℝ (hence of `D_T`) exists. So the
ZFC counterexample is destroyed at ingredients (1)+(2), which are the SAME object the proof-direction
memory identified as blocked: "an invariant ordinal/degree selection = `ω₁ ↪ ℝ`, AD-forbidden."

### Enumeration-degrees: the phenomenon IS realizable next door — isolates the missing Turing ingredient
Nakid-Cordero (arXiv:2510.19147) DISPROVES Martin's conjecture in the **enumeration** degrees under the
same set-theoretic strength: there is a Borel e-invariant `h` (Example 3.1) that is nonconstant, not
increasing, and incomparable to both jump and skip on every cone — a genuine invariant SIDEWAYS function.
It exists because `D_e` has (a) **no cone theorem** — Thm 3.2 (w/ Jacobsen-Grocott) partitions `D_e` into
continuum-many *disjoint cofinal* classes (impossible for `D_T`: countably many cones meet in a cone, and
any invariant set or its complement contains a cone), and (b) **𝒦-pairs** (a complementation/pairing
combinatorics with no Turing analog). **This is the cleanest possible evidence that the intuition "sideways
info has no invariant source" is NOT a logical truth — it is a special property of `D_T` conferred exactly
by Martin's cone theorem + the absence of cofinal partitions.** Turing resists the construction *because it
has the cone theorem*; the cone theorem is also the ONLY tool the proof direction has. Same object, both
directions.

### Tool-by-tool audit of AD-available sideways constructions (all fail at the SAME point)
- **(a) Uniformization_ℝ on `R(X,Y) = "Y ⊥ᵀ X"`** (nonempty ∀X). Uniformization_ℝ gives a *function*
  `X ↦ Y_X` with `Y_X ⊥ᵀ X`, but it is uniformization of a relation on REALS, not on degrees; the
  selector is **not degree-invariant** (`X ≡ᵀ X' ⇏ Y_X ≡ᵀ Y_{X'}`). Making it invariant = uniformizing
  the induced relation on `D_T` = choosing one degree per degree-class coherently = exactly a section of
  `D_T`, i.e. `ω₁ ↪ ℝ`. **Invariant uniformization is precisely what AD does NOT give** (Uniformization_ℝ
  uniformizes definable subsets of `ℝ × ℝ`; the `≡ᵀ`-invariant quotient relation is not thereby
  uniformized invariantly — this is the `definable ≠ invariant` barrier, already in memory).
- **(b) Wadge/scale selectors.** A scale gives a definable-uniformizing selector, same defect as (a):
  definable ≠ `≡ᵀ`-invariant. No scale respects Turing equivalence classes as points.
- **(c) Posner–Robinson complements.** For `X ≥ᵀ 0'`, P-R gives `G ⊥ᵀ X` with `X ⊕ G ≡ᵀ X'` (indeed
  `G' ≡ᵀ G ⊕ X ≡ᵀ X'`). The map `X ↦ [G]` would be a sideways invariant function IF an invariant choice
  of the P-R generic `G` existed on a cone. **No such invariant choice is known, and the obstruction is
  identical:** P-R `G` is built by forcing/below-`X'` genericity — a *per-real* construction; the P-R set
  for `X` is a nonempty relation `P(X,G)`, and an invariant selector is again a section of `≡ᵀ`. Lutz's
  Prop 3.14 (thesis) shows the closely-related "canonical oracle" selection fails already for `y ↦ (x⊕y)'`
  on a single degree (1-generic diagonalization) — the same non-canonicity that blocks a local Part 2.
  **No published invariant/OD Posner–Robinson complement exists** (searched; the P-R literature is entirely
  per-real: Shore–Slaman generalization, Woodin's hyperjump P-R, Solecki-dichotomy≈P-R — none produce a
  degree-invariant complement). This is a clean, correctly-scoped negative.
- **(d) Martin-measure ultrapower.** `[F] ∈ Ult(D_T, U_M)` is a genuine "new" degree, and `[F] ⊥ [id]`
  is expressible. But extracting a *real* representative of `[F]` (to get an actual invariant `F`) is a
  choice of a function `D_T → D_T` — you must already HAVE the sideways `F` to name `[F]`. The ultrapower
  reformulates, it does not construct: "is there a nonstandard `[F]` that is `U_M`-sideways" = "is there a
  counterexample" verbatim (= `F_*U_M ≤_RK U_M`, `≠ U_M`).

### The precise shared wall (statement)
Both directions reduce to the SAME degree-level object, which AD neither supplies nor refutes by its
cone-native tools:
> **WALL.** There is no `ZF+AD(+Unif_ℝ)`-definable way to select, `≡ᵀ`-invariantly and on a cone, one
> degree "off to the side" of `X` (i.e. a section of an invariant multifunction `D_T ⇉ D_T` whose values
> are `⊥ᵀ`-to-argument). Equivalently (Lutz Thm 5.35 / Siskind): no nonprincipal `V ≤_RK U_M` with
> `V ≠ U_M`. A DISPROOF supplies such a section (a counterexample `F`, `F_*U_M = V`); a PROOF shows no
> such section exists. **The section IS the counterexample IS the RK-predecessor.** There is no gap
> between "construct" and "refute-nonexistence" — they are one statement, negated.

**Why neither side is more tractable (the symmetry is genuine, not a failure of imagination).** The
proof side wants to *rule out* `V <_RK U_M` and `V ≡_RK U_M, V≠U_M` (Lutz's two sub-statements, §5.9);
Marks's conjecture ("every `f` is constant or injective on a pointed perfect tree", ZF+AD) would settle
the first (Prop 5.37) but is itself open and, per Lutz, "a proof or disproof would be a major advance."
The disproof side wants to *exhibit* such a `V`, i.e. an `f` that is neither constant nor injective on any
pointed perfect tree in the required way — the **exact negation** of Marks's conjecture localized to
`U_M`-predecessors. So the two directions are the two sides of Marks's conjecture. This is why the problem
is stuck *symmetrically*: it is not that proof is hard and disproof easy (or vice versa) — it is one
conjecture (Marks / RK-rigidity of `U_M`) whose truth = Part 1 and whose failure = a counterexample, with
AD's cone theorem giving a `{0,1}`-measure on invariant sets but no lever on the `≤_RK`-below structure.

### Honest verdict for the orchestrator
- The intuition "sideways info has no invariant source" is **TRUE on `D_T` but is a theorem-shaped
  statement, not a tautology** — it FAILS on `D_e` (Nakid-Cordero) and FAILS in ZFC on `D_T` (Thm 5.27).
  Its truth on `D_T` under AD is *exactly* Part 1; it is powered by the cone theorem's suppression of
  cofinal partitions + non-existence of a degree wellorder.
- **No construction survives.** Every AD tool (Unif_ℝ, scales, P-R, ultrapower) yields a selector that is
  definable-but-not-`≡ᵀ`-invariant, and invariantizing it = a section of `≡ᵀ` = `ω₁ ↪ ℝ`, AD-false. I did
  NOT find or fabricate a counterexample; I found the precise reason none is available.
- **No invariant/OD Posner–Robinson complement is known** in AD or `L(ℝ)`; the P-R literature is per-real
  only. This is the sharpest concrete sub-question and its answer is "open, believed unavailable, same wall."
- **Finding of record:** construction ≡ disproof ≡ negation-of-proof, all = "`U_M` has a nonprincipal
  RK-predecessor ≠ itself" = "Marks's pointed-perfect-tree dichotomy fails." The wall is symmetric; this
  explains the 50-year stall as a single locked object, not two independent hard directions.

**(B13, 2026-08-26) The e-degree counterexample is UNIFORM — it does NOT touch the open Turing core (sourced).**
Nakid-Cordero, "Martin's Conjecture in the Enumeration Degrees" (arXiv:2510.19147v2, Nov 2025), settles the
B9 question precisely. (i) The **skip** `A♦ = K̄_A` satisfies `A♦ ≰_e A` *always*, and `A ≤_e A♦ ⟺ A`
cototal `⟺ A♦ ≡_e A'`. The counterexample (Example 3.1) stitches `h(A)=A` on cototal / `A♦` on non-cototal
degrees — a Borel e-invariant function that is sideways on a cofinal class. (ii) The load-bearing step is
**Thm 5.1**: a *uniformly* e-invariant nonconstant `f` gives `A ≤_e f(A)` **or** `A♦ ≤_e f(A)`; the skip
branch appears because `≤_e` uses only **positive** information, so decoding on the "wrong side of the
symmetric difference" recovers the complement `K̄_A`. (iii) It **dies on Turing** because total degrees = the
Turing copy and every total degree is *cototal*, so there `A♦ ≡_e A'` and `A ≤_e A♦` (skip = jump,
increasing) — the sideways fork collapses, recovering the KNOWN uniform Turing result (Cor 5.5 = UMC 1).
**Two decisive honest points for our attack:** (a) the e-counterexample is **uniformly invariant**, hence
bears only on the *already-proved* uniform Turing case — it is NOT a counterexample-template for the open
*non-uniform* incomparable core; the increasing-jump fact is already fully consumed by our
`above-jump ⟹ above-id` (Groszek–Slaman) reduction, which still stalls at `escaping ⟹ MP`. (b) The *deeper*
Turing/e divide is **the absence of a Cone Theorem** for `D_e` (e-reducibility is not locally countable →
continuum-many cofinal pairwise-disjoint invariant classes → piecewise "stitching"); the Turing Cone Theorem
forbids exactly this partition, so Example 3.1 has no Turing analog *even before* the skip. The counterexample
is thus **over-determined** by Turing-specific facts (cone theorem + totality/cototality + no K-pairs), none
isolating a positive proof principle. Note also: Nakid-Cordero **refute Steel's conjecture for `D_e`** (a
Borel e-invariant `f` equivalent to no uniformly-invariant `f` on any cone, via maximal Kalimullin pairs) —
i.e. the "invariant ⟹ uniform on a cone" bridge is outright **FALSE in `D_e`**. So the Turing uniformity
bridge (our genuine crux) genuinely *requires* Turing-specific input (the cone theorem) and cannot follow from
soft/general reasoning — confirming the crux is exactly non-uniform→uniform, cone-dichotomy-vs-uniformization.

**(B14, 2026-08-26) CBER/superrigidity rigidity provably does NOT reach the incomparable core (sourced).**
Surveying Marks–Slaman–Steel (arXiv:1109.1875), Thomas "Martin's conjecture and strong ergodicity" (2009),
and Lutz's thesis: **every** MC↔CBER theorem runs one way, `MC ⟹ CBER-consequence` (Thomas's results are all
stamped "(MC)"; Popa cocycle superrigidity supplies *inputs* to MC-conditional theorems, never outputs a case
of MC). MSS state it outright: Martin's conjecture is *"a dimension of analysis completely orthogonal to
measure theory… all other known techniques for non-hyperfinite CBERs are measure-theoretic."* Two precise
facts: (i) ergodicity of `≡_T` under the Martin measure gives **only** `Δ`-ergodicity = the cone dichotomy
(the known-insufficient `{0,1}` coarseness); the stronger `E_0`-ergodicity that would constrain `≡_T → ≡_T`
homomorphisms is *itself* open and MC-conditional. (ii) Structural no-go: CBER/superrigidity tools see the
*equivalence relation* `≡_T` and its Borel-homomorphism/reducibility structure up to Martin-measure `0/1`, but
are **blind to the `≤_T` order between a class and its image** — which is the entire content of the
incomparable core. (Plus a hard mismatch: the Martin measure is not induced by any Borel probability measure
(Marks), so cocycle-superrigidity theorems — stated for pmp actions of rigid groups — do not even consume the
relevant measure.) **Verdict:** do not pursue CBER superrigidity as a forward tool; it is provably on the
wrong side of the MC↔CBER arrow. This independently re-confirms the RK-rigidity of `U_M`
(`escaping ⟹ MP` = "`U_M` has no nonprincipal RK-predecessor but itself", Lutz–Siskind §5.9) as the **sole
live route** — exactly the frame this session's `MeasurePreservingCK.lean` works in.

**(B15, 2026-08-26) Marks's conjecture attacks only the STRICT half — the frontier splits in two (sourced).**
Deep-dive on Marks's conjecture (Lutz thesis Conj 5.36, ZF+AD): *every function `f : 2^ω → 2^ω` (ARBITRARY,
not invariant) is constant on a pointed perfect tree or injective on a pointed perfect tree.* Status: **OPEN**
("surprisingly difficult", Lutz p.91); the non-pointed "perfect tree" version is TRUE (Sacks/Spector
tree-thinning, Lemma 2.7) — the whole difficulty is preserving **pointedness** (`T ≤_T x` for every branch)
through the fusion. **Key structural payoff — the RK-rigidity frontier is TWO independent halves**
(Lutz–Siskind Thm 5.15): (1) **strict half** `V ≤_RK U_M ⟹ U_M ≤_RK V` (= `U_M` RK-minimal), and (2)
**equivalence half** `U_M ≤_RK V ≤_RK U_M ⟹ V = U_M`. **Marks's conjecture ⟹ the STRICT half ONLY** (Prop
5.37: apply Marks to the invariant `f` inducing `V`; constant ⟹ `V` principal, injective ⟹ build `G` with
`G∘F = id` on the cone ⟹ `U_M ≤_RK V`). The **equivalence half is exactly this session's `g`-inversion gap**
(`V ≡_RK U_M, V≠U_M`) and its only known tool is Prop 5.24 (`{x : Cone(x) ∈ V} ∈ V ⟹ V = U_M`) / Siskind
ultrapower theory — a *separate*, non-Marks, inner-model problem. Converse (RK-rigidity ⟹ Marks) is NOT known;
Marks is plausibly strictly stronger. **CK-trichotomy does NOT attack Marks** (confirmed): (i) Marks's `f` is
non-invariant so `ω₁^{f x}` is not a degree-invariant — the cone theorem / `ck_dichotomy` (needs
`TuringInvariant`) don't even apply; (ii) even for invariant `f`, an ordinal rank can't yield injectivity on
degrees (can't separate incomparable degrees; `ω₁↪ℝ` forbidden) — and the naive "increasing↔injective,
preserving↔constant" pairing is *inverted* (Lutz's hyp-regressive case is CK-**preserving** yet concludes
`f x ≥_H x`, the injective/above side). The CK results live at the **measure/MP** level; Marks lives one level
below (tree/combinatorial), where the ordinal has no grip. **Genuinely novel operationalizable lead** (nothing
in the literature has traction): a **pointedness-preserving partition/fusion theorem** — a "pointed
Galvin–Prikry/Silver" or "pointed Sacks fusion" — is exactly where Marks's difficulty concentrates. Net: the
two halves need *different* tools (strict = pointed-tree combinatorics; equivalence = Siskind ultrapower);
even a full proof of Marks leaves the equivalence half open.

**(B16, 2026-08-26) The EQUIVALENCE half = kill case (2) of the Siskind trichotomy; g-inversion is irreducible; a novel un-closed avenue (sourced).**
Deep-dive on the equivalence half `U_M ≤_RK V ≤_RK U_M ⟹ V = U_M` (Lutz–Siskind §5; Siskind thesis §1.5–1.6;
Goldberg "Ultrapowers as iteration trees on HOD"):
- **Prop 5.24 (AD):** if `{x | Cone(x) ∈ V} ∈ V` then `V = U_M`. Proof: `A := {x | Cone(x)∈V} ∈ V` is uncountable
  (nonprincipal + ctbly-complete) so `Ã` is perfect (PSP), and countably-directed (`⋂ₙ Cone(xₙ) ∈ V` by ctble
  completeness meets `A`); **perfect + countably-directed ⟹ ≤ᵀ-cofinal** (Cor 4.5) ⟹ every cone ∈ V ⟹ `V=U_M`.
- **Siskind trichotomy Thm 1.5.8 (AD⁺):** a ctbly-complete ultrafilter `W` on `D_T` is (1) principal, (2)
  `{x | C̄_x ∈ W} ∈ W` (concentrates on **complements of cones**), or (3) `W = U_M`. **The equivalence half ⟺
  KILL CASE (2):** no nonprincipal `V ≡_RK U_M` concentrates on complements of cones. RK-equivalence does NOT
  supply Prop 5.24's hypothesis — case (2) is the un-excluded escape. This is a **clean self-contained target,
  more tractable than the full conjecture.** (For `V = F_*U_M`, the concentration hypothesis `{x|Cone(x)∈V}∈V`
  translates to "`F`'s range is `U_M`-upward-directed" `F X ≤ᵀ F X'` for `U_M×U_M`-most pairs; a ¬MP escaping
  `F` lands in case (2) — but directed+unbounded ⇏ cofinal for a mere tower, so an *elementary* kill fails;
  Prop 5.24's PSP + Cor 4.5 is essential, and RK-equivalence doesn't hand it to you.)
- **g-inversion = irreducible obstruction (verdict):** thesis **Thm 1.6.1** classifies factorization
  `f ≡_M h∘g` on a cone by a pure *fiber-refinement* criterion (`g(x)≡g(y) ⟹ f(x)≡f(y)`), with **NO** requirement
  `g,h ≤ id`; its worked example has `g = hyperjump`, both above id, `h` a measure-preserving *jump-lift* — so
  the invariant `g` witnessing `g_*V = U_M` is in general an **upward** MP map, the opposite of `g(y) ≤ᵀ y`.
  Part 2 (even if granted) gives `g(y) ≥ᵀ y`, the wrong direction. So `g∘F` MP ⟹ `g(F X) ≥ᵀ X` (machine-checked
  here as `gcomp_mp_recovers`) genuinely gives no `X`-vs-`F X` comparison. Not a hidden triviality.
- **Inner-model status (honest):** `Ult(HOD, U_M)` is well-founded and fine-structural (Goldberg with
  Schlutzenberg–Siskind, under AD+V=L(𝒫(ℝ))); Kunen's Thm 5.27 puts **all** ultrafilters on ordinals `< Θ`
  RK-below `U_M`. **But none of this yields RK-rigidity** — the ordinal-ultrafilter classification (solved) does
  NOT transfer to `D_T` (size continuum, non-ordinal). **The equivalence half is proved under NO hypothesis —
  not AD, AD_ℝ, nor AD+V=L(𝒫(ℝ)).** Siskind: a complete analysis of ctbly-complete ultrafilters on `D_T` would
  decide Part 1 and "may be a site of more tractable problems". `U_M` is **not commutative** (Fubini fails via
  `R(x,y) ⟺ x ∉ C_y`), and commutativity is `≤_RK`-downward-closed — cuts the wrong way for the equivalence half.
- **NOVEL un-closed avenue (the one genuine forward lead):** don't analyze `g` in isolation. In a real
  counterexample you have the **pair** `(F,g)` with `V = F_*U_M` (so `V` is NOT arbitrary — it concentrates on
  `F[cone]`) and `g_*V = U_M`. Combining "`V` concentrates on the `F`-image" with "`g` sends `V` to `U_M`" to
  force `{y | Cone(y) ∈ V} ∈ V` (i.e. NOT case (2)) is the place with slack the single-function analysis
  ignores — and it is not closed off in the literature. **This is the concrete next target for the equivalence
  half.**

**(B17, 2026-08-26) BOTH halves are Lutz–Siskind's explicit open Questions 3 & 4 (JAMS 2025) — strict half NOT separately known; + a machine-checked reduction.**
The published Lutz–Siskind (JAMS 38(2), 2025) lists, verbatim, the two halves as open questions:
- **Question 3 = STRICT half** = "`U_M` RK-minimal on `D_T`": *"Is there any ultrafilter on the Turing degrees
  strictly RK-below the Martin measure?"* — OPEN, not proved under any hypothesis (AD/AD_ℝ/AD⁺/AD+V=L(𝒫ℝ)).
- **Question 4 = EQUIVALENCE half**: *"any ultrafilter besides `U_M` weakly RK-equivalent to it?"* — OPEN.
- *"A negative answer to Questions 3 and 4 together would imply Part 1."*
So neither half is separately settled; the post-2023 activity is inner-model-theoretic (Siskind–Lutz
"order-preserving beyond Borel via IMT"; Goldberg–Sargsyan–Siskind HOD-ultrapower/meta-iteration machinery),
not yet delivering Q3/Q4. Nuance: `U_M` is NOT RK-minimal over ultrafilters on *ordinals* (Kunen Thm 5.27: all
`<Θ` ordinal-ultrafilters are RK-below `U_M`); Q3 is specifically about ultrafilters *on `D_T`*.
**This session's machine-checked reduction of the strict half** (`MartinStrictHalf.lean`, `MeasurePreservingCK.lean`):
`StrictHalfFor F (U_M ≤_RK F_*U_M) ⟺ DominatedInvertible F (∃ inv g, X ≤ᵀ g(F X) on a cone)`
(`strictHalf_iff_dominatedInvertible`, via `aboveId⟹MP` and `gcomp_mp_recovers`); and
`PointedInjectiveTree F ⟹ DominatedInvertible F` with the explicit map `g y = y⊕code`
(`dominatedInvertible_of_pointedInjectiveTree`). So Q3 (for pushforwards `F_*U_M`) is reduced to a single
named tree-existence `Nonempty (PointedInjectiveTree F)` — the injective analogue of `GroszekSlaman`, the
recursion-theoretic output of **Marks's pointed-perfect-tree conjecture**. Everything except that tree
construction is now machine-checked.
**Corrections (from the JAMS-2025 read):** (i) "`U_M` is not commutative" is a *thesis*-level statement, NOT
in the published paper — the published tool is the ω₁-pushforward + **Fubini** argument (Thm 5.22/Lemma 5.20:
every `f:2^ω→ω₁` is constant on a positive-measure set), used to show `U_L, U_B` are not RK-*above* `U_M`.
(ii) Whether `U_L/U_B` are RK-*below* `U_M` is open **Q5** (special case of Q3); Marks–Day: under AD_ℝ,
`U_L ≤_RK U_M ⟺ ∃` Turing-invariant `f` with `f(x)` always `x`-random. (iii) `U_M` non-selective (jump
non-1-1 on cones yet MP) — so "prove `U_M` selective" is a dead end, confirmed.

**(B18, 2026-08-26) The DOMINATED-INVERTIBILITY reformulation — cleanest machine-checked capstone for both halves.**
Both Lutz–Siskind open questions collapse to one notion.  `DominatedInvertible F` := `∃` invariant `g`,
`X ≤ᵀ g(F X)` on a cone ("`F` is *recoverable*").  Machine-checked (`MartinStrictHalf.lean`,
`MeasurePreservingCK.lean`, std axioms):
- `strictHalf_iff_dominatedInvertible`: `StrictHalfFor F (U_M ≤_RK F_*U_M) ⟺ DominatedInvertible F`.
- **`partI_of_DI_conditions`** (capstone): **Part 1 = (Q3) every non-constant invariant `F` is
  dominated-invertible ∧ (Q4) DI ⟹ MP.**  I.e. *"non-constant ⟹ recoverable"* ∧ *"recoverable ⟹ above-id"*.
- **Q3 fragments/handles:** `PointedInjectiveTree F ⟹ DI` (explicit `g y = y⊕code`);
  `strictHalf_of_countableFibered` = the countable-fiber case PROVED (named MSS input `CountableFiberMarks`);
  `dominatedInvertible_fiber_bounded` (DI bounds fibers *on its cone* — necessary);
  `partI_false_of_not_dominatedInvertible` (`¬DI ∧ non-const ⟹ Part 1 false` — honest disproof target).
- **Q4:** `EquivHalfFor` = `DI ⟹ MP`; `gcomp_mp_recovers` (`g∘F` MP ⟹ `g(F X) ≥ᵀ X`) is exactly the stall —
  it makes `g∘F` above-id, not `F`; `equivHalf_of_rangeInKernel` = concentrated fragment PROVED (Prop 5.24).

**Two honesty corrections made while formalizing (superseding B13/agent framing):** (i) **the "jump has
uncountable fibers" claim is FALSE** — the jump (any increasing `F`) is *bounded*-fibered
(`{d : d' ≡ᵀ c} ⊆ {d ≤ᵀ c}`) and trivially DI (`g = id`); the "jump reals-injective on a pointed tree" test
is trivial (`x ≤ᵀ x'`). (ii) **"unbounded fiber ⟹ ¬DI" is FALSE** — `dominatedInvertible_fiber_bounded`
bounds fibers only on *the* DI-cone, not globally (`F d = if d ⊥ 0' then 0' else d` has a globally-unbounded
fiber `{d ⊥ 0'}` yet is the identity on `cone(0')`, so DI).  So there is **no clean single-fiber
characterization of Q3**, and the "pointed-Silver / make the perfect set pointed" framing targets
*reals*-injectivity — a stronger, separate statement, not the degree-level strict half.  Net honest open
content: **Q3 = "is every non-constant invariant `F` dominated-invertible (recoverable)?"** (combinatorial
existence) and **Q4 = "DI ⟹ MP"** (inner-model, the g-inversion gap) — genuinely different walls.

---

# B19 (2026-08-26) — GENUINE ATTEMPT at the pointed INJECTIVE fusion (Marks's conjecture)

*Target: Marks's Conjecture (Lutz thesis Conj 5.36) — under ZF+AD every `f:2^ω→2^ω` is **constant on a
pointed perfect tree OR injective on a pointed perfect tree**. This implies the strict half of Part 1
(Prop 5.37). The non-pointed version is trivial (Lutz p.92: "Marks's conjecture is true if 'pointed perfect
tree' is replaced by 'perfect tree' — the argument is just a version of the tree thinning lemma"). The whole
difficulty is **pointedness**. This section: read the exact mechanisms from primary sources (Lutz thesis
§2.1, §2.3, §5.3–5.4, §5.9; Marks essay; Nakid-Cordero arXiv:2510.19147), attempted the fusion five ways,
and pins the exact obstruction. Honest verdict: NOT solved; the obstruction is now located much more sharply
than before and one of the five framings (the prior "GS-coding vs Silver collision") is CORRECTED.*

## B19.0 The exact mechanisms (verbatim from Lutz thesis, this session's read)

Three tools, precisely:

- **Lemma 2.7 (Tree thinning).** `T` pointed perfect, `Φ` a Turing functional **total on [T]** (Φ is a fixed
  computable functional, computable *from T*): EITHER `Φ` is constant on some `[T_σ]`, OR `T` thins to a
  pointed `S⊆T` with `Φ` injective on `[S]`. **Pointedness of `S` is FREE** because the thinning is
  computable-in-`T` (`S≤ᵀT`) so every branch of `[S]⊆[T]` computes `T` hence `S`. *This is Sacks/Spector
  forcing.* Requires `Φ` **computable**.
- **Lemma 2.3 (Inverting).** `Φ` computable, total + injective on `[T]` ⟹ `Φ(x)⊕T ≥ᵀ x` for `x∈[T]`
  (compactness). So a computable injective functional below `f` on a pointed tree ⟹ `f` above-id there.
- **Thm 2.19 (Groszek–Slaman coding, the basis theorem).** Perfect `A`, countable dense `B⊆A`, `c` with
  `b≤ᵀc ∀b∈B`: for every `x`, ∃ `y0,y1,y2,y3∈A` with `c⊕y0⊕y1⊕y2⊕y3 ≥ᵀ x`. **4 branches.** The bits of `x`
  are coded into *least-program-index comparisons* `e_i` (which program computes `b_i∈B` from `c`), NOT into
  the geometric left/right turns (that was the *un*-strengthened GS Thm 2.18 / the regressive-degrees proof).

**★ KEY STRUCTURAL CORRECTION to the prior "collision" framing (`MARTIN_PART1_STRICT_MARKS.md` §3).** In
**every** successful pointedness-preserving proof in the thesis (regressive Thm 5.10, order-preserving
Thm 6.3, measure-preserving Thm 5.15/5.18), **pointedness is delivered by Lemma 2.7 (tree-thinning), NOT by
GS-coding.** GS-coding (Thm 2.19) is used only to prove *above-identity* for **order-preserving** `f`, via
Cor 2.21: an order-preserving `f` has a **range that is countably-directed for `≤ᵀ`**, so the range is
cofinal and the coding fires. The coding is NOT the "pointedness engine." Therefore the prior framing —
"Silver value-separation *fights* Groszek–Slaman pointed-coding over branch positions" — **mis-identifies the
collision.** GS-coding and Silver are not the two combatants. **The real tension is:** tree-thinning
(Lemma 2.7), the actual pointedness engine, **requires a *computable* functional to thin against**, and for
the general injective case there is no computable injective witness below `f`.

## B19.1 The sharpened obstruction (what actually breaks)

The template that WORKS (regressive/OP/MP): (1) produce a **computable** `Φ` below `f` on a pointed `T`
(computable uniformization Lemma 2.11 + Martin cofinal→pointed Lemma 2.9); (2) **thin** to make `Φ` injective
(Lemma 2.7 — pointedness free); (3) **invert** (Lemma 2.3) ⟹ `f` above-id.

For a **general non-constant invariant `f`** (uncountable cone-null fibers, e.g. an *escaping/incomparable*
`f` if one exists), the strict half wants **injectivity**, and Silver's dichotomy gives `f` injective on a
**perfect** `P` — but:

> **THE OBSTRUCTION, precisely.** Silver injectivity is injectivity of **`f` itself**, and `f` is an
> *arbitrary invariant, non-continuous* function. Lemma 2.7 (the only pointedness-free thinning) applies
> **only to a computable `Φ`**. To make `P` pointed we would need a *computable-in-`T`* functional to thin
> against; Silver hands us no such witness. **The pointedness engine (2.7) and the injectivity source
> (Silver) are incompatible at the interface: 2.7 needs computability, Silver produces none.**

This is the SAME wall, restated, as "no computable injective witness below a general `f`." For MP `f` the
witness comes from the increasing **modulus** (Lemma 5.14, needs `AD_ℝ`/`AD⁺`) inverted by Cor 2.12. **A
general injective `f` has no modulus** (modulus ⟺ measure-preserving), so this source is gone. This is why
the countable-fiber case (§B19.2) is the exact boundary of what elementary tools reach.

## B19.2 Why COUNTABLE fibers is the exact boundary (and it is NOT about "countable = easy pointedness")

Refined understanding of the MSS countable-fiber theorem (`strictHalf_of_countableFibered`): with countable
fibers, **Lusin–Novikov** writes `f = ⋃ₙ (injective Borel `fₙ`)` — the pieces `fₙ` are **Borel, hence
computable relative to a fixed real (a Borel code)**. So the piece-selector `π(x)=` "the `n` with `x∈Bₙ`" is a
function to `ℕ` (countable range), and **Martin's pointed-tree lemma (2.10 / MSS 3.5)** makes `π` constant on
a pointed `[T]⊆Bₙ`. On `[T]`, `f=fₙ` is Borel-injective — **and now `fₙ` IS a computable-relative-to-a-fixed-
oracle functional**, so we are back in the tree-thinning regime (or injectivity is already witnessed by the
Borel code + Lemma 2.3 relativized). **The countable case works precisely because Lusin–Novikov manufactures
a COMPUTABLE (Borel) injective witness — exactly the thing the general case lacks.** The boundary is not
"countable range is combinatorially nice"; it is "countable fibers ⟹ a *Borel/computable* injective
decomposition exists (LN) ⟹ tree-thinning applies." **Uncountable fibers ⟹ LN fails ⟹ no computable injective
witness ⟹ no purchase for Lemma 2.7.** This is the crux, now correctly attributed.

## B19.3 The five requested angles, worked and adjudicated

**(1) Recursion theorem for self-reference.** Idea: build `T` so its code is available during construction,
baking `f`-separation in while branches read off `T`. *Verdict: does NOT bridge the gap.* The recursion
theorem gives self-reference to the *construction's own index*, i.e. lets the thinning rule mention `T`'s
code. But the thing being separated is `f`-**values**, and `f` is non-continuous: at a splitting node σ we can
separate `f` on two *finite* extensions (find `τ0,τ1⊇σ` with `f(τ0⌢·), f(τ1⌢·)` disagreeing at some finite
level for SOME branches), but `f` depends on the whole branch and the finite disagreement **need not persist
to the limit branches** (the modulus problem). The recursion theorem controls the *tree*'s self-knowledge,
NOT `f`'s modulus. To make finite separation persist you need an `f`-modulus, which for injective-not-MP `f`
provably does not exist (modulus ⟺ MP). **The recursion theorem is orthogonal to the finite-vs-limit tension;
it addresses pointedness-self-reference (already handled by 2.7's computability), not `f`-continuity.**

**(2) Residual freedom (sparse coded skeleton).** Idea: GS-coding pins only 2–4 branches; the generic branch
is free, so a sparse skeleton carries pointedness while other branches steer `f`-values apart. *Verdict:
based on the corrected mechanism (B19.0), this is a CATEGORY ERROR.* Pointedness is NOT carried by the coded
branches — **every** branch of a pointed tree must compute `T`, and that is delivered wholesale by
2.7-thinning (`S≤ᵀT`), not by coding 2–4 branches. The GS-coding's 4 branches establish *above-identity for
order-preserving `f`* (range-cofinality), a different goal. So "spend the coded branches on pointedness, free
branches on separation" does not typecheck: pointedness is a *global* property of *all* branches, automatic
under thinning, and needs no branch budget. The residual-freedom intuition was answering the wrong question.
**However** there is a salvageable kernel (see B19.4): the coding IS a way to force branch *degrees* upward
compatibly with a prescribed geometric skeleton — relevant if one tries to *manufacture* a computable
injective witness, which is the real need.

**(3) Pointed Silver / pointed Galvin–Prikry.** Idea: a Ramsey/perfect-set partition theorem that delivers a
*pointed* homogeneous set. *Verdict: this is the correct shape of what's needed, and it is EXACTLY Marks's
conjecture — no shortcut, no known such theorem.* Martin's pointed-tree lemma (2.10) IS "pointed Ramsey for
**countable**-valued colorings" (a countable-range `h` is constant on a pointed `[T]`). Marks's conjecture is
the **2-valued-but-continuum-target** analogue (constant-or-injective). Silver's theorem for `E_f` gives a
perfect homogeneous (= transversal) set; the pointed upgrade is open. Searched: no "pointed Silver/Galvin–
Prikry" exists in the literature; the Mathias/Ellentuck generic that witnesses Ramsey is a *generic* real,
and generics **avoid cones** (Lutz §5.6: "generic reals avoid a cone"), i.e. are the *opposite* of pointed
(pointed = computes-the-tail-structure; generic = decided-by-no-tail). **This is a genuine structural reason
the Ramsey route resists pointing: the large-set witness is generic, and generic ⊥ pointed.** New observation
this session, and it is a real (if negative) insight: *any* proof of Marks via a Ramsey-generic homogeneous
set must fight the generic-vs-pointed antagonism; the pointed witnesses live in a measure/category-null cone
that the generic construction actively avoids (this is precisely W1 from `MARTIN_BREAKTHROUGH_ATTEMPT.md` —
the cone is meager+null — re-surfacing in the Marks framing).

**(4) Reduce to invariant `f` (use invariance + cone-nullness).** Idea: for the strict-half application `f`
is invariant; invariance makes fibers cone-null; drive separation-with-pointedness from that. *Verdict: gives
a GENUINE usable lemma (below) but not the fusion.* Real content extracted: **no pointed perfect tree is
`E_f`-monochromatic** for non-constant invariant `f`. Proof: if `f` were `≡ᵀ`-constant on a pointed `[T']`,
that fiber ⊇ `cone(deg T')` (pointed ⟹ realizes a cone), contradicting cone-null. So on **every** pointed
tree the *constant* alternative of Marks is already false — meaning for invariant `f` the Marks dichotomy is
**forced into the injective branch on every pointed tree**. This SHARPENS the target: we don't need "constant
OR injective," we need, on *some* pointed tree, to upgrade "not-monochromatic" (2 inequivalent branches
exist) to "fully injective" (all branches pairwise inequivalent). But this upgrade is a fusion through ω
levels maintaining pairwise `E_f`-separation of the limit branches — and **`E_f`-separation of *limits* is
again the non-continuity/modulus wall** (finite separation at a node ≠ limit separation). Cone-nullness gives
separation *exists* locally; it does not give a *computable modulus* forcing it to the limit. Same wall.

**(5) High-stakes: is there an invariant `f` with NO pointed injective AND no pointed constant tree
(disproof)?** *Verdict: STRONG evidence AGAINST a disproof — the natural disproof template provably fails in
the Turing degrees.* The one place in the literature where the analogous dichotomy is DISPROVED is the
**enumeration degrees** (Nakid-Cordero 2025, arXiv:2510.19147): he builds a definable e-invariant function
not equivalent to any uniformly-invariant one. **But his construction's engine is the FAILURE of the Cone
Theorem in the e-degrees** ("the ultimate culprit of this difference is the lack of a Cone Theorem for the
enumeration degrees"), exploiting the **quasiminimal (non-total) e-degrees** which have **no Turing
analogue**, and the **skip is not increasing** (whereas the jump is). All three enabling features — no cone
theorem, non-total degrees, non-increasing skip — are **absent in the Turing degrees** (Turing has the cone
theorem, all degrees "total", jump increasing). So the sole known counterexample template is **structurally
blocked** in the Turing setting. This is positive evidence Marks is TRUE, and it localizes *why* the Turing
case is hard-but-plausibly-true: the cone theorem is exactly the tool that would have to be leveraged, and it
is a *global* (measure) tool that (W1) is orthogonal to the cone the pointed witness lives in. Net: a Turing
disproof would need a fundamentally new mechanism not present in the e-degree counterexample.

## B19.4 The one concrete forward lead this session produces

The corrected obstruction (B19.1–2) says the whole game is: **manufacture a computable injective functional
below `f` on a pointed tree.** For MP `f` this is the inverted modulus; for countable-fiber `f` it is the
Lusin–Novikov Borel piece. The open case is uncountable fibers with no modulus. **Lead:** the GS-coding
(Thm 2.19, salvaged from angle 2) is precisely a device that makes branch *degrees* recover a prescribed real
using finitely many branches of a *given* perfect set — i.e. it can *build* a functional `Ψ` with
`Ψ(y0⊕…⊕y3) = x` that is computable and injective-in-a-generalized-sense on the coded branches. The question
this reframes to: **can one code the `E_f`-class of a branch into the branch itself** (a "self-coding"
tree) so that `f(x)` computes enough of the coding to recover `x`'s position — turning `f` into its own
computable injective witness? This is a *coding-against-`f`* rather than coding-against-a-target-real. It is
not obviously circular (unlike the incomparable-core coordinated-tree route, B12), because it targets
injectivity (a Silver-type separation) not domination. **Whether `f`-value-coding can be maintained to the
limit is, once more, gated by an `f`-modulus** — so this lead does not escape the wall either, but it is the
sharpest concrete formulation: *Marks-for-invariant-`f` ⟺ every non-constant invariant `f` admits an
`f`-value self-coding perfect tree convergent to the limit* — a single modulus-existence question.

## B19.5 Honest verdict on pointed injectivity

**NOT achievable by any elementary fusion, for a precise and now-correctly-attributed reason:** the only
pointedness-preserving thinning (Lemma 2.7) consumes a **computable** injective witness, and Silver's
theorem — the sole unconditional source of injectivity for a general invariant `f` — produces **no computable
witness** (it separates `f` itself, which is non-continuous). Every source of a computable injective witness
that the literature knows (modulus for MP `f`; Lusin–Novikov for countable-fiber `f`; range-cofinality/GS-
coding for order-preserving `f`) requires a **special structural property of `f`** that a general (uncountable-
fiber, non-MP) invariant function lacks. The four prior "cautious optimism" handles (recursion theorem,
residual freedom, pointed Ramsey, invariance) each dissolve into the **same** underlying wall — the absence
of an `f`-**modulus** to push finite `f`-value separation to the limit — which is provably equivalent to `f`
being measure-preserving. **Corrections booked:** (i) the "GS-coding vs Silver" collision was mis-framed
(GS-coding is not the pointedness engine; tree-thinning is); (ii) "residual freedom of coded branches" is a
category error (pointedness is global/automatic under thinning, not a branch-budget); (iii) the pointed-
Ramsey route faces a real *generic-vs-pointed* antagonism (generics avoid the cone the pointed witness needs).
**Disproof (angle 5) is strongly disfavored:** the only known counterexample (e-degrees) runs on the failure
of the Cone Theorem + non-total degrees + non-increasing skip, all absent in the Turing degrees. **Net:
pointed injectivity for general invariant `f` is open, reduces cleanly to a single `f`-modulus-existence /
`f`-value-self-coding question (B19.4), and every elementary route bottoms out at modulus-existence ⟺ MP —
i.e. it is not a shortcut around the measure-theoretic frontier but the SAME frontier wearing combinatorial
clothes.** This matches, and independently re-derives via the Marks framing, the measure-route bottom line
(`MARTIN_PART1_RK_MEASURE.md`): both walls are "no invariant control of `f`'s value-distribution," which is
the inner-model-theoretic RK-rigidity of `U_M`.
