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
