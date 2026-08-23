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
