# Status — Martin's conjecture in Lean 4 / Mathlib

Machine-checked formal progress on **Martin's conjecture** on degree-invariant functions.
Full `lake build` green; **0 sorries, 0 custom axioms** (every headline theorem audited via
`#print axioms` — only `propext, Classical.choice, Quot.sound`). Determinacy is **never**
axiomatized: it is threaded as an explicit hypothesis `TuringDeterminacy Γ` (with
`Γ := fun _ => True` the ZF+AD form; open/closed instances are ZFC theorems).

This file is the current-state map. `ATTACK.md` is the living log of the open-problem attack
(constraints + counterexample attempts). Everything below is in namespace `Martin`.

### Session 2026-08-26g — the pointed-tree engine + Marks route (Prop 5.37) machine-checked
**→ `Lemma210.lean`, `Lemma211.lean`, `MarksBridge.lean`.** Built the pointed-perfect-tree uniformization
engine as clean general lemmas and used it to formalize the Marks route to the incomparable core.
- **`Lemma210.lean`** (Lutz Lemma 2.10, from `MartinPPT'`): a countable-range `h` is constant on a pointed
  perfect subtree of any cofinal set (`lemma210_of_martinPPT'`, `exists_constant_pointedTree`,
  `exists_constant_pointedTree_bool`). The single-real "countable-range constancy" engine.
- **`Lemma211.lean`** (Lutz Lemma 2.11 + Cor 2.12): a relation `R ⊆ ≥ᵀ` with cofinal domain is uniformized
  by one Turing functional on a pointed tree (`lemma211_of_martinPPT'`); increasing `f` has a computable
  right inverse on a pointed tree (`cor212_of_martinPPT'`). *(NB: the GroszekSlaman-specific content of these
  was already inlined in the repo's `groszekSlaman_of_martinPPT`; these are the clean general restatements.)*
- **`MarksBridge.lean` (the genuinely new piece): Lutz Prop 5.37 machine-checked.** `MarksTree F` (a pointed
  perfect tree on whose branch-degrees `F` is constant-or-injective) ⟹ `ConstantOnCone F ∨ DominatedInvertible F`
  (`constantOrDominatedInvertible_of_marksTree`), via `PPT.realizes` transporting branch-constancy/injectivity
  to a cone + `dominatedInvertible_of_injectiveOnCone`. Packaged: `constantOrStrictHalf_of_marksTree`,
  `strictHalf_of_marksConjecture` (Marks ⟹ strict half of RK-rigidity), and the **capstone**
  `partI_of_marksConjecture_and_equivHalf` (Marks conjecture + equivalence half Q4 ⟹ Part 1, via
  `partI_of_halves`) and `no_incomparable_of_marksConjecture_and_equivHalf` (Marks + Q4 ⟹ **no incomparable
  invariant `F`** = Part 1's sole open content directly). `marksTree_of_injectiveOnCone` pins the wall: Marks
  holds whenever `F` is injective on a cone, so the ONLY open content is `F` injective on **no** cone (needs
  tree-thinning Lemma 2.7 for a functional).
  All std axioms, full build 3117 green.
- **`DIWitness.lean` (new — characterizes the Q4 disproof target).** A *dominated-inverting witness* `g`
  (`X ≤ᵀ g(F X)` on a cone) for an **incomparable** `F` must be **non-regressive / jump-type**:
  `aboveId_of_regressive_diWitness` (regressive `g c ≤ᵀ c` ⟹ above-id, since `X ≤ᵀ g(F X) ≤ᵀ F X`);
  `not_regressive_diWitness_of_incomparable`; `diWitness_liftsValues_of_incomparable` (`g(F X) ≰ᵀ F X`
  cofinally). `dominatedInvertible_inflationary` (WLOG `c ≤ᵀ g c`). Honesty pair: `everyInvariant_below_mp`
  (every invariant `F` is below the MP function `(X⊕F X)′`, so "below MP" is vacuous) vs
  `dominatedInvertible_mpFactorsThroughF` (the real content: the MP dominator factors through `F X` alone).
  So a Q4 counterexample recovers `X` from an invariant *jump-type lift* of `deg(F X)` — matching `X ≤ᵀ (F X)′`
  while `F X ⊥ᵀ X`. **Q3 side:** `notDI_escapes_jumpIter` (¬DI ⟹ `X ≰ᵀ (F X)^{(n)}` for every finite jump-iterate),
  `notDI_incomparable_jumpSymmetric`. **Capstones:** `measurePreserving_iff_regressive_diWitness`
  (`MP ⟺ DI-via-regressive-witness`, separating solved side from open core) and **`incomparable_dichotomy`**
  (an incomparable `F` is either Q4 value-lifting-DI or Q3 jump-transcendently-lossy — the two disproof horns
  in one statement). Std axioms, full build 3118 green.
- **Net + next steps.** The reduction of Part 1's incomparable core to `[Marks conjecture ∧ equivalence-half
  Q4]` is now fully machine-checked, and both disproof targets are sharply characterized. Confirmed (multiple
  fresh attempts) that the residue is *invariant realizability* = RK-rigidity of `U_M`, not crossable by
  elementary/measure/combinatorial means (a counterexample is ZFC-constructible via a wellorder, AD-blocked at
  the invariant-selector step = `ω₁↪ℝ`). **Concrete next-steps (corrected):** (a) tree-thinning Lemma 2.7
  (functional ⟹ const-or-injective on a pointed subtree; a Sacks fusion) — would give Marks-for-functionals;
  (b) the Q9.3 2-uniform collapse is NOT a pair-tree problem — for fixed `(i,j)`, `Y=Φ_i^X` is single-real, so
  Lemma 2.10 (`exists_constant_pointedTree_bool`) fixes the branch per-`(i,j)`; the wall is *across* all
  `(i,j)` (the full assignment is `2^{ℕ²}`-valued = uncountable = the same core wall), needing a
  diagonal/Slaman–Steel-kernel combination, not a single tree. **Sharpest math frontier:** Woodin's generic
  ultrapower for the Martin-measure
  ideal (crit `= ω₁`, repr. `x↦ω₁ˣ`), open at the rigidity step — see `uniformization-engine-wall`,
  `di-witness-q4-target` memories and `MARTIN_STRICT_HALF_AND_Q4.md`.

### Session 2026-08-26f — Lutz-thesis primary-source dive: corrections, the decisive mechanism, Q9.3 formalized
**→ `MARTIN_BREAKTHROUGH_ATTEMPT.md` ("decisive mechanism" + "one object, three names").** Read the Lutz
thesis (pdftotext) directly. Outcomes:
- **`TwoUniform.lean`** (new, 3 thms, std axioms, build 3114 green): formalizes Lutz **open Question 9.3**
  (Martin's conjecture for *2-uniformly invariant* `F`). `TwoUniformlyTuringInvariant`; `.of_uniform`
  (uniform ⊆ 2-uniform); `.turingInvariant`; and **`partI_twoUniform_of_uniformize`** — Part 1 for all
  2-uniform `F` reduces to "every 2-uniform `F` is Martin-equiv to a uniform `G`" (a sub-case of Steel's
  Conj 9.4, plausibly more tractable), mirroring `incomparable_core_of_uniformization`. The hard collapse
  (fix the `{1,2}` branch on a pointed tree via Lemma 2.10) is documented as next step, not assumed.
- **`Lemma210.lean`** (new, 3 thms, std axioms, build 3115 green): derives **Lutz Lemma 2.10** (a
  countable-range `h` is constant on a pointed perfect subtree of any cofinal set) from the repo's
  `MartinPPT'` (Lemma 2.9). `cofinal_fiber` (some fiber `A∩{h=n}` stays cofinal, via `joinFam` of the
  fiber-bounds), `lemma210_of_martinPPT'`, and the clean `exists_constant_pointedTree` (`A=⊤` form). This is
  the engine under the whole regressive/MP uniformization (Lemma 2.11 = this applied to the reduction index);
  it supplies the single-real form of the "countable-range constancy" tool flagged missing for Q9.3. The
  pair/relation form (Lemma 2.11, needs `OracleCode`/`eval`) is the sharpened remaining step.
- **The decisive mechanism (source-grounded):** under AD the ONLY "cofinal → uniform-on-a-pointed-tree"
  engine is the countable-range trick (Lemma 2.10); Lemma 2.11/Cor 2.12 uniformize `R` to a functional iff
  `R ⊆ ≥ᵀ`, because the ℕ-valued datum is the reduction index, existing iff `f(x)≤ᵀx`. So regressive/MP are
  theorems; the incomparable core has NO ℕ-index (its separating invariants `ω₁ˣ` are ordinal-range, for which
  2.10 provably fails ⟹ `ω₁↪ℝ`). Part 1's open content = exactly the **ℕ-range vs ordinal-range gap**; the
  generic-ultrapower critical point (`x↦ω₁ˣ`) is the SAME object. Unifies W1/W2/W4.
- **Corrections (primary-source verified):** (i) the "proper-forcing lead" was mis-directed — the worked
  sketch proves `proper ⟹ not-RK-ABOVE U_M` (kills `U_L,U_B`; wrong direction); RK-BELOW is Lutz's open
  speculation only. (ii) Thm 5.35 (Part 1 ⟺ RK-rigidity) is **ZF+AD_ℝ**; MP Part 1 is **AD+DC_ℝ** (confirms
  the agent-B axiom correction). Catalogued Lutz's open questions 9.3, 9.9–9.14, 9.18–9.20 as concrete targets.

### Session 2026-08-26e — parallel frontier probes: two sharpenings + two hard no-gos
**→ `MARTIN_BREAKTHROUGH_ATTEMPT.md` (second-round section), `MARTIN_COUNTABLE_KERNEL.md`,
`MARTIN_VALUE_CLEANUP_AND_INDEPENDENCE.md`.** Two independent source-grounded deep-dives against the sharpest
target (kill Siskind case-2 / prove Steel 1.4). Still open (as expected), but genuine machine-checked output:
- **`CountableKernel.lean`** (std axioms): for a case-2 predecessor `V = F_*U_M`, the Prop-5.24 concentration
  set `{d | Cone(d) ∈ V}` **is** `BelowF F`, and it is **countable — bounded by a single real `r_K`**
  (`case2_kernel_bounded_of_countable`). Sharper than the prior "kernel avoids a cone." The "countable ⟹ one
  real" step is now proved in-repo (`countableUpperBound` via `Cantor.joinFam`) — the earlier `DC_ℝ`
  hypothesis was discharged, so it rests on a single named classical input `Prop524Countable`.
- **`ValueCleanup.lean`** (std axioms): value-side twin of `canonicalRepresentative_no_gain`. A fixed
  binary-uniform value-preserving cleanup `G x = Ψ x (F x)` is Martin-equiv to `F` and uniform iff `F` is
  (`valueCleanup_no_gain`); the degree-changing join cleanup breaks Martin-equiv on the core
  (`join_cleanup_breaks_equiv`). Trichotomy sharpens W6 to the value side.
- **Two hard no-gos:** (a) Goldberg UA/Ketonen is defined only for ultrafilters on *wellordered* sets, so it
  does not type-check for `U_M` under AD — the "obvious" inner-model weapon is inapplicable; (b) the
  enumeration-degree failure of the analogous statement needs Kalimullin pairs + quasiminimal degrees, both
  ZF-absent in `D_T`, so it is evidence *for* the Turing conjecture, not an independence route. Working
  verdict: Part 1 is **true under AD**; no independence is known or conjectured.
- **Synthesis** (both sides, machine-stated): a minimal counterexample is **"thin-below, sideways-valued"** —
  domination kernel bounded by one real `r_K`, yet `¬(F X ≤ᵀ X ⊕ r_K)` on every cone. The kernel bound has
  **no maximum** (r_K bounds it but `r_K ∉` kernel — that would need the obstructed uniform join), so the
  sharpening is self-similar and cannot collapse to one degree.
- **Corrected a mis-promoted lead** (read Lutz thesis ch. 5 directly): the proper-forcing argument proves
  *`proper ⟹ U not RK-**above** U_M`* (kills `U_L, U_B`; wrong direction for the incomparable core). The
  `RK-below` version Part 1 needs is Lutz's explicit **open speculation** ("properness is one candidate …
  Slaman: non-collapse of 𝔠 another"), not a worked path. So there is **no worked lead** into the core; the
  rigorous frame for a future attack is Woodin's generic ultrapower (crit `= ω₁`), open at the rigidity step.

### Session 2026-08-26d — "invent the machinery" breakthrough attempt on the incomparable core
**→ `MARTIN_BREAKTHROUGH_ATTEMPT.md`.** Genuinely tried ~22 ideas + 8 research dives to crack the core; NOT
solved (open even for experts). Three machine-checked by-products (std axioms, green):
- **`canonicalRepresentative_no_gain`** (`CanonicalRepresentative.lean`): `F∘c` uniform ⟺ `F` uniform for
  fixed computable degree-preserving `c` — input-reparametrization is uniformity-**neutral**; the obstruction
  is entirely in `F`'s **values**.
- **`incomparable_not_uniform`** (`MartinResults.lean`): incomparable `F` ⟹ ¬uniformly-invariant. So the
  incomparable core is exactly the (unknown!) source of non-uniform `T`-invariant functions.
- **`measurePreserving_iff_hasModulus`** (`MeasurePreserving.lean`): MP ⟺ `F` has an increasing modulus — the
  converse of Lemma 3.3, capturing the **convergence**: a Marks pointed *injective* tree needs a computable
  witness ⟺ a modulus ⟺ MP, so the Marks/combinatorial and measure routes bottom out at the *same* wall.
- **6-wall obstruction map** (W1 cone-orthogonality — PROVED: incomparable `F` is nowhere-continuous on the
  cone; W2 fat fibers; W3 definable≠computable; W4 countability; W5 invariance-mismatch; W6 circularity) and
  the precise inner-model target: RK-rigidity ⟺ `U_M`'s HOD-iterate minimal among `D_T`-ultrafilter iterates
  (factor map `k`). All routes converge on "no invariant control of `F`'s value-distribution" — open even at
  the Steel–Siskind–Goldberg frontier.

### Session 2026-08-26c — Steel's Conjecture 9.4 (uniform-representative) attack: canonical coding launders nothing

> **New angle, distinct from the measure (RK-rigidity) and Marks (pointed-injectivity) routes.**
> Target: **Steel's Conjecture** (Nakid-Cordero Conj. 1.4; a survey's 9.4) — *under AD, every T-invariant `F`
> is Martin-equivalent on a cone to a UNIFORMLY invariant `G`*; it implies MC Part 1, and its Borel form is
> *equivalent* to Borel MC (Marks). Five constructions of `G` from an arbitrary invariant `F` were attempted;
> the naive "canonical representative" is **machine-checked dead** and the rest are localized.

**→ `MartinsConjecture/CanonicalRepresentative.lean`** (new, sorry-free, standard axioms; in root build).

- **Construction #1 (canonical branch via pointed tree) — RIGOROUSLY KILLED.** Take a *fixed computable*
  degree-preserving coding `c` (e.g. even-bits `c x = join x 0`, coding `deg x` into a pointed perfect tree),
  set `G = F∘c`. `G x ≡ᵀ F x` for free (invariance), so Martin-equivalence is automatic. The hope that the
  fixed procedure `c` launders `F`'s non-uniformity is **provably false**: `canonicalRepresentative_no_gain`
  — for any uniformly-degree-preserving computable `c` with a fixed section, `F∘c` is uniformly invariant
  **iff** `F` is. Mechanism: coding steps are *fixed* equivalences, so composing through them is only a
  **fixed computable index-shift** (`EquivVia.trans_trE`, built on Bard's composable-functionals `trE`).
  The "x_x depends on the real x" worry in the prompt is *dissolved* by using a fixed computable `c` — and
  the deeper truth is worse: the coding contributes **zero** uniformity either way. **The entire obstruction
  lives in `F`'s values, never in the choice of representative.** Any reparametrization of *inputs* is
  Martin-equivalent-for-free but uniformity-neutral; a genuine `G` must alter `F`'s **values** off a cone.
- **Construction #3 (clean up `F` on a small set) — same wall.** Modifying `F` on a cone-null/measure-zero
  set to force uniformity is exactly "alter values," which #1's verdict says is the *only* place progress can
  come from — but there is no handle: the fibers are cone-null but (jump!) uncountable, and no canonical
  value-selection is available without already solving the uniformity question. Not machine-checked (it is
  the open content), but sharply localized by #1: reparametrization is useless, so #3 is where the difficulty
  actually is, and it is the same difficulty as the conjecture.
- **Construction #2 (uniformize the reduction via a game / Martin measure) — the honest obstruction, verified
  against the e-degree counterexample.** The standard determinacy proof of Part I *needs* the uniformity
  function `u` at the step where it feeds a *single* index (valid on a cone) into the Martin-measure/pressing-
  down argument; a *bare* reduction-index `ι(x)` for `Fx ≤ᵀ Fy` that depends on the real `x` (not just its
  degree) cannot be fed in, because the measure sees only degrees. A "uniformity game" that tries to *select*
  `ι` uniformly is exactly what fails: Nakid-Cordero's **e-degree counterexample** (Thm 6.5, Kalimullin pairs)
  is a *definable* invariant function whose non-uniformity is an **asymmetry** — "determining `0∈A` needs
  positive information not recoverable symmetrically from the indices witnessing `A≡B`". That asymmetry is
  possible **because the e-degrees lack a cone theorem**; the Turing cone theorem is precisely the extra
  structure a Turing proof must exploit (and the game cannot manufacture it). Verdict: no elementary game
  circumvents this — it is the crux, and it is Turing-cone-specific.
- **Construction #4 (injective-on-pointed-tree ⟹ uniform?) — NO, but instructive.** By Lutz–Siskind Lemma 2.1
  (`g` computable+injective on perfect `T` ⟹ `g(x)⊕T ≥ᵀ x`), injectivity on a *pointed* tree gives
  `Fx ≥ᵀ x` on a cone (above-identity), i.e. it discharges the *Part-I dichotomy value*, **not uniformity**.
  Injectivity is a statement about `F`'s graph on one tree; uniformity is about transforming *index witnesses*
  across *all* equivalences. A function can be injective on a pointed tree yet have `u` fail off that tree.
  So Marks's conjecture routes to *above-identity / RK-minimality* (the strict half), **not** to Steel 9.4.
  These are genuinely different targets; #4 conflates them.
- **Construction #5 (novel devices).** The one structural fact that survives: the e-degree analogue of Steel
  9.4 is **FALSE** (Nakid-Cordero), and the *sole* named reason is the **cone theorem** (Turing has it,
  e-degrees don't) + **no Kalimullin pairs in the Turing degrees**. So any correct Turing construction must
  be **cone-theorem-driven** and must break where Kalimullin asymmetry lives. This is a real design
  constraint, and it points back to the measure route (the cone theorem = the Martin measure), consistent
  with the memory's frontier: Steel 9.4 is not easier than MC — its Borel form is *equivalent* to Borel MC.

**Net:** Steel 9.4 is a genuine reframing but **not a shortcut**. The canonical-representative family (#1,#3-input-
side, #4) is machine-checked or argued to be uniformity-neutral or off-target; the live content (#2/#3-value-side)
is the same Turing-cone-specific asymmetry the measure and Marks routes already bottom out at. New machine-checked
lemmas: `EquivVia.trans_trE`, `uniform_precomp_of_uniform`, `uniform_of_uniform_precomp_section`,
`canonicalRepresentative_no_gain`.

### Session 2026-08-26b — the strict/equivalence halves in dominated-invertibility language
> **⚠️ READ THE MACHINE-CHECKED CORRECTION BULLET BELOW FIRST.** The correct degree-level framing is the
> **dominated-invertibility** organization (`MartinStrictHalf.lean`): Part 1 = (Q3) non-constant ⟹ DI ∧
> (Q4) DI ⟹ MP; disproof targets `¬DI` (Q3) and *DI-incomparable* `F` (Q4); `incomparable_violates_a_half`.
> The "pointed-injectivity / uncountable-fiber / pointed-Silver" bullets that follow are the *research trail*
> and contain two errors (jump is bounded-fibered; no clean single-fiber characterization) — kept for the
> record, superseded by the correction bullet.

**→ `MARTIN_PART1_STRICT_MARKS.md` + memory `marks-pointed-injectivity.md`.** A combinatorial handle on the
STRICT half (U_M RK-minimal), complementary to the measure route. Marks's conjecture (every f constant OR
injective on a POINTED perfect tree) ⟹ strict half (Lutz thesis Prop 5.37). Sharpening this session:
- **Marks-for-invariant-f is ALREADY PROVED when fibers are COUNTABLE** — Marks–Slaman–Steel Thm 3.6 route
  (verified from ar5iv 1109.1875): **Lusin–Novikov** (Kechris 18.10, needs countable sections) splits into
  countably many injective Borel pieces; **Martin's pointed-tree Lemma 3.5** lands a pointed set in one piece.
- **So the SOLE open content of Marks-for-invariant-f is UNCOUNTABLE fibers** (MSS explicitly restrict to
  countable Borel equiv rels; Silver's dichotomy "receives no mention"). A non-constant invariant f has
  cone-null fibers, but cone-null ≠ countable (the jump has uncountable fibers in every cone).
- **Exact open step (localized this session):** Silver's dichotomy (Thm 21.1, holds ∀f under AD) gives f
  injective on a *perfect* set P even for uncountable fibers; the ONLY gap is making P **pointed**. The
  collision: Groszek–Slaman pointed-coding (Lutz Thm 2.18/2.19) forces branch *positions* (to code the tree
  into left/right turns), while Silver injectivity needs *freedom* to steer f-values apart. Compatibility of
  these two for uncountable cone-null fibers = the open crux. No literature theorem does this.
- **Sharpest concrete test case:** *is the Turing jump injective on a pointed perfect tree?* (jump = the
  canonical non-constant, non-injective-on-any-cone invariant; a NO would disprove Marks; separated by a thin
  pointed tree it could be YES). This is a decidable-looking sub-question, unlike the inner-model wall.
- **MACHINE-CHECKED framework (`MartinStrictHalf.lean` + `MeasurePreservingCK.lean`, std axioms, green):** both
  Lutz–Siskind open questions now have a "proved fragment + open residue" structure.
  **Q3 (strict):** `strictHalf_iff_dominatedInvertible` (strict half ⟺ `DominatedInvertible F`);
  `PointedInjectiveTree F ⟹ DominatedInvertible` (explicit `g y = y⊕code`; `recover` = Lemma-2.1
  domination-recovery, mirrors `InvertingTree`); **`strictHalf_of_countableFibered`** = countable-fiber
  fragment PROVED (named `CountableFiberMarks` = MSS Thm 3.6); soundness `pointedInjectiveTree_id`.
  **Q4 (equivalence):** `EquivHalfFor`; **`equivHalf_of_rangeInKernel`** = concentrated fragment PROVED
  (named `Prop524`); `gcomp_mp_recovers` = the g-inversion stall. **`partI_of_halves`**: both halves ⟹ Part 1
  (= Thm 5.15). Q4 residue = inner-model (Siskind ultrapower).
- **⚠️ CORRECTION (machine-checked, supersedes the "uncountable fibers / pointed-Silver" bullets above):** the
  degree-level strict half is `DominatedInvertible F` (∃ inv `g`, `X ≤ᵀ g(F X)` on a cone), NOT reals-injectivity.
  (i) **The claim "the jump has uncountable fibers" is FALSE** — the jump, like any increasing `F`, is
  *bounded*-fibered (`{d : d' ≡ᵀ c} ⊆ {d ≤ᵀ c}`, countable), and is trivially DI (`g = id`). (ii)
  `dominatedInvertible_fiber_bounded`: DI bounds every fiber *on the DI-cone* — but only there, NOT globally
  (`F d = if d ⊥ 0' then 0' else d` has a globally-unbounded fiber `{d ⊥ 0'}` yet is the identity on `cone(0')`,
  hence DI). So there is **no clean single-fiber / uncountable-fiber characterization**, and the "make Silver's
  perfect set pointed" framing targets *reals*-injectivity, which is not what the degree-level strict half needs.
  (iii) **The honest open Q3 = "is every non-constant invariant `F` dominated-invertible?"**; the disproof
  target is `¬DominatedInvertible` (`partI_false_of_not_dominatedInvertible`); countable-fibered ⟹ DI (MSS,
  sufficient not necessary). The jump-injectivity "test case" is trivial (jump is reals-injective: `x ≤ᵀ x'`).

### Session 2026-08-26 — the Church–Kleene characterization of Part 1 + convergent frontier
**→ `MeasurePreservingCK.lean` (9 theorems, machine-checked, standard axioms) + `MARTIN_PART1_RK_MEASURE.md`.**
The measure-theoretic attack on `escaping ⟹ MP` (= `U_M` RK-rigidity), via the relativized Church–Kleene
ordinal `ω₁ˣ`. Since `MP ⟹ above-id` (Thm 3.4) and `ω₁ˣ` is monotone:
- **`measurePreserving_ck_nondecreasing`**: MP ⟹ `ω₁ˣ ≤ ω₁^{F X}` on a cone.
- **`ck_trichotomy`**: every invariant `F` is CK-regressive / CK-preserving / CK-increasing on a cone.
- **`partI_false_of_ckRegressive_escaping`** (headline): an escaping (≡ non-constant) `F` that **lowers `ω₁ˣ`
  on a cone would REFUTE Part 1** — a concrete disproof target.
- **`partI_iff_ck_split`** (capstone): Part 1 ⟺ [(no escaping CK-regressive `F`) ∧ (every escaping
  CK-non-decreasing `F` is MP)] — the open content partitioned exactly by `ω₁^{F X}` vs `ω₁ˣ`.
- The CK-position **IS** the Slaman–Steel/Lutz stratification (via the graph's Part-2 rank, no coordinated
  trees): CK-preserving escaping = `F X ≤_h X` = **Lutz's `D_h` territory** (closed mod Part-2-for-graph);
  **CK-increasing escaping = the sharpest open residue (ω₁-level)**.
- Honest scope: a genuine machine-checked *characterization/localization*, NOT a solve; both split-branches
  need degree-level (inner-model) info. The `g`-inversion trace (note) shows why RK-minimality is
  insufficient — Lutz–Siskind's "rigidity > RK-minimal", at mechanism level.

**Convergent frontier (three parallel deep-dives + own analysis, all agree — `ATTACK.md` B13/B14 + "SESSION
2026-08-26 DISPROOF"):** the incomparable core is stuck **symmetrically** — construction ≡ disproof ≡
negation-of-proof are **one object** = "`U_M` has a nonprincipal RK-predecessor ≠ itself" = **Marks's
pointed-perfect-tree conjecture fails at `U_M`**. (i) ZFC counterexample (Lutz Thm 5.27) dies under AD at
exactly the `ω₁↪ℝ` ingredient the proof needs; every AD construction tool (Uniformization_ℝ, scales,
Posner–Robinson complements, ultrapower) yields a definable-but-not-invariant selector (no invariant/OD P–R
complement is known). (ii) The e-degree counterexample (Nakid-Cordero) is **uniform** — bears only on the
KNOWN uniform Turing case; enabled by `D_e` lacking a cone theorem. (iii) CBER/superrigidity provably can't
reach it (MC ⊥ measure theory; tools see `≡_T` but not the `≤_T` order). **Net: RK-rigidity of `U_M` is the
sole live route; concrete named target = Marks's conjecture.**

### Session 2026-08-25 — GENUINE ATTACK on the open core (not bookkeeping)
**→ Entry point: `MARTIN_ATTACK_SUMMARY.md`** (1-page honest summary: the 5 approaches tried, coordinated
trees ruled out as circular, the frontier `escaping⟹MP` = `U_M` RK-rigidity validated verbatim against
Lutz–Siskind arXiv:2305.19646, and the next-attempt lead). Full detail in `MARTIN_PART1_APPROACH_OMEGA1.md`
(ω₁ no-go + unified obstruction) and `MARTIN_PART1_STRUCTURAL_AM.md` (Theorem A + measure route §7–11).
- **`MartinOmega1Approach.lean`**: reframe `IncomparableConstant ⟺ NoIncomparableSelfMap` (no invariant
  `F` has `F X ⊥ᵀ X` on a cone); the **graph-orbit device** `graphOrbit_strictMono` (iterate `X⊕F X`,
  choice-free strict increase on cone). The ω₁-chain approach it points to is a **provable no-go**
  (limit stages need `ω₁↪ℝ`, which AD forbids); Fodor-on-`ω₁ˣ` dies identically → unified obstruction:
  lifting per-degree info to ω₁-level needs a Turing code (Am region has none) or choice (AD-forbidden).
  Full writeup `MARTIN_PART1_APPROACH_OMEGA1.md`. Also `incomparable_jump_not_below` (`X≰ᵀF X ⟹ X'≰ᵀF X`).
- **`LevelCoordinatedTree.lean`** + `MARTIN_PART1_STRUCTURAL_AM.md`: the structural/∞-Borel route.
  **Theorem A** (math): Borel invariant `F` of Baire rank ρ has `F X ≤ᵀ X^(ρ)`, ρ **fixed** ⟹ Borel `Am`
  is a *transfinite `Bm`* at fixed level (Lutz's rank-unboundedness is **∞-Borel-specific**, not Borel).
  `level_of_cores` unifies finite `Bm` (`L=jump^[k]`) + Borel `Am` (`L=X^(ρ)`) at any invariant increasing
  level `L`. **Sharpened crux**: for Borel `F` the coordinated tree is dischargeable (Theorem A gives the
  code uniformly=NO good-rep barrier; Silver gives injectivity), so Borel `Am` collapses to the
  **domination step** — and the *uniform* half of domination is **provably impossible** for incomparable `F`
  (`incomparable_jump_not_below`); only *per-function* domination survives = the exact recursion-theoretic
  open crux. Caveat verified: Theorem A is type-A uniformity (`F X=Φ_e^{X^(ρ)}`) NOT type-B uniform
  invariance (`F X≤ᵀF Y` fails), so it does NOT solve Borel Part 1.

### Session 2026-08-25 additions (autonomous run — earlier structural bookkeeping)
- **`MartinGameCode.lean` + `GameCapstone.lean`** (prior session, verified): `GameCodeBelow`
  (`codeGame σ ≤ᵀ σ`) PROVED ⟹ **`MartinPPT` (Martin's Lemma 2.3) is a theorem modulo determinacy**
  (`martinPPT_of_gameDeterminacy`); hence Thm 3.4, Part 1 ⟺ escaping⟹MP, and order-preserving Part 1
  all rest on determinacy (+ at most one named lemma).
- **`MeasurePreservingFilter.lean`**: MP/escaping/above-id/constant and Part 1 itself as
  Martin-measure-pushforward (ultrafilter/Rudin–Keisler) statements; `RKle` + `pushCone_rkle_id` (the
  RK order on pushforwards is trivial — why RK-descent cannot prove Part 1).
- **`GraphFunction.lean`**: the graph `X ↦ X ⊕ F X = id ⊔ F`; the Martin order is an upper semilattice
  (`martinJoin_le`); precise reason MartinPPT cannot grip a counterexample.
- **`OrderPreservingCore.lean`**: `uncountableCofinal_iff_avoiding` — the order-preserving branch rests
  on **exactly one** open coding lemma (its two named hypotheses are equivalent).
- **`PosnerRobinson.lean`**: Posner–Robinson via the direct `G := jReal A` construction — the full
  theorem `posnerRobinsonFull (A) (h : ReadBack A) : ∃ G, A ⊕ G ≡ᵀ G'` bracketed by an explicit
  `ReadBack` Prop, with `readBack_iff` (bracket = exactly the hard read-back reduction), the cone case
  `A ≥ᵀ 0'` as a corollary, and `not_readBack_of_computable` (the gap provably FAILS for computable `A` —
  machine-checking it is a genuine obstruction, not accidentally provable).
- **`IncomparableArithReduction.lean`**: **a finer classification of Part 1's sole open content** —
  `partI_of_three_cases_and_arith`: Part 1 ⟸ `RegressiveSlamanSteel` (known) + `StrictArithRegressiveConstant`
  (the arithmetic-degrees regressive theorem, discharging the `AnBm` jump-distance sub-case) + three
  arithmetically-typed sub-cases (`AnAm`/`BnAm`/`BnBm`). Honest: a structural sharpening (one sub-case
  identified with a recognized open theorem), not a crossing. Also: `incomparableConstant_iff_four_subcases`
  (the four-way split is LOSSLESS) and `incomparable_not_below_argJoin` (a counterexample value escapes
  `X⊕Z` for every fixed `Z` — sharper than escaping).
> ⚠️ **The coordinated-tree material below (ArithRegressiveSkeleton / BnBmSkeleton / LevelCoordinatedTree,
> and the "four-face map reduces the core to coordinated trees" framing) is SUPERSEDED by the genuine-attack
> section above and `MARTIN_PART1_STRUCTURAL_AM.md` §2.6: the coordinated-tree method is CIRCULAR for the
> incomparable core (its domination bracket ≡ the core). The files are honest (brackets open) but are NOT a
> viable route. The viable route is measure-theoretic (`escaping⟹MP`). Keep the below as record, not as a plan.**
- **`ArithRegressiveSkeleton.lean`**: `StrictArithRegressiveConstant` (the `AnBm` target) opened into its
  three *relativized* Slaman–Steel steps (tree / domination / coding relative to `X^(k)`); assembly PROVED,
  including the AnBm twist that step-3's `x ≤ᵀ F x` on a branch is a *contradiction* (vs the Turing case's
  "above identity"), the three steps bracketed.
- **`BnAmPartTwo.lean` + `OpenContentCapstone.lean`**: **the incomparable core has a COHERENT FOUR-FACE MAP.**
  For `G X := jump^[k](F X)` (invariant, above-id on the `Bn` cone): `bnAm_jumpComp_not_finite_jump` —
  `BnAm` forces `G` to *infinite* Part-2 rank (a structural leak into Part 2, not a reduction);
  `bnBm_jumpComp_finite_bounded` — `BnBm`
  keeps `G` at *finite* rank (`X ≤ᵀ G X ≤ᵀ X^(k+m)`). So the `Am`/`Bm` split (`F X ≰ₐ X` vs `F X ≤ₐ X`) IS
  the infinite/finite Part-2-rank split. Two of the four faces are the two known Martin regimes (AnBm=Part-1-regressive,
  BnAm=Part-2-increasing).
  `escapingMP_of_three_cases_and_arith` ports the decomposition to the canonical `escaping⟹MP` phrasing.
  The leak is abstracted to `am_not_finite_jump_of_increasing` (it uses *only* that the operator is
  increasing, `A ≤ᵀ op A`) — the precise property the enumeration-degree *skip* lacks, machine-connecting
  the analysis to Nakid-Cordero's e-degree contrast (arXiv:2510.19147; `ATTACK.md` B9+). Primary packaging
  `partI_of_arith_bnBm_escaping`: Part 1 ⟸ known SS + arith-regressive theorem + `ArithEscapingHalf` (Am,
  Part-2-flavoured) + `SubcaseBnBm`.
- **`BnBmSkeleton.lean`**: **`BnBm` reduces to the SAME relativized Slaman–Steel skeleton as `AnBm`**
  (`bnBm_of_cores`, machine-checked): the coordinated tree computing `F` from `x^(k)`, step-3's `x ≤ᵀ F x`
  on branches contradicting *incomparability* (branches on the incomp cone) exactly as `AnBm`'s contradicts
  arith-strictness. So the whole `Bm` region (`AnBm ∪ BnBm`) is uniformly relativized-S-S coordinated-tree
  brackets; the genuine CBER difficulty is concentrated in `BnBm`'s step-1 (`HasBnBmUniformTree`, an
  arith-*preserving* injective uniformization) — a distinct, plausibly harder bracket, NOT a separate
  method. `arithBelowHalf_of_bnBm_cores`: `ArithBelowHalf` ⟸ the `AnBm` + `BnBm` step-1 brackets.
  (Honest correction to earlier framing: `BnBm` is not "native to neither regime" — it is the
  incomparable-core instance of the Part-1 coordinated-tree method.)
- **`RegressiveSkeleton.lean`**: the KNOWN Slaman–Steel regressive theorem opened into its three steps
  (coordinated tree / branch domination / branch coding); assembly + downstream PROVED
  (`regressiveSlamanSteel_of_cores`, `regressiveImpliesConstant_of_cores`), the two hard steps bracketed.
- **`PartIIUniform.lean`**: **Part 2 opened for the uniform class** (previously untouched — Part 2 was
  proven for no class). `UniformRegular` + the Steel jump-chain inside it; assembly + exactness both ways
  (`partIIUniform_iff_cores`: uniform Part 2 ⟺ its three cores); comparison trichotomy + successor
  provable half proved; the three cores (comparison/well-foundedness/jump-minimality) bracketed.
- Extensive `ATTACK.md` original-research log: every fresh angle on the incomparable core funnels to the
  same barrier; sharpest new proof-level localization = the S-S *domination* step needs `x ≥ᵀ f x`, which
  incomparability denies. No crossing (expected). 82 files, full build green, all std axioms.

---

## The conjecture, and exactly what is open

**Part 1** (`ConstantOnCone F ∨ AboveIdOnCone F` for Turing-invariant `F`) reduces, provably
and losslessly, to two cores (`CoreAnalysis.partI_iff_cores`):
- `RegressiveImpliesConstant` — `F X <ᵀ X` on a cone ⟹ constant on a cone;
- `IncomparableImpliesConstant` — `F X ⊥ᵀ X` on a cone ⟹ constant on a cone.

**⚠️ CORRECTION (2026-08-23): the regressive core is NOT open — it is a KNOWN Slaman–Steel theorem.**
Slaman–Steel proved Part 1 for *all* regressive functions on the Turing degrees (Lutz–Siskind Thm 1.4:
`f(x) ≤ᵀ x ⟹ f` constant or `f(x) ≡ᵀ x` on a cone).  So `RegressiveImpliesConstant` follows outright
(`regressiveImpliesConstant_of_slamanSteel`, from `RegressiveSlamanSteel`).  The **sole genuinely-open
content of Part 1 is the incomparable core** (`IncomparableImpliesConstant`, functions "off to the
side").  Definitive statement: `partI_open_content_TFAE` — Part 1 ⟺ incomparable core ⟺ (escaping⟹MP)
⟺ (no escaping `F` incomparable to a fixed degree) are all equivalent, i.e. **one** open problem.
Earlier sections of this file (and the ω₁^x work below) mislabeled the *Turing* regressive core
as open, conflating it with Lutz's *hyperarithmetic-degrees* regressive result (`arXiv:2306.05746`, a
different degree structure); read them with that correction in mind.  Both cores additionally hold for
**uniformly**-invariant `F` (`partI_uniform`) and **degree-bounded** `F` (`bounded_implies_constant`).

**The two orthogonal inputs Part 1 rests on** (both determinacy theorems; the class-specific
one is the open one):

1. **Determinacy input** — `MartinDichotomy` (≡ `MartinPPT`, `martinPPT_iff_dichotomy`): every
   set contains a pointed perfect tree or its complement contains a cone. Its **invariant case
   is proved** (`perfectDichotomy_invariant`); a cone is *unconditionally* a full pointed
   perfect tree with the effective `recover` field (`cone_contains_PPT`).
   **The non-invariant case (Martin's Lemma 2.3 / "Martin's fusion") — its mathematical content
   is now MACHINE-CHECKED** (`MartinGame.lean`, 2026-08-23). The correct proof (Marks–Slaman–Steel
   Lemma 3.5) uses the *asymmetric* game — I plays `x`, II plays `y`, II loses unless `y ≥ᵀ x`, else
   I wins iff `x ≥ᵀ y ∧ x ∈ A`. Proved: `winsI_martinGame_of_cofinal` (cofinal ⟹ player I wins),
   `cofinal_realizes_cone`, and `martinGamePerfectEmbedding`/`cofinal_perfectEmbedding` (the pointed
   perfect embedding into `A` — the "game half" `PerfectEmbedding.lean` flagged as the sole gap).
   `MartinGameFusion.lean`/`MartinGameTree.lean` reduce the **whole** non-invariant case to a single
   computability fact `GameCodeBelow` (`codeGame σ ≤ᵀ σ`). **✅ That fact is now PROVED**
   (`MartinGameCode.gameCodeBelow`, 2026-08-23): `embVal_le` presents the game embedding as recursive-in-`σ`
   (primitive recursion on histories via `Nat.RecursiveIn.prec`), wrapped in the graph-prefix+`Primrec`
   pattern of `codeReal_le`. **So `MartinPPT` (Martin's Lemma 2.3) is now a THEOREM modulo only determinacy**:
   `martinPPT_of_gameDeterminacy` (`MartinGameCode.lean`). Downstream, everything that assumed `MartinPPT`
   is now dischargeable from determinacy — `GameCapstone.lean`: `measurePreservingAboveId_of_gameDeterminacy`
   (Lutz–Siskind **Theorem 3.4 from determinacy alone**), `partI_of_gameDeterminacy_escaping`,
   `partI_iff_escapingMP_of_gameDeterminacy` (**Part 1 ⟺ escaping⟹MP on determinacy alone**),
   `partI_iff_pushforward_of_gameDeterminacy`. All standard axioms only. Nothing here is a hypothesis
   anymore except determinacy itself; the open content is the incomparable core (input 2 below).

2. **Class-specific input** — `escaping ⟹ MP` (`escapingMP_iff_no_fixedIncomparable`,
   `EscapingDichotomy.lean`): equivalent to "no escaping invariant `F` is Turing-incomparable
   to a fixed degree on a cone." **This is the actual open problem.** See `ATTACK.md`.

`partI_of_dichotomy_noFixedIncomparable` (`PartIRecast.lean`) is the sharpest packaging:
Part 1 ⟸ (1) + (2).

**Cleanest corrected statements of the open content** (2026-08-23, given the KNOWN regressive theorem
`RegressiveSlamanSteel` and `MartinPPT`): `partI_iff_incomparable` — Part 1 ⟺ the incomparable core;
`escapingMP_iff_incomparable` — `escaping ⟹ MP` ⟺ the incomparable core; `partI_iff_escapingMP` — the
chain, so **all three coincide**.  There is genuinely *one* open problem (the incomparable core =
`escaping ⟹ MP`), the regressive core being a Slaman–Steel theorem.

**Cleanest single-hypothesis form** (`partI_general_of_uniformity`, `MartinResults.lean`): full
Part 1 ⟸ the *one* implication "`TuringInvariant F ⟹ UniformlyTuringInvariant F` (on a cone)" —
a **sufficient** condition (the intended route to the Borel case — though `Borel ⟹ uniform` is itself
**open**, ≈ Steel's conjecture; not necessary, since Part 1 doesn't imply uniformity). Everything
downstream is machine-checked; `ATTACK.md` analyses exactly why determinacy does not deliver this bridge
for `F` (cone dichotomy vs cone uniformization).

**Sharpened to Steel's conjecture** (`partI_general_of_steelBridge`, `MartinResults.lean`): full Part 1
⟸ "every `TuringInvariant F` is `MartinEquiv` (cone-`≡ᵀ`) to *some* uniformly-invariant `G`" — which is
**exactly Steel's conjecture** ("every definable Turing-degree function is equivalent to a uniformly
invariant one"), the literature's canonical reduction target. This *generalizes* the uniformity-bridge
form (take `G := F`). The contrapositive `counterexample_refutes_steel` shows a Part-1 counterexample
refutes Steel's conjecture. Grounding: Nakid-Cordero 2025 (arXiv:2510.19147) prove the bridge *fails* in
the enumeration degrees — so it is genuinely Turing-specific, not pure logic.

---

## What is machine-checked (headline map)

**Recursion-theory foundation** (`OracleCode.*`, `Cantor.*`, `Universal.lean`, `Jump.lean`):
oracle enumeration theorem, the step-indexed universal machine `evaln` + `evaln_prim`, the
relativized Kleene recursion theorem (`exists_fixedPoint`), s-m-n/padding, Σ₁-completeness of
the jump, Shoenfield limit lemma, jump strictness `X <ᵀ X′` and its degree-invariance.

**Kleene–Post** (`KleenePost.lean`, `EffectiveKP.lean`): incomparable degrees exist, and the
effective version `∅ <ᵀ A <ᵀ 0′`.

**Cone theorem / Martin measure** (`ConeTheorem.lean`, `MartinMeasure.lean`, `ConeFilter.lean`):
`cone_theorem` (dichotomy from `GameDetermined`), the σ-pigeonhole `exists_onCone_of_cover`,
and the measure packaged as a first-class Mathlib `Filter` — `coneFilter`, proper + countably
complete (`CountableInterFilter`), ultrafilter on invariant sets (`coneFilter_dichotomy`),
and `pushCone_dichotomy`/`pushCone_comp`/`pushCone_id`/`pushCone_const` (the invariant
pushforward `F ↦ F_*U` is a monoid action; carries `id ↦ U`, `const ↦ principal`).

**Lachlan's theorem, globalized** (`LachlanTheorem.lean`): for a computably-uniformly-invariant
r.e. operator above id on a cone, `Wˣ ≡ᵀ X` or `Wˣ ≡ᵀ X′` on a cone (both cases built:
`ContinuousCase.lean`, `DiscontinuousCase.lean`, `CodingFamily*.lean`).

**Bard's Lemma 3.4** (`BardUniformity.lean`, `MartinResults.lean`): `uti_computable`
(uniform ⟹ computably-uniform), unlocking `partI_uniform` and both cores for the uniform class.
`partI_uniform_general` (the `Measurable`-free uniform Part I) and the capstones
`partI_Borel_of_uniformity_bridge` / `partI_general_of_uniformity`: the bridge
"Turing-invariant ⟹ uniformly Turing-invariant" is a **sufficient condition** for Part I
(everything downstream is machine-checked) — the intended route to the Borel case, **but the bridge is
open even for Borel** (Part 1 for general Borel is open; ≈ Steel's conjecture). It is sufficient, *not*
necessary (constant/above-id functions needn't be uniform), and its truth for `F` is itself open. `escapingMP_of_uniformity_bridge`: the bridge subsumes the
`escaping ⟹ MP` route. (Why determinacy doesn't deliver the bridge: `ATTACK.md`.)

**Measure-preserving reduction** (`MeasurePreserving.lean`, `PointedTree.lean`, `MartinTree.lean`,
`RawPPT.lean`, `PerfectEmbedding.lean`): Theorem 3.4 ⟸ `GroszekSlaman` ⟸ `MartinPPT`, with
`recover` (Lutz–Siskind Lemma 2.1 = `lemma21`) and `realizes` (Prop 1.10 =
`realizes_of_perfectEmbedding`) both **proved as theorems**, not assumed.

**Pointed perfect trees, invariant case fully built** (`ConeTree.lean`, `ConeRawPPT.lean`):
`invariant_cofinal_contains_PPT` — a Turing-invariant cofinal determined set contains a full
`PPT`, via `codeReal_equiv` (`codeReal Y ≡ᵀ Y`, a two-direction `RecursiveIn` reduction).

**Regressive-core decomposition** (`RegressiveJumpDecomp.lean`): `regressive_jump_dichotomy` — a
new jump-distance σ-pigeonhole (each degree has countably many predecessors) splits the open
regressive core into **Case B** (`X ≤ᵀ (F X)^(k)`: `F` preserves the arithmetic degree, finitary)
or **Case A** (`X ≰ᵀ (F X)^(n)` ∀n: Lutz's `ω₁^x` hyperarithmetic regime). Packaged as a core-reduction
`regressiveCore_of_cases`. Pinpoints the obstruction as the lack of a well-founded rank on the Turing
degrees; see `ATTACK.md`.

**The Fodor engine** (`OrdinalUltrapower.lean`): `no_descending_ordinal_cone` — the cone measure's
ordinal ultrapower is well-founded (countable completeness ⟹ no infinite `≺`-descending sequence of
ordinal-valued functions on cones). `no_regressive_of_ordinal_rank`: the regressive core follows from
a degree-invariant ordinal rank a regressive `F` strictly decreases. This isolates the *sole* missing
ingredient — the rank `ω₁^x`.

**The Church–Kleene ordinal `ω₁^x`** (`ChurchKleene.lean`): `churchKleene` (relativized `ω₁^X` = sup of
order types of `X`-computable well-orders, correctly guarded `≤ᵀ X`), with `churchKleene_mono` +
`churchKleene_invariant` + `omega_le_churchKleene` (`ω₁^X ≥ ω`, non-degeneracy — the rank is not
trivially `0`, so the engine constraint is non-vacuous) proven. Instantiating the engine:
`no_omega1_decreasing_conePreserving` (no cone-preserving regressive `F` strictly decreases `ω₁^x`) and
`regressive_omega1_dichotomy` (a regressive `F` preserves or strictly decreases `ω₁^x` on a cone). So a
cone-preserving counterexample is **`ω₁`-preserving**. **Sharper framing** (see `ATTACK.md`): the engine
*already* kills the `ω₁`-**decreasing** case (= `F X <_h X`, which is *all* of Lutz's `D_h` regressive
setting) via ordinal well-foundedness — no `Σ¹₁`-bounding. So the genuine open residual is the
`ω₁`-**preserving** = **hyp-preserving Turing case** (`F X ≡_h X`, `F X <ᵀ X`), a Turing-specific
phenomenon *vacuous* on `D_h` (Lutz never sees it), with no ordinal rank (the Turing degrees inside one
hyperarithmetic degree are ill-founded).

New constraints (`CounterexampleConstraints.lean`): `arithmetically_bounded_implies_constant`
(counterexample is *arithmetically* escaping), `nonconstant_above_or_incomparable_fixed` (per-degree
trap). Both open cores are reduced to jump-distance sub-cores (`regressiveCore_of_cases`,
`incomparableCore_of_cases`).

**Order-preserving case, reduced to the coding step** (`CounterexampleConstraints.lean`, following
Lutz–Siskind §4).  `partI_orderPreserving_of_coding`: Part 1 for *every* order-preserving `F` follows
from `MartinPPT` (⟹ Thm 3.4) plus the single atomic `OrderPreservingUncountableCofinal` — the
Groszek–Slaman–Kihara perfect-set coding (Cor 4.5).  The elementary pieces are all **proved**:
`nonconstant_values_uncountable` (Case 1: countable range ⟹ constant), `orderPreserving_mp_of_rangeCofinal`
(cofinal ⟹ MP), `orderPreserving_range_countablyDirected` (§4.2 directedness, via the reusable
`Cantor.component_le_joinFam`).  Chain: `avoidingImpliesConstant_of_theorem46` ⟶
`orderPreservingNonconstantMP_of_uncountableCofinal` ⟶ `partI_orderPreserving_of_theorem46`.  So the
sole remaining unformalized ingredient of the order-preserving case is the coding.

**Counterexample constraints** (`EscapingDichotomy.lean`, `PartIRecast.lean`,
`CounterexampleConstraints.lean`): machine-checked profile of any Part-1 counterexample —
`nonMP_incomparable_cone`/`_interval` (incomparable to a whole cone of fixed degrees, uniform
over each countable interval), `nonMP_kernel_avoids_cone` (kernel ideal is proper),
`nonconstant_values_uncountable`, `counterexample_full_profile`,
`incomparable_case_doubly_incomparable`, and `regressive_conePreserving_descending_chain`.
The precise barrier (no Turing-code extraction from a non-definable invariant `F`) and all
construction probes are logged in `ATTACK.md`.

---

## Reusable engineering notes (Lean/Mathlib gotchas)

- **`PFun` is not reducible.** `simp`/`rw` refuse to act on `Part.some x >>= f` for variable
  `f : ℕ →. ℕ`. Workarounds: state things with `f : ℕ → Part ℕ`; use the `mem_eval_*`
  characterizations in `OracleCode.lean`; `show _ = _ from Part.bind_some _ _` casts.
- **`Nat.rec_add_one` won't fire** on `Nat.rec` with `Part ℕ` motive via `rw`/`simp`; use
  `show (Nat.rec (motive := fun _ => Part ℕ) _ _ m).bind _ = _` to expose iota reduction.
- **`rw` under `have`-binders fails** when the target is in the binder's proof term; `simp only`
  often succeeds where `rw` fails.
- **`Primrec.list_rec` step arg needs `.to₂`.** Deep/nested `list_foldr_prim` blows up `whnf`:
  pass all implicits explicitly `(f := ..)(base := ..)(op := ..)` and
  `set_option maxHeartbeats 8000000 in`. Use `cond b 1 0` (not `if b then`) to match `list_rec`.
- **Search-over-`allBoolLists` + oracle-prefix pattern** (`existsOK_prim`/`consb_prim` in
  `EffectiveTreeReduction.lean`): `list_foldr_prim` + `foldr_or_mem`/`foldr_and_mem`; read the
  oracle via `graphEnc`/`graphEnc_recursiveIn`; bridge `==` to `Primrec.eq.decide` with
  `beq_eq_decide` (`primrec_beq`). This is the template for any effective-reduction build.
- **`Cantor.le_iff_bitg`** turns `X ≤ᵀ Y` into a `RecursiveIn {toPFun Y}` goal about `bitg X`.
- `if_pos`/`if_neg` are deprecated in current Mathlib (warnings only).
