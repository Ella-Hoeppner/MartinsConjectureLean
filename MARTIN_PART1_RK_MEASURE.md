# The measure-theoretic attack on the RK-rigidity frontier — development and precise limits

*Attacking `escaping ⟹ MP` (≡ `U_M` has no nonprincipal RK-predecessor but itself, Lutz–Siskind
arXiv:2305.19646) **measure-theoretically**, this session. A genuine partial handle (machine-checked) plus a
precise map of why the elementary/ordinal measure tools stop short of the degree-level crux. Not a solve.*

## The measure-theoretic scaffolding (already in the repo, plus this session's addition)
Write `U_M` for the Martin (cone) measure. For invariant `F`:
- **Kernel** `BelowF F Z := (Z ≤ᵀ F X on a cone)` — the degrees `F` eventually dominates. It is a **Turing
  ideal** (`belowF_downward`, `belowF_join`: downward- and finite-join-closed). *Correction to a prior note:
  it is NOT countably-join-closed — a countable join `⊕Zₙ ≤ᵀ F X` needs the reductions `Zₙ ≤ᵀ F X` uniform in
  `n`, which "F X computes each `Zₙ`" does not give.*
- `MP ⟺ ∀Z, BelowF F Z` (`mp_iff_belowF_univ`) — MP means the kernel is everything.
- **`MP ⟺ kernel cofinal`** (`mp_iff_belowF_cofinal`): since the kernel is downward-closed, cofinal ⟹ = all.
  Contrapositive: **a ¬MP `F` has a *non-cofinal* kernel** — some `W₀` bounds it from above.
- `MP ⟺ above-id` (`mp_iff_aboveId_of_martinPPT`, = Groszek–Slaman Thm 3.4).

## This session's contribution: the Church–Kleene constraint (machine-checked, `MeasurePreservingCK.lean`)
Since `MP ⟹ above-id` and `ω₁ˣ` is monotone (`churchKleene_mono`):
- **`measurePreserving_ck_nondecreasing`**: `MP F ⟹ ω₁ˣ ≤ ω₁^{F X}` on a cone (MP never lowers the CK ordinal).
- **`ck_regressive_not_measurePreserving`**: if `ω₁^{F X} < ω₁ˣ` on a cone (`F` is *CK-regressive*), then `F`
  is **not** MP. So an *escaping* CK-regressive `F` is a genuine counterexample-candidate to `escaping ⟹ MP`.

*Why this is choice-free (correcting a prior over-statement that "Fodor is fully blocked"):* `ω₁ˣ` is
`≡ᵀ`-invariant (`churchKleene_invariant`), so comparing `ω₁^{F X}` with `ω₁ˣ` needs **no** per-degree
representative choice — the cone-dichotomy applies to the invariant set `{X : ω₁^{F X} < ω₁ˣ}` directly. (What
IS blocked is defining a regressive `g : ω₁ → ω₁` on the ordinals — *that* needs a representative per ordinal.)

### The CK-decomposition and a concrete disproof target (machine-checked, same file)
- **`ck_dichotomy`**: any invariant `F` is CK-regressive (`ω₁^{F X} < ω₁ˣ`) or CK-non-decreasing on a cone.
- **`escaping_ck_cases`**: `escaping ⟹ MP` decomposes into (a) rule out CK-regressive escaping `F`, and
  (b) prove CK-non-decreasing escaping `F` is MP.
- **`partI_false_of_ckRegressive_escaping`** (the headline): via `partI_iff_escapingMP`, an invariant
  *escaping* (≡ non-constant) `F` that **lowers the Church–Kleene ordinal on a cone would REFUTE Part 1**.
  So the disproof route is concrete: exhibit a non-constant invariant `F` with `ω₁^{F X} < ω₁ˣ` cofinally.
- **`escaping_ck_nondecreasing_of_partI`** (the dual necessary condition): *if* Part 1 holds, every escaping
  `F` is CK-non-decreasing — any proof must route through establishing `ω₁ˣ ≤ ω₁^{F X}`.

Whether branch (a) is empty is itself open and **beyond the ordinal engine**, confirmed at the code level:
`no_regressive_of_ordinal_rank` (the only descent engine) requires `base ≤ᵀ F X` on the cone, which is
exactly kernel-membership of `base`; for a ¬MP (escaping) `F` the kernel is non-cofinal, so no admissible
`base` exists — the engine cannot fire. Symmetrically, *constructing* a CK-regressive escaping `F` needs an
**invariant** choice of a CK-lowering value per degree (invariant uniformization of the incomparable-value
relation), unavailable even under `Uniformization_ℝ`. So proof and disproof of branch (a) hit the *same*
degree-level rigidity wall — the fine RK-structure of `U_M`, inner-model territory.

## Why the ordinal handle stops short (precise barriers)
Having localized the CK-regressive escaping case, the natural kill is the ordinal-ultrapower well-foundedness
`no_omega1_decreasing_conePreserving`: a degree-invariant CK-*decreasing* + *cone-preserving* function is
impossible. But:
1. **Cone-preservation fails for the sideways/escaping case, provably.** The lemma needs a single `base` with
   `∀X ≥ base, ω₁^{F X} < ω₁ˣ ∧ base ≤ᵀ F X`. The second conjunct (`base ≤ᵀ F X` on the cone) is exactly
   `base ∈ kernel`. But a base large enough for the CK-regressive cone would have to be `≥` that cone's base;
   and since `¬MP ⟹ kernel non-cofinal` (`mp_iff_belowF_cofinal`), **no kernel element is that large**. So the
   CK-regressive escaping counterexample-candidate genuinely evades the ω₁-descent.
2. **The graph doesn't help here.** `G X = X ⊕ F X` is cone-preserving, but `ω₁^{G X} = max(ω₁ˣ, ω₁^{F X}) =
   ω₁ˣ` in the CK-regressive case — so `G` *preserves* `ω₁`, never decreases it: no descent.
3. **Ordinals are too coarse for the crux.** `¬MP` is compatible with CK-*increasing* `F` (a value `F X` can
   be hyperarithmetically bigger than `X` yet Turing-*incomparable* to the avoided `Z₀`). So the CK-constraint
   filters only the CK-regressive sub-case; the general `{0,1}` degree-level fact `Z₀ ≤ᵀ F X`? is invisible to
   any ordinal invariant (an invariant ordinal function that determined the degree would well-order the
   degrees — `ω₁ ↪ ℝ`, AD-forbidden).
4. **The transfinite graph-orbit can't reach ω₁** (last session's `MARTIN_PART1_APPROACH_OMEGA1.md`): the
   limit stages need ordinal codes, i.e. `ω₁ ↪ ℝ`.

## Honest bottom line
The measure-theoretic scaffolding is now complete (kernel ideal / cofinality / above-id / CK-monotonicity),
and it yields a genuine machine-checked constraint (`MP ⟹ CK-non-decreasing`) localizing the CK-regressive
escaping counterexample-candidate. But **every elementary/ordinal measure tool stops at the same wall**: the
crux is the degree-level `{0,1}` statement `Z₀ ≤ᵀ F X`?, which no ordinal invariant or countable-completeness
argument reaches, and whose resolution is the inner-model-theoretic frontier (Steel/Siskind). The residual
open cases, refined by this session: escaping `F` that is CK-regressive, CK-preserving, or CK-increasing-but-
Turing-sideways — all beyond the ordinal method. A proof needs the fine RK-structure of `U_M` **on the
degrees**, not on the ordinals `U_M` pushes to.

## Clarification: the frontier is NOT selectivity (`U_M` is not RK-minimal in the selective sense)
`RK-minimal ⟺ selective` (every function is constant or 1-1 on a set in the ultrafilter). **`U_M` is not
selective:** the Turing jump is a *non-constant* invariant function that is *not injective on any cone* — by
Friedberg jump-inversion, every cone contains continuum-many `X` with the same jump degree `X'`. Yet
`jump_*U_M = U_M` (the jump is measure-preserving: `{X : Z ≤ᵀ X'} ⊇ cone(Z)`). So:
- the RK-rigidity frontier (`V ≤_RK U_M` nonprincipal `⟹ V = U_M`, Lutz–Siskind) is **stronger than, and
  different from, selectivity** — it is satisfied by *non-injective* MP functions like the jump, and it rules
  out sideways ¬MP predecessors, not "collapsing" ones;
- so one cannot attack the frontier by proving `U_M` selective (that is false) — the target is genuinely the
  `= U_M` rigidity, which is exactly `escaping ⟹ MP`.

This closes off "prove `U_M` selective/RK-minimal" as a route and confirms the target is the value-distribution
rigidity, whose degree-level `{0,1}` content is the inner-model-theoretic crux.

## The mechanism: why even RK-minimality would be insufficient (the `g`-inversion gap)
Trace the RK-minimality argument to see *exactly* where it stalls (this is the mechanism behind
Lutz–Siskind's "rigidity is strictly stronger than RK-minimal"). Suppose `U_M` were RK-minimal and let `F`
be a counterexample: `V := F_*U_M` is nonprincipal and `≠ U_M`, so RK-minimality gives `V ≡_RK U_M`, i.e. an
invariant `g` with `g_*V = U_M`. Then `(g∘F)_*U_M = U_M`, so `g∘F` is measure-preserving, and by **Thm 3.4
for `U_M`** (`mp_iff_aboveId`), `g(F X) ≥ᵀ X` on a cone. One hopes for a contradiction with `F X ⊥ Z_0`.
**It doesn't come:** for `X ≥ Z_0`, `g(F X) ≥ X ≥ Z_0`, so `g` maps the `⊥ Z_0` value `F X` to something
`≥ Z_0` — but `g` is an *arbitrary invariant function*, free to **lift** a sideways value above `Z_0`. Since
`g` need not be a Turing reduction (`g(Y) ≰ᵀ Y` in general), `g(F X) ≥ X` gives **no** comparison between `X`
and `F X`. So RK-minimality (`V ≡_RK U_M` via arbitrary `g`) is genuinely weaker than the needed `V = U_M`;
the residue is precisely: **no invariant `g` "inverts" a ¬MP `F` back to `U_M`.** That non-invertibility is
the degree-level rigidity — the inner-model crux — and this trace shows it is not evadable by the
`≡_RK`-level (selectivity/RK-minimality) tools, matching Lutz–Siskind exactly.

*(Aside, correcting a mis-step: `U_M` non-selective does NOT by itself give `U_M` non-RK-minimal. The
ω-ultrafilter lemma "`f` non-1-1 on every `U`-set ⟹ `f_*U <_RK U` strictly" fails for `U_M`: the jump is
non-1-1 on every cone yet `jump_*U_M = U_M` — `U_M` carries nontrivial `≡_RK`-self-maps, so `≡_RK` and `=`
part ways here, which is the same gap the `g`-inversion trace exposes.)*
