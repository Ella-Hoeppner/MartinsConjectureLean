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
