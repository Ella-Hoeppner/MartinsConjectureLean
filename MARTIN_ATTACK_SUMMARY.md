# Martin's Conjecture Part 1 — genuine attack, honest summary

*A real attempt to crack the sole open content of Part 1 (the incomparable core), not a formalization of
known results. No crossing — it is a ~50-year-open problem — but a thorough, honest attack that correctly
identified, precisely stated, and (against the literature) validated the true frontier, with machine-checked
substrate and two genuine self-corrections. Details: `MARTIN_PART1_APPROACH_OMEGA1.md`,
`MARTIN_PART1_STRUCTURAL_AM.md`.*

## The problem, stripped down
The sole open content of Part 1 is the **incomparable core**: a Turing-invariant `F` with `F X ⊥ᵀ X` on a
cone is constant on a cone. Machine-checked reframing (`incomparableConstant_iff_noIncomparableSelfMap`):
this says **no invariant `F` goes "sideways" (`F X ⊥ᵀ X`) on a cone**.

## What I tried, and what happened
1. **Increasing graph-orbit → ω₁-chain.** Iterate `G X = X ⊕ F X` (invariant, increasing, strictly so on
   the cone — `graphOrbit_strictMono`, machine-checked). A length-`ω₁` chain would give `ω₁ ↪ ℝ`, impossible
   under AD ⇒ contradiction. **Provable no-go:** building the chain to `ω₁` *is* the `ω₁ ↪ ℝ` AD forbids —
   self-defeating.
2. **Fodor on the Church–Kleene ordinal.** Dies at the *identical* `ω₁ ↪ ℝ` step (need to pick a degree per
   ordinal). **Unified obstruction:** lifting per-degree info to `ω₁`-level needs a Turing code (the open
   region has none) or `ω₁`-many choices (AD-forbidden). *Validated:* Lutz–Siskind's theorem is stated under
   `AD + Uniformization_ℝ` — exactly the choice-substitute this obstruction says is required.
3. **Structural / ∞-Borel route.** **Theorem A** (rigorous): a Borel invariant `F` of Baire rank `ρ` has
   `F X ≤ᵀ X^(ρ)` with `ρ` *fixed* ⇒ the Borel case has *no* rank-unboundedness; Lutz's obstruction is
   ∞-Borel-specific, not Borel. (Correctly separates Borel from the hard transfinite case.)
4. **Coordinated trees — RULED OUT (honest self-correction).** For the incomparable core, (coordinated tree
   ∧ domination ∧ coding) ⟹ `x ≤ᵀ F x` ⟹ `⊥`; so proving the domination bracket *is* proving the core — the
   Slaman–Steel method is inherently a **regressive** tool and gives no genuine reduction. The *uniform* half
   of domination is provably impossible (`incomparable_jump_not_below`, machine-checked). This **corrects**
   an earlier over-optimistic "the core reduces to a coordinated tree" framing.
5. **Measure-theoretic route — the viable one.** The Groszek–Slaman engine (`MP ⟹ above-id`, machine-checked
   in-repo) is *not* circular for the incomparable core. So the crux is `escaping ⟹ MP`, a **value-distribution**
   question with zero coordinated-tree content. A counterexample is escaping-but-**not**-measure-preserving
   (`incomparable_not_measurePreserving`, machine-checked).

## The frontier — identified, then validated verbatim against the literature
The crux is cleanest as **`escaping ⟹ above-id`** (since `MP ⟺ above-id`), and in ultrafilter terms as
**`U`-preservation**: for invariant `F`, `F_*U` non-principal ⟹ `F_*U = U`. I derived this — *including the
subtle point that it is stronger than plain RK-minimality* (`= U`, not merely `≡_RK U`).

**This matches the published frontier exactly.** Lutz–Siskind (arXiv:2305.19646) prove: under
`ZF + AD + Uniformization_ℝ`, Part 1 ⟺ **"every nonprincipal ultrafilter `V` on the Turing degrees with
`V ≤_RK U_M` equals `U_M`"**, and explicitly note it is *stronger than `U_M` being RK-minimal*. Their Def 1.7
(measure-preserving), Prop 1.8, and Thm 3.4 coincide term-for-term with the repo's `MeasurePreserving`,
`mp_iff_aboveId`, and the Groszek–Slaman engine.

**Deepest "why" (§10):** the incomparable core is the *non-linearity* of the Turing degrees. Under a normal
measure on `ω₁` (linear order) the analogue is trivially true (Fodor; no incomparable case). The degrees'
*partial* order creates the incomparable case, with no ordinal analogue — that is the whole difficulty.

## Honest bottom line
- **Not solved.** The frontier — `U_M` has no nonprincipal RK-predecessor on the degrees other than itself —
  is a genuine open problem in **AD ultrafilter theory** (Steel–Woodin / Siskind's inner model theory), open
  even under `AD + Uniformization_ℝ`; the AD-vs-AD⁺ depth question stands.
- **Genuine contributions:** correctly identifying + precisely stating the frontier (independently matching
  the literature verbatim); ruling out the coordinated-tree approach with a proof (correcting earlier work);
  Theorem A (Borel = fixed level); the non-linearity account; and machine-checked substrate
  (`MartinOmega1Approach.lean`, `LevelCoordinatedTree.lean`, standard axioms only).
- **Next session:** attack `escaping ⟹ MP` / the RK-statement measure-theoretically (is `U_M` RK-minimal
  known? then the open part is the rigidity `≡_RK U_M ⟹ = U_M`). **Do not** return to coordinated trees.

## A concrete lead for the next attempt (connecting the pieces)
The RK-rigidity frontier ("`U_M` has no nonprincipal RK-predecessor on the degrees but itself") **holds for
the Turing degrees but FAILS for the enumeration degrees** — Nakid-Cordero (arXiv:2510.19147) build a
definable non-uniform e-invariant function, i.e. a nonprincipal RK-predecessor of the e-analogue of `U_M`
that is `≠` it. The pivot (my `ATTACK.md` B9+): the Turing **jump is increasing** (`A ≤ᵀ jump^[k] A`,
machine-checked `self_le_jumpIter`), whereas the enumeration **skip is not** — and my Part-2 leak
(`am_not_finite_jump_of_increasing`) consumes *exactly* the increasing property. So a proof of the RK-rigidity
statement for the Turing degrees should **exploit the jump's increasing-ness as the feature the e-degree skip
lacks** — this is where the Turing/e-degree asymmetry lives, made concrete. Combined with the non-linearity
account (§10 of the structural note: ordinals are linear ⇒ Fodor ⇒ easy; degrees are partial ⇒ incomparable
case), the target for a proof is: *use `A ≤ᵀ jump A` and the cone/ultrafilter structure to force an
unbounded-below invariant pushforward of `U_M` to be cofinal-above (= `U_M`).* That is the sharpest concrete
handle this attack produced on the actual open frontier.

**Honesty caveat on the lead (I tested it).** The *direct* deployment fails: for a fixed avoided `Z_0` that
is hyperarithmetically generic relative to `F X` (`Z_0 ≰_h F X`), *no* jump `(F X)^(α)` computes `Z_0`, so the
jump-tower alone does not force `F X` (or its jumps) above `Z_0`. Increasing-ness is the right *feature*
(it is what the e-degree skip lacks and what `am_not_finite_jump_of_increasing` consumes), but it must be
combined with the cone/ultrafilter/measure structure — it is not, by itself, a proof. So the lead names the
correct property to exploit, not a shortcut; the genuine work remains in AD ultrafilter theory.
