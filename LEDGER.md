# Ledger

**Sorry count: 0.** Every declaration in the repository compiles sorry-free with only
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — verified by `#print axioms`
(see `axiom_audit.lean` and REPORT.md).

This ledger therefore records not sorries but **known gaps, deliberate scope cuts, and the
obstructions behind them**, for a future run.

## Gaps (things stated or motivated but not proved)

1. ~~**Jump order-preservation / degree-invariance**~~ **DISCHARGED** in
   `JumpInvariance.lean` (added after the first ledger draft): `trE_primrec` proves the code
   translation primitive recursive via `Primrec.nat_strong_rec`, yielding `jumpFn_mono`,
   `jumpFn_congr`, `Martin.orderPreserving_jump`/`turingInvariant_jump`, and the degree-level
   `TuringDegree.jump` with `TuringDegree.lt_jump`. All sorry-free.

2. **No determinacy instance for the cone theorem.** `Martin.cone_theorem` takes
   `GameDetermined A` as a hypothesis. Nothing in Mathlib proves determinacy of any nontrivial
   game class (Gale–Stewart open/closed determinacy included). Options for a future run:
   (a) prove clopen/open determinacy for our concrete game encoding directly (Gale–Stewart is
   ~a few hundred lines); (b) bridge to Sven Manthe's Borel determinacy repo
   (github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean, Lean v4.28 vs our
   v4.34 — needs porting) — its main theorem is `GaleStewartGame.borel_determinacy`.
   A bridge must translate his tree-games to our history-number games.

3. **`PartII_Borel_WF` phrasing.** Well-foundedness is stated via `WellFounded` on the subtype
   `{F // Regular F}` with the strict Martin order. Classically this is the standard
   "prewellordering" phrasing (total + well-founded), but a referee should double-check it
   against Lutz Def 1.15 ff. — in particular that we did not need to quotient by `≡ₘ` first
   (we did not: well-foundedness of a strict order is quotient-invariant).

4. **Uniformity convention (Lachlan).** `LachlanStatement` uses the arbitrary-`u` notion of
   uniform invariance (Lutz Def 1.28). Lachlan's original 1975 paper should be checked for
   whether his uniformity is the same or the computable-`u` variant
   (`ComputablyUniformlyTuringInvariant` is provided for the latter). The statement is
   strictly stronger with arbitrary `u` in the negative position (¬∃ over a larger class), so
   if in doubt the formalization errs on the *stronger* claim; flip if the literature
   disagrees.

5. **Borel = product-measurable.** `Measurable` on `ℕ → Bool` uses the product σ-algebra
   (`MeasurableSpace.pi` with `⊤` on `Bool`), which coincides with the Borel σ-algebra of the
   Cantor topology mathematically; the identification (`borel_eq_pi`-style lemma) is not
   formalized. Statement-level risk is low but it should be discharged before claiming the
   statements are *the* Borel Martin conjecture.

## Deliberate scope cuts

- **No universal machine / `evaln`** for oracle codes. Not needed for jump strictness (see
  blueprint). Needed later for: jump is Σ⁰₁-complete relative to the oracle, c.e. degrees,
  Lachlan's theorem.
- **`rfind` instead of `rfind'`** in `OracleCode` — see blueprint; revisit if a step-indexed
  universal machine is built.
- **Lachlan's theorem (T4)** not attempted: needs the recursion theorem for oracle codes
  (fixed-point via `smn`, i.e. `curry` machinery on `OracleCode`), which needs the primrec
  code-operation layer (same infrastructure as gap 1). This is the natural next milestone.
- **Kleene–Post** (incomparable degrees below `0′`) not attempted (finite-extension argument;
  needs careful finite-string/oracle-approximation infrastructure that does not exist yet).

## Obstructions hit (engineering notes for the next run)

- **`PFun` is not reducible.** `simp`/`rw` refuse to act on `Part.some x >>= f` when
  `f : ℕ →. ℕ` is a variable ("motive is not type correct" / "made no progress" with a note
  about implicit transparency). Workarounds used throughout: (i) state everything possible
  with `f : ℕ → Part ℕ` (e.g. `jumpFn`); (ii) the `mem_eval_*` membership characterizations
  in `OracleCode.lean`, proved term-level once; (iii) `show _ = _ from Part.bind_some _ _`
  casts. Upstream fix worth proposing: make `PFun` reducible or provide a `simp` set.
- **`Nat.rec_add_one` does not fire** via `rw`/`simp` on `Nat.rec` terms with `Part ℕ` motive;
  use `show (Nat.rec (motive := fun _ => Part ℕ) _ _ m).bind _ = _` to expose the iota
  reduction instead.
- **`rw` under `have`-binders fails** when the rewrite target occurs in the binder's proof
  term (e.g. unfolding `hlen`); `simp only` succeeds where `rw` fails.
- **`if_pos`/`if_neg` are deprecated** in current Mathlib (warnings only; left as-is).
- The `Denumerable OracleCode` instance exists but nothing uses it yet; it is the hook for
  stating `Computable` facts about code-valued functions later.
