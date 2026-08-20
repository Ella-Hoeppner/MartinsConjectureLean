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

2. **No determinacy instance for the cone theorem.** (Session 2: the dichotomy is now
   proved *unconditionally* for open and closed Turing-invariant sets via topological
   triviality — `TopologicalTriviality.lean` — so the determinacy hypothesis only matters
   from proper Borel levels upward.) `Martin.cone_theorem` takes
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
   statements are *the* Borel Martin conjecture.  (Session 2 partially mitigates: the jump
   and all cones are proved measurable w.r.t. the operative σ-algebra, so the framework's
   own membership facts are self-consistent.)

## Deliberate scope cuts

- ~~**No universal machine / `evaln`**~~ **BUILT (session 4)**: `Evaln.lean` +
  `EvalnPrim.lean` (`evaln_prim`) + `Universal.lean`.  This unlocked the recursion theorem,
  s-m-n, padding, Σ₁-completeness of the jump (`dom_iff_jumpP`), and the full Shoenfield
  limit lemma (`limit_lemma`).
- **`rfind` instead of `rfind'`** in `OracleCode` — the session-4 universal machine
  (`evaln`) used a bounded `searchList` over an explicit value list instead of the
  `rfind'`-offset device, so the plain-`rfind` choice caused no problems downstream.
- **Lachlan's theorem (T4)** not attempted — but its prerequisite (the recursion theorem
  for oracle codes) is now PROVED (`Universal.exists_fixedPoint`), along with s-m-n
  (`SmnPadding.smn`) and padding.  What remains is transcribing Lachlan's specific
  combinatorial argument; deferred rather than risk an incorrect formalization.
- ~~**Kleene–Post** not attempted~~ **PROVED in session 2** (`KleenePost.lean`), via the use
  principle (`Locality.lean`).  Note: the classical statement also places the incomparable
  pair *below `0′`* (via a computable-in-`0′` construction); the effectiveness refinement is
  NOT formalized — only existence of an incomparable pair.  The refinement would need the
  construction to be `0′`-computable, i.e. the universal machine / `evaln` layer.
- **General Theorem 3.4 / pointed perfect trees — frontier as of 2026-08-20.** The general
  measure-preserving direction of Part 1 is reduced, in full and machine-checked, to
  `MartinPPT'` (`RawPPT.lean`): *every set cofinal in the Turing degrees contains a pointed
  perfect tree*. This is exactly Martin's cited Lemma 2.3 (ZF+AD), with **no** recursion-
  theoretic promises attached — the old `recover` field (Lutz–Siskind Lemma 2.1) is now the
  proved theorem `Martin.lemma21` (`EffectiveTree.lean` + `EffectiveTreeReduction.lean`), and
  `pointed`/`realizes` are the genuine minimal content of "pointed perfect tree". Remaining
  gap = `MartinPPT'` itself: Martin's tree-producing determinacy game plus the perfect-tree
  navigation for `realizes` (Prop 1.10). Must be proved from a determinacy hypothesis
  (`GameDetermined`/`TuringDeterminacy`), **never** an added axiom. This is the single cited
  input the whole measure-preserving branch now rests on.

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
