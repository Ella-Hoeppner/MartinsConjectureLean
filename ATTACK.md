# Attack log: Martin's conjecture, Part I

Session 3 (2026-08-13 afternoon). This file records the *direct* attack on the open
content of Martin's conjecture: what was proved, what was attempted on the open cores,
and precisely where each attempt failed. Companion code: `MartinMeasure.lean`,
`Reduction.lean`, `BoundedCase.lean`, `OrderPreservingCase.lean` (all sorry-free).

## What the attack achieved (proved, sorry-free)

Under the explicit hypothesis `TuringDeterminacy` (all Turing-invariant games determined
— the AD-style hypothesis; its Borel restriction is a ZFC theorem of Martin not yet in
Lean):

1. **σ-pigeonhole** (`exists_onCone_of_cover`): countably many invariant determined sets
   covering a cone ⟹ one contains a cone. Martin measure is a countably complete
   ultrafilter, formally.
2. **Comparability trichotomy** (`comparability_on_cone`): every invariant `F` is, on a
   cone, ≡ id, > id, < id, or ⊥ id.
3. **The reduction** (`partI_of_cores`): Part I ⟸ the two open cores:
   - `RegressiveImpliesConstant` (`F < id` on a cone ⟹ constant on a cone),
   - `IncomparableImpliesConstant` (`F ⊥ id` on a cone ⟹ constant on a cone).
   In the other two regimes Part I is proved outright.
4. **Index stabilization** (`exists_uniform_index_on_cone`): a regressive invariant `F`
   is computed by a *single fixed* oracle machine on a representative of every degree on
   a cone.
5. **Boundedness lemma** (`bounded_implies_constant`): values below a fixed `Z` on a cone
   ⟹ constant on a cone (countably many `Z`-computable reals + pigeonhole).
6. **Escape theorem** (`counterexample_escapes`) and the sharpened cores
   (`regressive_core_iff_escaping`, `incomparable_core_iff_escaping`): any counterexample
   escapes every fixed degree on a cone.
7. **Order-preserving skeleton** (`orderPreserving_measurePreserving_or_avoids`,
   determinacy-free; `partI_orderPreserving_of_lemmas`): Lutz–Siskind's theorem reduced
   to its two main lemmas, with the elementary dichotomy fully proved.
8. **Counterexample profile** (`counterexample_profile`): the conjunction of 2 & 6.

Items 1–6 constitute, to our knowledge, the first machine-checked formalization of the
standard structural analysis surrounding Martin's conjecture. The open problem is now
formally *isolated*: it is exactly the two escaping cores.

## Exact analysis of the cores (added at session end)

`CoreAnalysis.lean`: the incomparable core is an *impossibility statement*
(`incomparable_core_iff_never` — its hypothesis and conclusion are jointly
contradictory), and the reduction of Part I to the two cores is an **exact
equivalence** (`partI_iff_cores`).  So the formal isolation of the open content is
lossless: Part I (AD-style, mod Turing determinacy) *is* the conjunction
"regressive ⟹ constant" ∧ "invariant functions are never ⊥-with-id on a cone".

## Direct attempts on the escaping cores, and where they died

**Attempt A — join-limit coding (regressive/avoiding case).** Given escaping `F`, build
`X₀ ≤ X₁ ≤ ⋯` where `X_{n+1}` escapes `Z_n := ⊕_{k≤n} F(X_k) ⊕ Z₀`, and pass to
`X_ω := ⊕ X_n`. Order preservation gives `F(X_ω) ≥ F(X_n)` for each `n`. **Failure
point**: to contradict "range avoids `cone Z₀`" one needs `F(X_ω) ≥ ⊕_n F(X_n)` (the
*ω-join*, into which `Z₀` could be coded), but an upper bound of each column need not
compute the join *uniformly* — this is precisely the non-uniformity gap that makes
Spector exact pairs exist. The argument establishes nothing beyond directedness.

**Attempt B — topological/Baire arguments.** Every degree-class is dense, and `F` is
constant-mod-≡ on each class; for continuous or Borel `F` one hopes density + continuity
collapse the values. **Failure point**: the value-classes are themselves dense, so
"`F(X_n) → F(Y)` with `F(X_n) ∈ D₁`" gives `F(Y) ∈ closure(D₁) = 2^ω` — no information.
Category-theoretic strengthening founders on the standard mismatch: cones are neither
comeager nor null; Martin measure and Baire category are orthogonal largeness notions.

**Attempt C — Posner–Robinson leverage (incomparable case).** With `F X ⊥ X`, the join
`H(X) = X ⊕ F X` is invariant and strictly above the identity; relativized
Posner–Robinson (`A ≰ X ⟹ ∃ G ≥ X, A ⊕ G ≡ G′`) is the classical tool to convert
"incomparable information" into jump-computations and drive a contradiction against
part II-type structure. **Failure point**: Posner–Robinson itself (Kumabe–Slaman
forcing) is a major unformalized theorem, and the surrounding argument (Slaman–Steel)
additionally needs the pointed-perfect-tree machinery. Both are genuine formalization
projects, not session-scale steps.

**Attempt D — after stabilization (uniform-machine case).** Index stabilization gives a
fixed `e` computing `F` on a representative of every degree on a cone. Steel's proof
(for uniformly invariant `F`) proceeds by comparison games along *pointed perfect
trees* to show the value degree stabilizes. **Failure point**: the representative
produced by stabilization varies with the degree, and controlling `Φ_e` across
*different representatives of the same degree* is exactly the content of Steel's
game analysis. Without pointed trees there is no handle.

## Progress on pillar (i) after this log was first written

`UniformJoin.lean` (sorry-free) lays the foundation of the pointed-tree pillar in the
"uniformly pointed join-cone" formulation, which avoids tree combinatorics entirely:

* `join_realizes` — above the base, canonical representatives `join W X` realize every
  degree;
* `equivVia_join_uniform` — **controlled congruence**: a computable index
  transformation, independent of `W, X, X'`, turning witnesses for `X ≡ₜ X'` into
  witnesses for `join W X ≡ₜ join W X'` (proved by explicit code construction: a fixed
  even/odd mixer code, the right-projection code, and the `trOracle` splice of the given
  index through the projection);
* `uniformlyTuringInvariant_comp_join` — composing a uniformly invariant function with
  the canonical-representative map preserves uniform invariance, with a computed
  uniformity function.

This is precisely the mechanism by which Steel-style arguments control a function
across representatives of the same degree.  What remains for Steel's uniform case is
the comparison-game analysis itself (pillar iii).

## BREAKTHROUGH (session 4): the single blocker is gone

The universal machine for `OracleCode` — the artifact every attempt funneled through — is
now built and proved, sorry-free:

* `Evaln.lean`: `evaln` (step-indexed evaluation with a finite oracle table), with
  `evaln_sound`, `evaln_complete`, `evaln_mono`.
* `EvalnPrim.lean`: **`evaln_prim`** — `evaln` is primitive recursive (course-of-values
  recursion over stage tables; `stageStep_spec` + `Primrec.nat_strong_rec`).
* `Universal.lean`: **`eval_universal`** (the two-argument evaluator is recursive in any
  total oracle, by dovetailing `evaln` over the oracle's own graph) and
  **`exists_fixedPoint`** — Kleene's second recursion theorem, relativized.
* `LimitLemma.lean`: **`dom_iff_jumpP`** (Σ₁-completeness of the jump) and
  **`recursiveIn_jump_of_limit`** (Shoenfield limit lemma, substantive direction).

With these, the paths in Attempts D and E are no longer blocked at the recursion-theorem
step. See `Lachlan.lean` for the first named partial result now within reach.

## Lachlan's theorem: a concrete formalization plan (session-4 research)

Researched against Lutz's thesis Ch. 3 (2026-08-13).  **Exact statement** (local form,
Cor 3.11, ZF, *no determinacy*): if `W` is an r.e. operator, `X ≥ᵀ 0′`, and `X ↦ Wˣ` is
uniformly Turing invariant on `deg_T(X)`, then `W` is constant on `deg_T(X)`, or
`Wˣ ≡ᵀ X`, or `Wˣ ≡ᵀ X′`.  The unrestricted-`F` "no Post solution" gloss is often
attributed to Lachlan but at full strength is **Steel 1982**; Lachlan's own theorem carries
the **r.e.-operator** hypothesis.  (Formal statements corrected accordingly in `Martin.lean`:
`NoUniformPostSolution`, `LachlanLocalStatement`.)

**The engine — Thm 3.10 (determinacy-free): `W` continuous on `deg_T(X)` or `Wˣ ≥ᵀ X′`.**
Discontinuity direction (the pure diagonalization, the smallest clean target):
1. From discontinuity of the r.e. operator, extract a marker `n` with `n ∉ Wˣ` but for every
   `σ ≺ X` some finite `τ ⊇ σ` has `n ∈ W^{σ⌢τ}`.
2. Build `yₑ ≡ᵀ X` coding `Φˣₑ(e)↓`: `yₑ = X` if it diverges; else splice the least marker-
   witnessing `τ` after the halting-stage prefix.
3. **s-m-n (NOT a Kleene fixed point):** computable `r, s` with `X ≡ᵀ yₑ via (r e, s e)`.
   (Uses `smn`/`curryEnc` + padding — already formalized.)
4. Feed `(r e, s e)` through a **computable** uniformity function `u` (Bard's Lemma 3.8):
   `u (r e, s e)` computes `W^{yₑ}` from `Wˣ`, uniformly in `e`.
5. `n ∈ W^{yₑ} ⟺ Φˣₑ(e)↓`, so `Wˣ` computes `X′` (uses `dom_iff_jumpP` — formalized).
Continuity direction (Cor 3.11): continuity ⟹ `Wˣ ≤ᵀ X ⊕ 0′`, and with `X ≥ᵀ 0′` and
Bard's Thm 3.6, `W` constant or `Wˣ ≡ᵀ X`.  Globalization to a cone (Thm 3.1) uses Turing
determinacy once (Prop 3.9) — plug in our `cone_theorem`.

**Missing infrastructure (the reason this is a separate multi-session project, not a
2-hour add):**
- **r.e. operators** `W : (ℕ → Bool) → Set ℕ` with the enumeration/marker structure and a
  notion of continuity on a degree.  We have oracle *functionals* (`eval`) but not the
  r.e.-operator layer.
- **Bard's Lemma 3.8** (arbitrary uniformity function ⟹ a computable one) — a reusable
  lemma we would need to prove.
- The splicing s-m-n functions `r, s` proved to compute `yₑ`/`X` with the exact prefix
  behaviour.
Everything else (s-m-n, padding, Σ₁-completeness `dom_iff_jumpP`, the jump, the cone
theorem) is already in hand.  This is the recommended next-session target; it is deliberately
**not** attempted here rather than risk an incorrect or `sorry`-laden formalization.

### UPDATE (2026-08-14): reduction half DONE; the exact coding construction worked out

**Reduction half formalized** (`DiscontinuousCase.lean`): given the coding family
(`HasCodingFamily`) + computable uniformity, `discontinuous_reduction` proves `X′ ≤ᵀ Wˣ`
via s-m-n + `eval_universal` at the marker; sharpened to `Wˣ ≡ᵀ X′`
(`discontinuous_equiv_jump`), assembled into `local_dichotomy_high` (Lutz Cor 3.11 form) and
`no_operator_post_solution`.  **The universal code was never a blocker** — `eval_universal`
and `exists_fixedPoint` are proved.  Only `HasCodingFamily` and Bard's Lemma 3.8 remain.

**The precise coding real (the missing step 2), now correct — insertion, not overwrite.**
Fix marker `n₀`.  Let `t(c)` = halting stage of `Φ_c^X(c)` (least steps; ⊥ if it diverges),
with use `u ≤ t`.  Let `τ'(c)` = least `τ` with `haltsOn(X↾t(c) ⌢ τ, e, n₀)` (exists by
discontinuity: `extHaltsFrom(X↾t, e, n₀)`).  Define `Y_c` by **inserting** `τ'` at position
`t`:
```
Y_c(m) = X(m)              if Φ_c^X(c) does not halt within m steps      (⟺ m < t, or ⊥)
       = τ'(c)(m − t)      if halted within m steps and t ≤ m < t+|τ'|
       = X(m − |τ'|)       if halted within m steps and m ≥ t+|τ'|
```
- **`Y_c ≤ᵀ X`** (uniform machine `cY`, oracle `X`, input `⟨c,m⟩`): bounded simulation
  `evaln m` decides "halted within m steps"; if so compute `t, τ'` (τ' by a terminating
  `rfind` over `haltsOn`, `0′`-free since `haltsOn` on a fixed prefix is decidable via
  `evaln`), then read the shifted `X`.  Total & `X`-recursive.  `r c := curryEnc ⌜cY⌝ c`.
- **`X ≤ᵀ Y_c`** (uniform machine `cM`, oracle `O` = `Y_c`, input `⟨c,m⟩`): run `Φ_c^O(c)`
  for `m` steps — **valid because `Φ_c`'s use `u ≤ t` sees only `Y_c↾t = X↾t`**, so
  `Φ_c^{Y_c}(c) = Φ_c^X(c)` (same stage `t`, same `τ'` from `O↾t`).  Recover
  `X(m) = O(m)` if not-halted-within-m, else `O(m+|τ'|)` (un-shift).  `s c := curryEnc ⌜cM⌝ c`.
- **`n₀ ∈ W^{Y_c} ⟺ Φ_c^X(c)↓`**: if halts, `Y_c↾(t+|τ'|) = X↾t ⌢ τ'` halts `W` at `n₀`
  (monotonicity); if diverges, `Y_c = X` and no prefix of `X` halts `W` at `n₀`.

`cY` uses the fixed oracle `X`, so `exists_code_of_recursiveIn` on the (uniform in `⟨c,m⟩`)
`RecursiveIn {toPFun X}` proof gives it directly, then `r c := curryEnc ⌜cY⌝ c`.  **`cM` is the
genuine cost**: its oracle is `Y_c`, which *varies with `c`*, so a computable `s` needs one
**oracle-generic** code (same code, correctness for every oracle), i.e. the *explicit*
universal machine as an `OracleCode` — which the codebase does **not** have.  `Universal.lean`
proves only the per-oracle `RecursiveIn` form (`eval_universal`); `exists_code` off it gives a
*per-`X`* code, not a uniform one.  Building the explicit universal code (assemble
`graphEnc`'s oracle-`prec` code + oracle-free `evaln`/`ts`/`extv` codes via `exists_code_of_partrec`
+ the `rfind` search, mirroring `eval_universal`'s proof at the code level, ~300–400 lines) is
therefore the true **prerequisite foundational milestone** — the "step-indexed universal
machine" `OracleCode.lean`'s design note says was not built.  **DONE (2026-08-14,
`UniversalCode.lean`): `eval_univCode`** — `univCode : OracleCode` with
`eval (toPFun X) univCode ⟨e,n⟩ = eval (toPFun X) (ofNatCode e) n` for every total `0/1`
oracle `X`, a single code uniform across oracles.  Built from `cGraph` (explicit oracle
graph-prefix encoder) + oracle-free `uEvalnD`/`uTs`/`uExtv` codes (`exists_code_of_partrec`) +
the `rfind` search; correctness by `evaln` soundness/completeness with the membership lemmas.
The reusable Part-monad eval idiom (`eval_left_app`/`eval_right_app` + explicit `Part.bind_some`
terms for `PFun` continuations) is now in place.  **This unblocks the coding-family recovery
machine `cM`** (bounded universal sim via `univCode` + un-shift): the remaining work to
discharge `HasCodingFamily` is the `Y_c` splicing + `cY`/`cM` codes + s-m-n specialization, and
externally Bard's Lemma 3.8.

### UPDATE (2026-08-14): the coding family's mathematical heart is DONE

`CodingFamily.lean` builds the coding real and its marker property, sorry-free:
- `yc e n₀ X c` — the splicing real (insert the least `0/1` marker-witness at `Φ_c^X(c)`'s
  halting stage), with `haltedB`/`hStage`/`conv_iff_jump` halting machinery, `graphOf_yc`
  (graph agreement), and **`marker_property`**: `reReal e (yc..) n₀ = true ↔ jump X c = true`
  under the `0/1` discontinuity data.
- `wit` uses a `⟨witness, step⟩` **pair-search** (not "least `k` with `haltsOn`", which is only
  `Σ₁`), so it is genuinely `X`-computable — the precondition for `yc ≤ᵀ X`.

**Remaining to discharge `HasCodingFamily`** (two Turing reductions as exact s-m-n codes):
1. **`yc ≤ᵀ X`**: prove `(c,m) ↦ bitg (yc.. c) m` is `RecursiveIn {toPFun X}` (bounded `evaln`
   sim for `haltedB` + bounded search for `hStage` + the `wit` `μ`-search + shift), take its
   code via `exists_code_of_recursiveIn`, then `r c := curryEnc ⌜cY⌝ c`.
2. **`X ≤ᵀ yc`**: an oracle-generic recovery machine `cM` (run `Φ_c^{Y_c}(c)` via `univCode`,
   then un-shift), correct because `Φ_c`'s use lies below the halting stage where `Y_c = X`;
   then `s c := curryEnc ⌜cM⌝ c`.
Both are ~200-line `RecursiveIn`/code constructions (the `condN`/`jstrEnc` idiom + `univCode`);
the math is settled, the labor is the remaining step.  Externally: Bard's Lemma 3.8.  With it, `cM` (recovery = bounded
universal sim + un-shift) and `cY` assemble `HasCodingFamily`; then Bard 3.8 (bare uniform
invariance ⟹ computable) is the last external lemma.  Math certain; scope is a dedicated session.

**Steel's uniform Part II (Q4):** needs the m-Game + AD + Wadge/Martin–Monk machinery and
**uniformly pointed perfect trees**.  We already have the u.p.p.-tree analog in the
join-cone formulation (`UniformJoin.equivVia_join_uniform` — the uniform congruence index),
but the game and Wadge layers are absent.

## Effective Kleene–Post: complete Lean-level execution guide

The full proof is worked out; what remains is formalization labour (encoding plumbing).
Recorded here so a future session can execute it directly.

**Statement.** `∃ A B : ℕ → Bool, A ≤ᵀ jump ∅ ∧ B ≤ᵀ jump ∅ ∧ ¬(A ≤ᵀ B) ∧ ¬(B ≤ᵀ A)`.

**Representation.** Strings are `List ℕ` of 0/1 values (matching `evaln`'s oracle table),
encoded by `Encodable.encode`.  A condition is `pair (encode σ) (encode τ)`.

**Step** at stage `r` (`r = 2e` defeats `Φₑᴮ = A`; `r = 2e+1` defeats `Φₑᴬ = B`, symmetric).
Even case, `e = r/2`, current condition `(σ, τ)`:
- Query `0′`: does `∃ ext, fuel, evaln fuel (τ ++ ext) (ofNatCode e) |σ|` halt?  This is exactly
  `extHalting_recursiveIn_jump` at `(encode τ, e, |σ|)` — **proved**.
- **YES**: run `ehFun` (halts, since decided yes) to get the least witness `w = (encode ext, fuel)`;
  let `v` be the `evaln` value.  Set `σ' = σ ++ [if v = 0 then 1 else 0]` (a bit ≠ `v`),
  `τ' = τ ++ ext`.
- **NO**: `σ' = σ ++ [0]`, `τ' = τ ++ [0]`.
Step is `Nat.RecursiveIn {jump ∅}` (decode/encode/`evaln` are primrec; one oracle query; the
YES-branch search `ehFun` is `∅`-partrec hence recursive in `jump ∅`).

**Stages / reals.** `stages = prec` over the step (base `pair (encode []) (encode [])`); `σ`/`τ`
are nested, so `A = ⋃ σ`, `B = ⋃ τ` are well-defined limits; `A, B ≤ᵀ jump ∅` because
`stages` is `jump ∅`-recursive and `A n` reads the σ-part of a stage past `n` (mirror
`KleenePost.agreesA`).

**Incomparability (the non-obvious bridge — all tools present).** For requirement `2e`:
- *YES branch*: `evaln fuel (τ ++ ext) c |σ|_r = some v` and `B ⊇ τ' = τ ++ ext`, so by
  `evaln_sound` (table = a prefix of `B`’s graph) `v ∈ eval (toPFun B) c |σ|_r`, i.e.
  `Φₑᴮ(|σ|_r) = v`.  And `A(|σ|_r)` was set `≠ v`.  So `Φₑᴮ ≠ A`.
- *NO branch*: if `Φₑᴮ(|σ|_r)↓` then by `evaln_complete` some `evaln k (graphOf (bitg B) k) c |σ|_r`
  halts; since `B ⊇ τ`, `evaln_mono` extends that table to `τ ++ ext` for a suitable `ext`,
  contradicting the NO decision.  So `Φₑᴮ(|σ|_r)↑ ≠ A` (total).
Hence no `e` computes `A` from `B`; symmetric for `B` from `A`.

Implementation note (the one non-obvious combinator): the "if the `0′` bit says *halts*,
run the `∅`-partrec witness search, else return a default" conditional is expressible in
`Nat.RecursiveIn` **via the `prec` constructor recursing on the oracle bit** `b`:
`Nat.rec (Part.some default) (fun _ _ => searchValue p) b` — the partial search is only
evaluated in the `b ≥ 1` (successor) branch, so it is never run when the bit is `0`.  This
sidesteps the usual "can't multiply out a partial function" obstruction.

Every ingredient (`extHalting_recursiveIn_jump`, `ehFun`, `evaln_sound/complete/mono`, `prec`,
the encodings) is already in the repository.  The obstacle is purely the length/friction of the
`Nat.RecursiveIn {jump ∅}` step term and the limit bookkeeping — estimated one focused session.

## Assessment

The mathematical wall is real and precisely located: all four attempts die at one of
three missing pillars — (i) pointed perfect trees and the "measure-one sets contain
pointed trees" refinement of the cone theorem, (ii) Posner–Robinson / Kumabe–Slaman
forcing, (iii) Steel's comparison-game analysis. These are the same pillars the human
proofs of the *known* partial results rest on. No shortcut around them was found, and
(honestly) none was expected: the escaping cores as isolated here are exactly the
50-year-open content.

## Attempt E — Steel's dichotomy game, formulated in this framework

The last direct attempt of the session was to formulate Steel's
boundedness-or-domination game for a uniformly invariant `F` inside the game
framework of `ConeTheorem.lean` (players alternate bits; II's real codes a triple
`(k, l, Y)`; payoff: *if* `Y ≡ₜ X` via `(k, l)` *then* `X ≤ₜ F Y`), aiming at:

* II wins ⟹ `F ≥ id` on a cone — this direction is executable with existing tools:
  the play is computable from the players' data (`gamePlay_le`), and uniformity
  transports `X ≤ₜ F Y` to `X ≤ₜ F X` via `u (k, l)`;
* I wins ⟹ `F` is bounded on a cone (⟹ constant, by the boundedness lemma).

**Failure point, and a structural discovery.**  The "I wins" analysis requires II to
play indices `(k, l)` witnessing `Y ≡ₜ X` where `X` is I's response *to that very
play*: the honest-play indices are a fixed point of a computable index
transformation.  This is exactly the **Kleene recursion theorem for oracle codes**
(`∀ computable g, ∃ c, ∀ O, eval O (g c) = eval O c`), whose proof requires the
self-application `Φ_x(x)` — i.e. the **step-indexed universal machine** (`evaln`),
the one infrastructure layer this project deliberately skipped.

The same missing artifact blocks Attempt D (Steel's comparison analysis), Lachlan's
theorem (recursion-theorem trickery), and the effective refinement of Kleene–Post.
**Conclusion: every remaining path — all three pillars — funnels through a single
missing artifact: the universal machine for `OracleCode`.**  It is a large mechanical
port (Mathlib's `evaln` + `evaln_prim` development, relativized, est. 300–600 lines
of hard primrec proofs) but requires no new ideas.  It is unambiguously the next
target; with it, Steel's uniform case per the blueprint above becomes a concrete,
fully-specified formalization plan rather than research.

## Next formal milestones (in dependency order)

1. ~~Pointed perfect trees~~ **Done in the join-cone formulation** (`UniformJoin.lean`).
2. ~~The universal machine for `OracleCode`~~ **DONE (session 4)** — `Evaln.lean`,
   `EvalnPrim.lean` (`evaln_prim`), `Universal.lean` (`eval_universal`,
   `exists_fixedPoint`).  The oracle recursion theorem, s-m-n, padding, Σ₁-completeness
   of the jump, and the full Shoenfield limit lemma are all now proved.
3. **Lachlan's theorem** — the modern Bard–Lutz proof, now scoped precisely (session-5
   research + groundwork).  **Key correction:** it needs *no* recursion theorem; the core
   is s-m-n + the universal machine + join + Post's Σ₁ theorem — all present.  Determinacy
   enters only in the final "on a cone" wrapper.  Three pieces:
   - **(L1) computable uniformity** (Bard Lemma 3.4): its linchpin — computable composition
     of functionals `Φ_i^{Φ_j^X} = Φ_{i∗j}^X` — is **already in the codebase** as
     `trOracle`/`eval_trOracle` (`Jump.lean`) with the index map primrec (`trE_primrec`),
     now packaged as `OracleCode.eval_trE_comp` (`UniformFunctionals.lean`).  What remains
     of L1 is the fixed-word semigroup calculation with a handful of concrete machines.
   - **(L2) local dichotomy** (Lutz Thm 3.10): the `y_e` diagonalization — build a real
     `y_e ≡ᵀ X` (via bounded simulation: `y_e(m)` copies `X(m)` unless `Φ_e^X(e)` halts
     within `m` steps, then splices a `τ`-witness) with `n∈W^{y_e} ⟺ Φ_e^X(e)↓`, so a
     computable uniformity function lets `Wˣ` decide `X′`.  **This is the irreducible hard
     core** — a genuine oracle-machine construction on the scale of the effective-KP build.
   - **(L3) assembly**: the easy half `Wˣ ≤ᵀ X′` is **done** (`ReOperator.reReal_le_jump`,
     Post Σ₁); Bard Fact 3.1 is **done** (`Cantor.joinFam_le`); the continuous case
     `Wˣ ≤ᵀ X⊕0′` is now **DONE** (`ContinuousCase.continuous_case`): the `μ`-search over
     prefix lengths, both tests `0′`-decidable (`haltsOn_recursiveIn_jump`,
     `extHaltsFrom_recursiveIn_jump`), the prefix `X`-computable (`graphEnc`), assembled over
     `{toPFun X, jumpFn ∅}` and cut to `join X 0′` via `Nat.RecursiveIn.subst`, with
     correctness kernel `decisive_answer`.
   Groundwork complete this session: `eval_trE_comp`, `joinFam_le`, `le_iff_bitg`,
   `reReal`/`reReal_le_jump`/`reReal_eq_of_reduces`, the operator use principle +
   monotonicity + openness (`OperatorLocal`), and `extHaltsFrom_recursiveIn_jump`
   (`ContinuousCase`).  Honest path: thread computable uniformity as an explicit hypothesis
   (like determinacy) and prove L2+L3; then discharge it via L1.  Refs: Lutz thesis Ch. 3;
   Bard arXiv:1907.10766; Nakid-Cordero arXiv:2510.19147 Lemma 4.2.
4. **Steel's uniform case** — extends Lachlan to arbitrary (non-r.e.) uniformly-invariant
   functions; genuinely needs determinacy (a prewellordering/rank argument).  Larger.
5. **Posner–Robinson** (Kumabe–Slaman forcing) — the remaining pillar for the
   Slaman–Steel and Lutz–Siskind theorems in full.
6. ~~**Effective Kleene–Post** (incomparable degrees `≤ᵀ 0′`)~~ **DONE (session 5)** —
   `EffectiveKP.effective_kleene_post`; the `0′`-recursive finite-extension construction is
   fully built (`condN` via `prec` over the encoded step `reqStepEnc`), with the
   intermediate-degree corollary `∅ <ᵀ A <ᵀ 0′` (`exists_intermediate_degree`).
