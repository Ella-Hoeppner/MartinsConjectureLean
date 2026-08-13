# Task Brief: Martin's Conjecture in Lean 4 / Mathlib

## Mission

Attempt formal progress on **Martin's conjecture** (also called the Martin conjecture on degree-invariant functions) using Lean 4 with Mathlib. A full proof or disproof is a moonshot and is **not** the success criterion. Work through the tiered goals below in order; each tier is independently valuable, and several would constitute novel formalization work. Your final deliverable is compiling Lean code plus an honest written report of exactly what was and wasn't achieved.

Do your own literature research (web search, arXiv) rather than trusting this brief's mathematical summaries blindly. This brief orients you; the papers are ground truth.

---

## Mathematical background

Work in Cantor space 2^ω (equivalently, subsets of ℕ / reals).

**Turing reducibility.** X ≤ᵀ Y iff X is computable by a Turing machine with oracle access to Y. X ≡ᵀ Y iff both directions hold. Equivalence classes are **Turing degrees**. The partial order of degrees is denoted 𝒟.

**The jump.** X′ = the halting problem relativized to X = {e : Φₑˣ(e)↓}, where Φₑˣ is the e-th oracle machine with oracle X. Key facts: X <ᵀ X′ (jump strictness), and the jump is degree-invariant and order-preserving on degrees. Iterates: X″, X‴, and transfinite iterates X^(α) for computable ordinals α via effective transfinite recursion.

**Cones.** The cone above Y is {X : X ≥ᵀ Y}. "Property P holds on a cone" means ∃Y ∀X ≥ᵀ Y, P(X). Cones are the "large" sets in this subject; "on a cone" plays the role of "almost everywhere."

**Degree-invariant function.** F : 2^ω → 2^ω is degree-invariant (DI) iff X ≡ᵀ Y ⟹ F(X) ≡ᵀ F(Y).

**Order on DI functions.** F ≤ₘ G iff F(X) ≤ᵀ G(X) on a cone. F ≡ₘ G iff F(X) ≡ᵀ G(X) on a cone.

**Uniformly degree-invariant.** F is uniformly DI iff there is a computable function u such that whenever i, j are indices witnessing X ≡ᵀ Y (i.e., Φᵢʸ = X and Φⱼˣ = Y), u(i,j) codes indices witnessing F(X) ≡ᵀ F(Y). (Check the exact convention in the literature — index-pair coding varies by author.)

**Order-preserving.** F is order-preserving iff X ≤ᵀ Y ⟹ F(X) ≤ᵀ F(Y). (This implies DI.)

---

## The conjecture

Originally stated by D. A. Martin in ZF + DC + AD (the axiom of determinacy). It has two parts. Informally:

**Part I.** Every DI function F : 2^ω → 2^ω is either (a) constant on a cone (∃C such that F(X) ≡ᵀ C on a cone), or (b) above the identity on a cone (F(X) ≥ᵀ X on a cone).

**Part II.** The DI functions satisfying (b), ordered by ≤ₘ, are prewellordered, and the successor of F in this order is the jump composed with F, i.e., X ↦ F(X)′. Consequence: on a cone, the only DI functions are (up to ≡ₘ) the constants, the identity, and the (transfinite) iterates of the jump.

Interpretation: every "reasonable" (definable, coding-independent) operation on computational-difficulty levels is an iterate of the halting-jump; there is no definable degree-invariant way to land strictly between a degree and its jump.

---

## ⚠️ Set-theoretic framing — read this before writing any Lean

**Do NOT axiomatize AD.** Full AD is inconsistent with the axiom of choice, and Lean/Mathlib assumes choice globally (`Classical.choice`). Adding AD as an axiom lets you derive `False`, from which you can "prove" Martin's conjecture and its negation and everything else. Any result whose `#print axioms` output shows a custom axiom is worthless. If you need a determinacy hypothesis beyond what's provable, thread it through as an explicit **hypothesis of the theorem statement**, never as a global axiom.

The correct ZFC-compatible target is the **Borel version**: restrict F to Borel functions. Borel determinacy is a ZFC theorem (Martin 1975), so "Martin's conjecture for Borel functions" is a well-posed ZFC statement, and this is the version modern partial results (e.g., Lutz–Siskind) are proved in. The uniformly-invariant special cases need even less.

---

## Known landmarks (candidate formalization targets, roughly increasing difficulty)

1. **Jump strictness and basic degree theory.** X <ᵀ X′; jump is DI; ≤ᵀ is a preorder; degrees form an upper semilattice.
2. **Martin's cone theorem** (a.k.a. Martin's lemma): every degree-invariant *set* D ⊆ 2^ω that is determined (in particular, every Borel DI set, via Borel determinacy) either contains a cone or is disjoint from a cone. Proof is short *given* determinacy: the winner's strategy in the game for D is itself an oracle generating the cone. This is the workhorse of the whole subject.
3. **Lachlan (1975).** There is no *uniformly* DI solution to Post's problem — no uniformly DI F with X <ᵀ F(X) <ᵀ X′ on a cone. Proof is recursion-theoretic (recursion theorem trickery), needs no determinacy beyond arithmetic facts. **Probably the most tractable named theorem here.**
4. **Steel (1982); Slaman–Steel (1988).** Parts II and I respectively for *uniformly* DI functions.
5. **Lutz–Siskind (c. 2020–2024).** Part I for *order-preserving* Borel functions (ZFC), plus consequences (e.g., ruling out order-preserving Borel solutions to Post's problem). Also see Patrick Lutz's thesis, "Results on Martin's Conjecture" (Berkeley, 2021) — likely the best single modern exposition.
6. **Survey:** Marks–Slaman–Steel, "Martin's conjecture, arithmetic equivalence, and countable Borel equivalence relations." Fetch and read this early.

Classic textbook grounding: Soare (*Turing Computability*), Odifreddi (*Classical Recursion Theory*).

---

## Step 0: Mathlib audit (do this first, ~before any proving)

Survey `Mathlib.Computability.*` and anything else relevant. Expected state (verify — do not trust this list):

- Present: Turing machine models, primitive/partial recursive functions (`Nat.Partrec`), Gödel numbering (`Nat.Partrec.Code`), the unrelativized halting problem, many-one reducibility (`Computability/Reduce`), possibly a `TuringDegree` stub via `turingReducible` — check whether it's substantive or skeletal.
- Almost certainly absent: **oracle computation** in usable form, the **jump**, jump strictness, cones, anything about DI functions. Descriptive set theory: Mathlib has Polish spaces and Borel hierarchies (`MeasureTheory`, `Descriptive`?) — audit what's usable. **Borel determinacy is very likely not formalized in Mathlib or anywhere; check** (search Mathlib, the Lean Zulip archives, and GitHub for prior art — also for any community degree-theory projects). Gale–Stewart / open determinacy may exist in some form.

The single biggest infrastructure decision is **how to represent oracle computation**. Options include relativizing `Nat.Partrec.Code` (add an oracle query constructor), or defining Turing functionals via monotone use-bounded approximations. Pick whichever integrates best with existing Mathlib machinery, and document the decision and its tradeoffs in the blueprint before committing. A wrong choice here poisons everything downstream.

## Tiered goals

- **T0 — Audit + blueprint.** Complete the audit. Write `blueprint.md`: definitions to build, dependency graph, chosen oracle-computation representation, target statements in informal math + intended Lean signatures.
- **T1 — Relativized computability core.** Oracle machines / Turing functionals; ≤ᵀ as preorder; degrees as quotient; join; the jump; **jump strictness** (this is the keystone sanity theorem — if you can't prove X <ᵀ X′, the definitions are wrong); jump is order-preserving and DI. Optional but valuable: Kleene–Post incomparable degrees below 0′.
- **T2 — State the conjecture.** Formal Lean statements of Part I and Part II, Borel version, plus the uniformly-DI and order-preserving variants. Getting these *statements* right, reviewed against the literature, is likely **novel** — no known prior formalization.
- **T3 — Martin's cone theorem.** If any determinacy is available or buildable, prove the cone theorem at whatever level of the Borel hierarchy you can (even the clopen/open-determinacy version of the cone theorem is worthwhile). Otherwise prove it with determinacy-of-the-relevant-game as an explicit hypothesis.
- **T4 — A named special case.** Lachlan's theorem is the recommended target (pure recursion theory, no determinacy). Alternatively any self-contained lemma cluster from Steel / Slaman–Steel / Lutz–Siskind.
- **T5 — Moonshot.** Only after T1–T4: attempt anything novel — an extension of a known special case, or exploration of counterexample space. Note for counterexample hunters: any candidate DI solution to Post's problem must be *non-uniform* (Lachlan) and *non-order-preserving* (Lutz–Siskind), which is exactly why nobody has found one. Treat any apparent breakthrough per the anti-fooling checklist.

## Working practices

- Standard `lake` project pinned to current Mathlib; run `lake build` frequently; keep everything compiling.
- Maintain `blueprint.md` (the plan) and `LEDGER.md` (every `sorry`, why it's there, plan to discharge it).
- Many small lemmas over monolithic proofs. Scaffold with `sorry`, then fill, hardest-first within each tier.
- When stuck on one lemma after serious attempts, record the obstruction in the ledger and move on; don't burn the whole budget on one wall.
- Definitions are the dangerous part, not proofs. Before building on a definition, write 2–3 sanity lemmas exercising it (see checklist).

## Anti-fooling checklist (apply before claiming anything)

1. `#print axioms` on every headline theorem. Only standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) allowed. Any custom axiom ⟹ result is void.
2. Vacuity checks: a slightly-wrong definition of ≤ᵀ can make theorems trivially true. Sanity anchors: ∅′ ≰ᵀ ∅ (unrelativized halting problem is genuinely uncomputable in your encoding); X ≤ᵀ X′; many-one reducibility implies Turing reducibility but not conversely; computable sets form exactly degree 0.
3. If you believe you've proved or refuted Martin's conjecture: you almost certainly haven't. Write the argument out in *informal prose*, identify precisely which known-open case it settles, check it against Lachlan / Steel / Slaman–Steel / Lutz–Siskind, and hunt for the error (most likely: a definition that doesn't mean what you think, an accidentally-inconsistent hypothesis, or a vacuous quantifier). Only after the informal argument survives your own adversarial review should you present it as a claim — and even then, label it "candidate result, needs expert review."
4. Never claim "proved" for anything containing `sorry`, and say so explicitly in the report for anything that does.

## Final report must include

What compiles sorry-free (with `#print axioms` output), what's scaffolded, the oracle-computation design decision and why, which tier was reached, obstructions hit, honest assessment of novelty (T2 statements formalized for the first time? which sanity lemmas pass?), and concrete next steps for a future run. No overclaiming — an accurate "we built relativized computability and formally stated Martin's conjecture" is a genuinely good outcome.