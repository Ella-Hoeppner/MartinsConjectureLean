# Blueprint: Martin's Conjecture in Lean 4 / Mathlib

Start: 2026-08-13, ~12:20 EDT. Toolchain: Lean 4.34.0-rc1, Mathlib master (rev pinned in lakefile).

## T0 audit results

Present in Mathlib (2026-08):
- `Mathlib/Computability/RecursiveIn.lean` (Duve–Roth, 2025): `Nat.RecursiveIn (O : Set (ℕ →. ℕ)) (f : ℕ →. ℕ) : Prop` — inductive, Odifreddi-style
  (constructors zero/succ/left/right/oracle/pair/comp/prec/rfind). Lifted `RecursiveIn`/`ComputableIn` for `Primcodable` types.
  API is *thin*: monotonicity/subst/partrec embedding only; **no closure lemmas** (no cond, no ite, no curry).
- `Mathlib/Computability/TuringDegree.lean`: `TuringReducible f g := RecursiveIn {g} f` (notation `f ≤ᵀ g`, scoped `Computability`),
  `TuringEquivalent` (`≡ᵀ`), preorder instance, `TuringDegree := Antisymmetrization` with `PartialOrder`.
- `Mathlib/Computability/PartrecCode.lean`: Gödel numbering `Nat.Partrec.Code` for *unrelativized* partial recursive functions,
  `eval`, `exists_code`, smn (`curry`), universal machine (`evaln`), fixed point, halting problem (in `Halting.lean`).
- `Mathlib/SetTheory/Descriptive/Tree.lean` only — **no determinacy in Mathlib** (no Gale–Stewart, no Borel determinacy).

Absent (= our work): oracle Gödel numbering, the jump, jump strictness, join/upper-semilattice on points of Cantor space,
cones, degree-invariant functions, Martin order ≤ₘ, any statement of Martin's conjecture.

## Oracle-computation representation (THE design decision)

**Chosen**: keep Mathlib's `Nat.RecursiveIn {g}` as the *definition* of `≤ᵀ` (don't fork the definition — theorems then
live in Mathlib's language and are upstreamable). Add a Gödel numbering for it:

```
inductive OracleCode | zero | succ | left | right | oracle | pair | comp | prec | rfind
evalo (O : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
exists_code : Nat.RecursiveIn {O} f ↔ ∃ c, evalo O c = f
```

Deviations from Mathlib's `Nat.Partrec.Code`, and why:
- extra `oracle` constructor (the point);
- `rfind` instead of `rfind'` (with offset): the eval clause then matches `Nat.RecursiveIn`'s `rfind` constructor
  *constructor-for-constructor*, making `exists_code` a short structural induction in both directions.
  Cost: `rfind'` is what you want for a step-indexed universal machine (`evaln`); we skip the universal machine in this
  run (not needed for jump strictness — see below), so plain `rfind` is strictly simpler. Documented for upstreaming.
- own numeric encoding `encodeCode : OracleCode → ℕ` (zero↦0, succ↦1, left↦2, right↦3, oracle↦4; composites
  `4*pair(a,b) + (5|6|7)` for pair/comp/prec, `4*pair(a,0)+8` for rfind), total decoding `ofNatCode : ℕ → OracleCode`,
  round-trip `ofNatCode (encodeCode c) = c`. Encoding need not be injective-onto; only the round-trip and
  primrec-ness of constructor arithmetic matter.

**Key insight that makes T1 cheap** (avoids porting the ~1000-line universal-machine development):
- `¬(O′ ≤ᵀ O)` needs only `exists_code` (completeness) + diagonalization — no code arithmetic at all.
- `O ≤ᵀ O′` needs a *primrec family* of codes k(n,m) = code for "compute O(n), halt iff = m", then
  `O(n) = rfind m [jump answers yes at k(n,m)]` via the `rfind` constructor. Requires only `encodeCode`-level
  primrec arithmetic for `const`/`comp`/`pair` — NOT `Primrec ofNatCode`, NOT `evaln`.
- Constants chosen per-oracle may be `Classical.choose`-noncomputable: `Primrec.const` doesn't care.
  (E.g. the fixed "equality test" code c_eq is chosen via `exists_code` from a `Partrec` proof, per oracle O.)

## The jump

```
jumpP (O : ℕ →. ℕ) : ℕ → Prop := fun e => ((evalo O (ofNatCode e)) e).Dom   -- diagonal halting
jumpFn O : ℕ →. ℕ := fun e => Part.some (if jumpP O e then 1 else 0)          -- total 0/1 function (classical)
```
The jump of anything is a *total* 0/1 function = a point of Cantor space, as it should be.

## Dependency graph / file plan

1. `OracleCode.lean` — codes, evalo, exists_code, const, encode/decode + round-trip, primrec arithmetic lemmas.
2. `Jump.lean` — jumpP/jumpFn; `jump_not_turingReducible_self : ¬(jumpFn O ≤ᵀ O)`; `turingReducible_jump : O ≤ᵀ jumpFn O`;
   strictness; sanity anchors (∅′ uncomputable: `¬Nat.Partrec (jumpFn O)` for partrec O ⊇ the classical statement).
3. `CantorPoints.lean` — `ℕ → Bool` as degree-theory carrier: `toPFun`, `≤ᵀ`/`≡ᵀ` on points, join `X ⊕ Y`
   (even/odd interleaving; lub proofs use totality via the `prec` constructor trick), jump on points.
4. `Martin.lean` (T2) — cones, "on a cone", degree-invariant, order-preserving, uniformly DI, Martin order ≤ₘ,
   Borel = `Measurable` for the product σ-algebra on `ℕ → Bool`; formal statements of Part I, Part II,
   uniform and order-preserving variants; Lachlan statement.
5. `ConeTheorem.lean` (T3) — games on 2^ω with strategies `List Bool → Bool`, determinacy of a payoff set as an
   explicit *hypothesis*, Martin's cone theorem. (No determinacy is provable from Mathlib today; Sven Manthe's
   Borel-determinacy repo is external prior art — see research notes.)
6. Stretch: jump is (uniformly) degree-invariant / order-preserving — needs primrec code-translation
   (strong-recursion on encodings via `Primrec.nat_strong_rec`); scheduled last, may be `sorry`-scaffolded.

## Sanity anchors (anti-fooling)

- `∅′ ≰ᵀ ∅`: jumpFn of a partrec oracle is not partrec. [proved via strictness]
- `X ≤ᵀ X′` [proved, non-vacuous: uses genuine rfind search]
- `Partrec f ↔ f ≤ᵀ (zero oracle)` [Mathlib: partrec_iff_forall_turingReducible etc.]
- computable points are exactly the bottom degree on Cantor points.
