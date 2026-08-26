# Value-cleanup no-go (Task A) + independence assessment (Task B)

*Session 2026-08-26. Two genuine advances on the two tasks, both grounded in fresh
primary-source research (Nakid-Cordero arXiv:2510.19147 v2, read in full; Lutz–Siskind
arXiv:2305.19646; Lutz thesis Ch.5,7) and one new machine-checked file
(`ValueCleanup.lean`, 6 theorems, standard axioms only). Not a solve; honest scope below.*

---

## TASK A — value-cleanup: a VALUE-side no-go, machine-checked

### The result (`MartinsConjecture/ValueCleanup.lean`)

`CanonicalRepresentative.lean` already proved the **input-side** no-go
(`canonicalRepresentative_no_gain`): precomposing `F` with a fixed
uniformly-degree-preserving computable coding `c` is uniformity-*neutral*
(`F∘c` uniform ⟺ `F` uniform). So the obstruction lives in `F`'s **values**, and
value-cleanup (replace `F x` by `G x ≡ᵀ F x`, using `x`) is the only lever.

This session closes the natural value-side attempt. The most general
Martin-equivalence-preserving value-cleanup is a fixed binary operation
`G x = Ψ x (F x)` with `Ψ x y ≡ᵀ y` (value-preserving). Machine-checked verdict
(`valueCleanup_no_gain`, standard axioms):

> For any **fixed** binary uniformly-invariant, value-preserving `Ψ`, the cleanup
> `G x = Ψ x (F x)` is Martin-equivalent to `F` and **uniformly invariant iff `F`
> is**. A fixed degree-preserving value reprocessing can neither create nor destroy
> the uniformity obstruction.

Components:
- `martinEquiv_valueCleanup` — value-preserving ⟹ `G x ≡ᵀ F x` pointwise (Martin-equiv free).
- `uniform_valueCleanup_of_uniform` (**forward**) — if `F` uniform via `u`, the missing
  second-argument witness `(k,l)=u(i,j)` is a computable function of `(i,j)`, so `Ψ`'s
  binary transformer composed with `u` uniformizes `G`. **`Ψ` can only forward `F`'s
  witness; it cannot manufacture one.**
- `uniform_of_uniform_valueCleanup` (**converse**) — value-preserving via fixed `(p,q)`
  ⟹ `F x ≡ᵀ G x` via fixed indices, so `G`'s transformer conjugates (through the
  computable composition `EquivVia.trans_trE`) into an `F`-transformer.

### Closing the dichotomy (machine-checked)

The theorem's hypotheses are *value-preserving* (degree-preserving) `Ψ`. What if the
cleanup **uses `x` to change the degree** (e.g. the join `Ψ x y = x ⊕ y`, which could
carry `x`'s reduction data)? Then it **breaks Martin-equivalence on the open core**:

- `join_cleanup_breaks_equiv` — if `F x ⊥ᵀ x` then `x ⊕ F x ≢ᵀ F x` (else
  `x ≤ᵀ x⊕F x ≡ᵀ F x`, contradicting incomparability).
- `join_not_valuePreserving_on_incomparable` — no fixed `(p,q)` witnesses
  `ValuePreserving` for the join at incomparable `X`.

**Complete trichotomy for value-cleanups `G x = Ψ x (F x)`:**
1. `Ψ` fixed & degree-preserving ⟹ **neutral** (`valueCleanup_no_gain`).
2. `Ψ` degree-changing (uses `x`) ⟹ **breaks Martin-equivalence** in the incomparable
   core (`join_cleanup_breaks_equiv`).
3. `Ψ` non-uniform ⟹ the cleanup is **as hard as Steel's conjecture** (it must itself
   supply the non-invariant reduction data).

### Honest scope
This does **not** refute Steel's conjecture — it sharpens the obstruction. Together
with the input-side result it shows: *neither input reparametrization nor fixed
value-preserving reprocessing can uniformize a non-uniform `F`.* The cleanup would
have to be non-uniform itself (case 3) — i.e. it must already solve the problem. This
is the precise, machine-checked form of the circularity (W6) for the value-cleanup
route, and it is genuinely new (the prior repo result covered only the input side).

---

## The Task-A ↔ Task-B bridge (a new reformulation)

Nakid-Cordero's proof (Thm 6.6) that the **e-degree sideways function has NO uniform
equivalent** proceeds by: a uniform Borel equivalent `H` would (via their Lemma 6.4,
constancy on each K-pair degree) yield a **Borel choice-of-index** `R(X) = least n with
X = Γ_n(H(H(X)))`, which **well-orders each e-degree in type ω** — contradicted by
genericity: for a generic `G` and a one-bit flip `G*`, the left cuts satisfy
`L_G ≡_e L_{G*}` but `L_G ≠ L_{G*}` as reals, so `R` cannot consistently choose.

**This is exactly the value-cleanup selector of Task A.** A uniform `G ≡ᵀ F` gives (by
the MSS bridge: "≡_m a uniformly invariant function ⟺ uniform on a pointed perfect
tree") a canonical/uniform reduction-index selector on a cone. So:

> **Steel's Conjecture ⟺ every Turing degree (on a cone) admits a uniform selection of
> a reduction-index for `F`'s values that survives the degree's internal generic
> symmetries.** The e-analogue *fails* because K-pair-half e-degrees carry a genericity
> symmetry (`L_G ≡_e L_{G*}`, distinct reals) with no invariant selector.

**Honest caveat (self-scrutiny).** Turing degrees trivially contain `2^ℵ₀` distinct
reals, so "distinct e-equivalent reals" is not per se the obstruction. The e-specific
content is that the *selector R is forced to be constant on the degree* (Lemma 6.4, via
Thm 5.1's increasing-or-constant), so the choice must be **degree-uniform**, and the
left-cut genericity then kills it. The Turing analogue of "R constant on the degree" is
exactly uniform invariance; whether a *left-cut-style genericity symmetry* obstructs a
Turing selector is **open** — but the structural facts below say the e-obstruction's
engine is ABSENT in D_T. So this bridge explains *why the e-case fails* and *why the
Turing case is expected to hold*, without claiming a proof.

---

## TASK B — is Part 1 independent of ZF+AD, or false? Honest verdict: NO evidence for either; structural evidence AGAINST.

### The two known ways Part 1 fails, and what each needs

| Failure route | Theorem | What it needs | Available in D_T under AD? |
|---|---|---|---|
| ZFC counterexample | Lutz thesis Thm 5.27 | a **wellordering of the degrees** (write D_T as an increasing wellordered union of countable ideals) | **NO** — AD refutes any wellorder of ℝ |
| e-degree counterexample | Nakid-Cordero Thm 6.6 (a **ZF** theorem) | **nontrivial Kalimullin pairs** + **non-total (quasiminimal) degrees** | **NO** — provably absent in ZF |

### Why the e-failure is NOT evidence the Turing case fails (the key finding)

The e-degree counterexample is the **exact analogue of the Turing incomparable core**:
`F(A) = B` with `B ⊥_e A` (K-pair halves are quasiminimal, form a minimal pair). One
might fear this signals the Turing incomparable core could also fail. It does **not**,
for a precise ZF-provable reason:

- **Nontrivial K-pairs collapse in D_T.** The two halves `{A, Ā}` of a semicomputable
  pair are **Turing-equivalent** (`Ā ≤_T A` trivially — complement is computable). In
  the e-degrees they have *different* degrees, each quasiminimal, forming the K-pair.
  The whole engine of the counterexample (Lemma 6.4, on nontrivial K_U-pairs with
  `A >_e U`) **cannot even be stated** in D_T. [Jockusch; Cai–Ganchev–Lempp–Miller–
  Soskova, JAMS 2016.]
- **The "sideways" third case is a non-total artifact.** Nakid-Cordero Thm 5.1 gives
  uniform e-functions "constant, increasing, **or above the skip**"; the skip case is
  "the only part of the argument where negative information is necessary" and **collapses
  to the jump on total (= Turing) degrees** (Cor 5.5). So Slaman–Steel's clean
  "constant or increasing" (no sideways) is exactly what totality buys.

**Conclusion.** The e-degree failure exploits precisely the structure D_T lacks
(non-totality, K-pairs). Far from suggesting the Turing case fails, it shows the Turing
case is *protected* by two ZF facts (K-pair collapse, totality) plus one AD fact (the
Cone Theorem, which holds in D_T under AD but fails in D_e in ZF). This is genuine
structural evidence *against* independence/falsity.

### The genuine residual axiom question (honest)

- **"Part 1 fails" is a ZFC theorem** (Thm 5.27). So it has no consistency strength;
  the content is all on the "Part 1 holds" side, which needs ≥ Turing Determinacy.
- **Known partial proofs consume choice-substitutes:** Lutz–Siskind order-preserving
  Part 1 is a theorem of **ZF + AD + DC_ℝ** (Thm 3.7) — *correcting the repo memory's
  "AD + Uniformization_ℝ"*: DC_ℝ suffices via modulus *sequences* (Lemma 5.17);
  Uniformization_ℝ is only needed for the slicker first proof and the RK reformulations.
  Whether **plain AD** suffices (drop DC_ℝ) is **open** ("We do not know if ... in
  ZF + AD", Lutz–Siskind after Lemma 3.3).
- **The incomparable core has no proof under ANY determinacy hypothesis**, including
  AD_ℝ / AD⁺. But **no model of AD is known where Part 1 fails, and no one conjectures
  it independent of AD.** Consistency ordering (confirmed): `AD ≡ AD+DC_ℝ <
  AD+Uniformization_ℝ ≤ AD_ℝ < AD_ℝ+DC < ...`; `AD_ℝ ⟺ AD + DC_ℝ + Uniformization_ℝ`
  (Woodin–Martin, logical equivalence).

### Verdict for Task B
Part 1 is **not refutable from ZF+AD** (both known failure routes need something AD
denies or D_T structurally lacks) and is **not known/conjectured independent of AD**.
The field's — and this analysis's — working assessment is that it is **true under AD**,
with the genuine open content being the RK-rigidity of `U_M` (inner-model theory,
Steel/Siskind). The residual *axiom-strength* question (does the incomparable core need
DC_ℝ / Uniformization_ℝ, or plain AD?) is open but is a question of *proof strength*,
not of independence/falsity. **No "half-way between AD and AC" hypothesis is known to
resurrect a counterexample** while keeping AD's regularity — the counterexample needs a
wellorder of ℝ (full-choice-flavored), which any such hypothesis strong enough to build
it would have to supply, contradicting AD's perfect-set property.

---

## Net honest bottom line
- **Task A:** machine-checked value-side no-go (`ValueCleanup.lean`) — fixed
  degree-preserving value-cleanup is neutral; degree-changing breaks Martin-equivalence
  in the core; only a non-uniform cleanup (= solving the problem) remains. Plus a new
  reformulation of Steel's conjecture as a *degree-uniform reduction-index selector*
  question, connected to Nakid-Cordero's e-degree obstruction.
- **Task B:** honest, sourced verdict — Part 1 is not independent of / false under
  ZF+AD by any known mechanism; the e-degree failure is powered by structure (K-pairs,
  non-totality) that is ZF-provably absent in D_T, constituting evidence *for* the
  Turing conjecture. Corrected the repo's axiom claim: order-preserving Part 1 is
  ZF+AD+DC_ℝ, not requiring Uniformization_ℝ.
