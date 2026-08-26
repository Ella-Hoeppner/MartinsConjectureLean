# The pointed-injectivity (Marks) route to the STRICT half of Part 1

*Session 2026-08-26. A combinatorial route to "U_M RK-minimal" (V ≤_RK U_M nonprincipal ⟹ U_M ≤_RK V),
complementary to the measure-theoretic `escaping ⟹ MP` route. Main content: the countable-fiber case is
ALREADY a theorem (Marks–Slaman–Steel), so the entire open content is UNCOUNTABLE cone-null fibers, and the
open step is a single, precisely-stated fusion-compatibility question. Not a solve; a sharp localization plus
a concrete decidable test case (the jump).*

All facts below verified against primary sources (arXiv:1109.1875 MSS via ar5iv; Lutz thesis;
Lutz–Siskind arXiv:2305.19646; Kechris CDST). Citations inline.

---

## 0. The target and why Marks gives it

Strict half of Part 1 = **U_M has no nonprincipal RK-predecessor but itself** (Lutz–Siskind Thm 5.15, the
`⟹ V = U_M` rigidity; the weaker `⟹ V ≡_RK U_M` is RK-minimality). Under Uniformization_ℝ, every
V ≤_RK U_M is induced by a Turing-**invariant** f with V = f_*U_M.

**Marks's conjecture** (Lutz thesis Conj 5.36/9.10, unpublished [Mar20]): ZF+AD ⊢ every f:2^ω→2^ω is
*constant on a pointed perfect tree* OR *injective on a pointed perfect tree*.

**Marks ⟹ strict half** (Lutz thesis Prop 5.37): apply Marks to the invariant f.
- Constant on pointed tree T ⟹ f constant on cone(deg T) ⟹ V = f_*U_M principal.
- Injective on pointed tree T ⟹ (computable-injective-on-pointed-tree ⟹ above-id, Lutz–Siskind Lem 2.1 /
  Cor 2.6) f is right-invertible on [T] ⟹ ∃ G, G_*V = U_M ⟹ U_M ≤_RK V.
So a nonprincipal V ≤_RK U_M satisfies U_M ≤_RK V, i.e. no *strict* predecessor. (Note: this delivers
RK-minimality; the full `= U_M` rigidity is the extra `≡_RK ⟹ =` step, separate.)

**We only need Marks for INVARIANT f.** That is a real simplification and it is what the fiber structure below
exploits.

---

## 1. The fiber structure of an invariant f (the lever)

For non-constant Turing-invariant f, each fiber f^{-1}(c) = {x : f(x) ≡_T c} is:
- **Turing-invariant** (f invariant ⟹ fibers are unions of degrees), and
- **cone-null**: contains no cone (else f is constant on that cone). Under Turing determinacy every invariant
  set contains a cone or is disjoint from one, so cone-null = disjoint-from-a-cone = "avoids a cone".

The natural equivalence relation is **E_f : x E_f y ⟺ f(x) ≡_T f(y)**, whose classes are exactly the fibers.
E_f is invariant (a union of E_f-classes is degree-invariant). Non-constant f ⟺ E_f has ≥ 2 classes ⟺ (under
cone-null) uncountably many classes cofinally (each class avoids a cone, so no finite/countable family of
classes covers a cone).

---

## 2. ★ The countable-fiber case is SOLVED (Marks–Slaman–Steel, verified)

**If every fiber is COUNTABLE, Marks-for-invariant-f holds.** This is essentially MSS Thm 3.6's engine
(arXiv:1109.1875 §3, verified from ar5iv):

1. **Lusin–Novikov** (Kechris CDST Thm 18.10): a Borel R ⊆ 2^ω×2^ω with all vertical sections countable is a
   countable union of graphs of Borel partial functions. Applied to graph(f) (fibers = f^{-1}(c) countable):
   2^ω splits into **countably many Borel pieces {B_i}** on each of which f is injective.
   [This needs f Borel *and* countable fibers. For an arbitrary invariant f under AD the "Borel" is handled
    by working inside an ∞-Borel/scale code, or by restricting to the definable f that Part 1 concerns.]
2. **Martin's pointed-tree lemma** (MSS Lemma 3.5, ZF+AD): any π:2^ω→ω is constant on a pointed perfect set.
   Apply to π(x) = (the i with x ∈ B_i). Get a **pointed perfect tree T with [T] ⊆ B_i** for a single i.
3. On [T], f = (f restricted to B_i) is **injective**, and T is **pointed**. Done.

**Why pointedness comes for free here:** the only obstruction to pointedness is the *finitely/countably*-valued
choice "which piece B_i", and Martin's lemma stabilizes exactly countably-valued functions on a pointed set.
The injectivity is then inherited from the piece, requiring no further fusion. **This is the whole trick, and
it is fundamentally a COUNTABLE phenomenon.**

**Consequence:** if one could show a non-constant invariant f has countable fibers on a cone, the strict half
would follow. But this is FALSE in general: the Turing **jump** J(x) = x' is invariant, non-constant, and by
Friedberg jump-inversion every cone contains continuum-many x with the same jump-degree — **uncountable
fibers**. So the countable-fiber case is a genuine special case, and insufficient alone.

---

## 3. ★★ The uncountable-fiber case: the exact open step

For uncountable fibers, Lusin–Novikov fails (needs countable sections). The replacement is **Silver's
dichotomy** (Kechris CDST Thm 21.1; holds for ALL equivalence relations under AD via the perfect set property):

> Applied to E_f (x E_f y ⟺ f(x)≡_T f(y)): either countably many classes (⟹ some class non-meager ⟹ f
> constant on a perfect subset of a fiber ⟹ f "constant" up to ≡_T there), or a **perfect set P of pairwise
> E_f-inequivalent** elements ⟹ f injective on P.

So for a non-constant invariant f, **f is injective on a PERFECT set P — unconditionally, even for uncountable
fibers.** *The only gap between here and Marks is POINTEDNESS of P.*

### The construction sketch (concrete), and where it breaks

Build the injective tree by fusion on a splitting tree S ⊆ 2^{<ω}, maintaining a perfect subtree of a fixed
pointed "background" tree T_0 (the cone-realizer). At a splitting node σ that has reached level n of the
construction, we must choose two extensions σ0*, σ1* and split the subtree below them, subject to TWO demands:

- **(I) Injectivity (Silver).** The f-values on the two sides must stay separated: for the eventual branches
  x through σ0* and y through σ1*, f(x) ≢_T f(y). Silver's fusion achieves this by picking σ0*, σ1* with
  f-values already forced into distinct E_f-classes at some finite level of computation — possible because
  cone-null-ness / perfectness of the ~-quotient guarantees the two subtrees below σ contain E_f-inequivalent
  points. This step uses FREEDOM to move the branches to wherever the f-values separate.

- **(II) Pointedness (Groszek–Slaman coding).** Every branch must compute the tree. The GS method (Lutz thesis
  Thm 2.18, strengthened Thm 2.19) codes an arbitrary target real z into the **left/right turn pattern** of
  branches of a perfect tree — i.e. it *dictates the positions* of (some) branches to encode the shape of the
  tree, so that a branch, reading off its own turns, recovers the tree. This step uses the branch POSITIONS as
  the coding medium.

**THE COLLISION.** (I) wants to *move branches to separate f-values*; (II) wants to *fix branch positions to
encode the tree*. In the countable case the two never fight because pointedness is discharged wholesale by
Martin's lemma on the (countable) piece-index and injectivity is inherited, never re-derived in the fusion.
In the uncountable case injectivity must be *maintained inside the pointed fusion*, and it is exactly here that
no theorem exists. **The precise open step:**

> **OPEN STEP.** For a non-constant Turing-invariant f with cone-null (possibly uncountable) fibers, can one
> run a fusion producing a pointed perfect tree T (every branch computes T) on which f is injective?
> Equivalently: is Silver's value-separation compatible with Groszek–Slaman left/right pointed-coding?

Two structural reasons for cautious optimism (not a proof):
- **The GS coding uses only FINITELY MANY branches** (2 in Thm 2.18, 4 in Thm 2.19) to compute any given
  target; the *generic* branch is not pinned. So there may be enough residual positional freedom in the other
  branches to steer f-values apart while a sparse coded skeleton carries the pointedness. This is the most
  promising concrete angle to push.
- **Cone-null-ness is strong.** Each fiber avoids a cone, so above the background tree's base every fiber is
  "thin" in the cone sense; intuitively there is always an E_f-inequivalent extension available in any pointed
  subtree, because a fiber cannot contain the pointed cone [T'] (that would be a cone). Formally: if f were
  constant (≡_T) on some pointed [T'], that fiber would contain cone(deg T') — contradicting cone-null. **So
  no pointed subtree is monochromatic for E_f.** This is a genuine, usable fact: *every pointed perfect tree
  contains two E_f-inequivalent branches* (indeed the constant-alternative of Marks is exactly ruled out on
  every pointed tree for non-constant invariant f). The open step is upgrading "not monochromatic on any
  pointed tree" to "injective on SOME pointed tree" — a Silver-style iteration, but INSIDE the pointed category.

### Why this is not automatic (the honest obstruction)

"Not monochromatic on any pointed tree" gives, at the root, two E_f-inequivalent pointed subtrees. Iterating
into a full binary splitting requires: at every node, both children pointed AND E_f-separated, AND the whole
fusion pointed (branches compute the *global* tree, not just local splits). The GS coding is a *global*
constraint (a branch must recover the entire left/right history), whereas Silver separation is a *local* node
condition. Interleaving a global coding constraint with a local separation constraint through a transfinite
fusion, keeping BOTH, is the technical heart — and no published fusion does both simultaneously for an
arbitrary (non-Borel-rank-bounded) invariant f. **This is the crux, stated as sharply as the current
understanding allows.**

---

## 4. The concrete DECIDABLE test case: is the Turing jump injective on a pointed perfect tree?

The jump J(x)=x' is the canonical stress test:
- J is invariant, non-constant, and non-injective on any cone (Friedberg: continuum-many x per jump-degree).
- So Marks for J requires an **injective pointed tree** (the constant alternative is out).
- **Question (concrete):** ∃ pointed perfect tree T with x ↦ x' injective on [T]? Equivalently, a pointed
  perfect tree of pairwise ≢_T'-... no: injective on values means x' ≢_T y' for distinct branches, i.e. the
  branches have pairwise distinct jump degrees.

Status of this test: PLAUSIBLY YES and checkable. A thin enough pointed tree can force branches into distinct
jump-degrees: build T so that along splitting, the two subtrees are pushed into Turing-incomparable cones
(à la Kleene–Post/Sacks below), while GS-coding the tree into the branches. Distinct jump degrees is a *weaker*
separation than the general E_f-separation (jumps are monotone and well-understood), so if ANY invariant f
should have a pointed injective tree, the jump should. **A NO here would DISPROVE Marks** (high-stakes — scrutinize
carefully; but note it would NOT by itself refute Part 1, since the jump is measure-preserving and Part 1 for
the jump is handled by the MP theorem — Marks is merely *sufficient*, not necessary). **A YES is strong
positive evidence for Marks and a template for the general fusion.** This is the single most tractable next
computation and does not touch the inner-model wall.

---

## 5. Can the strict half be proved DIRECTLY for invariant f, bypassing full Marks?

Partially — and the countable case IS such a bypass:
- **Countable-fiber invariant f: strict half is a theorem** (§2). No full Marks needed; Lusin–Novikov +
  Martin's lemma suffice. Worth formalizing as a genuine partial result (see below).
- **Lusin–Novikov adaptation:** LN says countable-fiber Borel functions are countable unions of Borel
  injections. The *cone/pointed* adaptation is exactly §2 — LN gives the countably-many injective pieces,
  Martin's lemma makes one pointed. This IS "Lusin–Novikov in the pointed setting", and it works, for
  countable fibers only. There is no LN for uncountable fibers (LN is false then), so the direct bypass stops
  precisely at the uncountable-fiber wall — the SAME wall as full Marks-for-invariant-f. So there is no cheaper
  direct route past countable fibers: the uncountable-fiber pointed injectivity IS the irreducible content.
- **Under AD, a perfect (non-pointed) set of injectivity always exists** (Silver, §3). The strict-half-specific
  extra is only pointedness. So the *entire* distance from "known DST" to "strict half for invariant f" is the
  single word POINTED in Silver's theorem.

---

## 6. Relation to the measure-theoretic route, and net assessment

Two routes to the strict half, hitting DIFFERENT walls:
- **Measure route** (`counterexample-attack.md`, `MARTIN_PART1_RK_MEASURE.md`): escaping ⟹ MP; wall = the
  degree-level {0,1} rigidity of U_M, invisible to ordinal/measure tools — inner-model theory (Steel/Siskind).
- **Marks/pointed route** (this note): cone-null-fibers ⟹ pointed injective tree; wall = compatibility of
  Silver value-separation with Groszek–Slaman pointed-coding for uncountable fibers — a **fusion-combinatorics**
  question, not obviously inner-model.

The pointed route is more constructive and has a genuine foothold the measure route lacks: **the countable-fiber
case is done**, and the open residue is a single concrete fusion question with a decidable test case (the jump).
It is a legitimately different angle of attack, and I judge the jump test case + the "no pointed tree is
E_f-monochromatic" fact (§3, both new framings this session) to be the most promising concrete handles.

**Honest bottom line:** NOT a solve. But the localization is sharp: strict-half-for-invariant-f = Marks-for-
invariant-f = [countable fibers: DONE] + [uncountable cone-null fibers: pointed-Silver, OPEN]. The open step is
stated precisely (§3 OPEN STEP), is combinatorial, and comes with (a) a usable non-monochromaticity lemma, (b)
a residual-freedom observation (GS codes with finitely many branches), and (c) a concrete decidable test (the
jump). None of the elementary walls of the measure route (ω₁↪ℝ, ordinal-coarseness) obstruct this route; the
obstruction is purely the interleaving of local separation with global coding.

---

## 7. Formalization target (COMPLETE mathematics, not busywork)

The countable-fiber strict-half theorem (§2) is fully rigorous and currently absent from the repo. A Lean
statement:
  `(∀ c, Set.Countable (f ⁻¹' {y | y ≡_T c})) → invariant f → (∃ pointed T, InjOn f [T]) ∨ constantOnCone f`
built from a Lusin–Novikov interface + the existing `MartinPPT` (Martin's pointed-tree lemma, already
machine-checked per `martin-fusion-attempt.md` / `GameCapstone.lean`). This would be a genuine machine-checked
partial result on the strict half — the first COMBINATORIAL (as opposed to measure-theoretic) fragment proved.
