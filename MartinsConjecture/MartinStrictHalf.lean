/-
**The STRICT half of the RK-rigidity of `U_M`, reduced to a pointed injective tree.**

Part 1's open core = RK-rigidity of the Martin measure `U_M`, which splits (Lutz–Siskind Thm 5.15) into
a **strict half** (`V ≤_RK U_M ⟹ U_M ≤_RK V`, i.e. `U_M` is RK-minimal) and an **equivalence half**
(`U_M ≤_RK V ≤_RK U_M ⟹ V = U_M`).  In `MeasurePreservingCK.lean` the strict half for a pushforward
`V = F_*U_M` was characterized as **dominated-invertibility** `DominatedInvertible F`
(`∃` invariant `g`, `X ≤ᵀ g(F X)` on a cone), via `strictHalf_iff_dominatedInvertible`.

This file formalizes the **countable-fiber fragment** of the strict half.  It introduces a pointed recovery
tree `PointedInjectiveTree F` (a pointed perfect tree realizing a cone with the Lemma-2.1 *recovery*
`x ≤ᵀ F x ⊕ code`) and shows, machine-checked, `PointedInjectiveTree F ⟹ DominatedInvertible F ⟹ StrictHalfFor F`
via the explicit dominating map `g y = y ⊕ code`.  Crucially (`pointedInjectiveTree_fiber_le`), the degree-level
`recover` **forces `F` to be countable-fibered on the cone** — so this interface fits *exactly* the case
Marks–Slaman–Steel already **prove** (countable fibers, `strictHalf_of_countableFibered`), and does **not**
reach the open part of Lutz–Siskind Question 3, which is *uncountable* cone-null fibers (there recovery must be
reals-level).  It is the injectivity analogue of `InvertingTree` (which handled *increasing* `F` by
right-inverting a modulus); here we use only the recovery inequality, so the dominating map is just
"join with the tree code".
-/
import MartinsConjecture.MeasurePreservingCK

open scoped Computability
open OracleCode Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A pointed recovery tree** for `F` (the degree-level, countable-fiber interface).  A pointed perfect
tree (code `code`, branches `mem`) that realizes a cone of degrees, with `F` *effectively recoverable*: the
branch is `≤ᵀ` its `F`-value joined with the tree (`recover`, the Lemma-2.1 domination conclusion applied to
`F`).  By `pointedInjectiveTree_fiber_le` this forces `F` to be **countable-fibered on the cone**, so its
existence is exactly the **MSS-proved countable-fiber case** (not the open uncountable one — for which
recovery would have to be reals-level).  Named `PointedInjectiveTree` because for such `F` a Marks
pointed *injective* tree yields it (via the effective inverse); but the interface only records `recover`. -/
structure PointedInjectiveTree (F : (ℕ → Bool) → ℕ → Bool) where
  /-- The tree code — a real every branch computes. -/
  code : ℕ → Bool
  /-- Membership in the branches `[T]`. -/
  mem : (ℕ → Bool) → Prop
  /-- Pointedness: every branch computes the tree. -/
  pointed : ∀ x, mem x → code ≤ₜ x
  /-- The tree realizes a cone: every degree `≥ᵀ code` is a branch's. -/
  realizes : ∀ d, code ≤ₜ d → ∃ x, mem x ∧ x ≡ₜ d
  /-- Effective injectivity: the branch is recovered from its `F`-value and the tree. -/
  recover : ∀ x, mem x → x ≤ₜ Cantor.join (F x) code

/-- **A pointed injective tree yields dominated-invertibility**, with the explicit invariant dominating map
`g y = y ⊕ code`.  For a degree `d ≥ᵀ code`, realize it by a branch `x ≡ᵀ d`; then
`d ≡ᵀ x ≤ᵀ F x ⊕ code ≡ᵀ F d ⊕ code = g (F d)` (recovery + invariance). -/
theorem dominatedInvertible_of_pointedInjectiveTree (hF : TuringInvariant F)
    (Tr : PointedInjectiveTree F) : DominatedInvertible F := by
  refine ⟨fun y => Cantor.join y Tr.code, ?_, Tr.code, fun X hX => ?_⟩
  · -- `g y = y ⊕ code` is Turing-invariant.
    intro X Y hXY
    exact ⟨Cantor.join_le (hXY.1.trans (Cantor.left_le_join Y Tr.code)) (Cantor.right_le_join Y Tr.code),
           Cantor.join_le (hXY.2.trans (Cantor.left_le_join X Tr.code)) (Cantor.right_le_join X Tr.code)⟩
  · -- On the cone above `code`: `X ≤ᵀ g (F X) = F X ⊕ code`.
    obtain ⟨x, hxmem, hxX⟩ := Tr.realizes X hX
    -- `X ≤ᵀ x ≤ᵀ F x ⊕ code ≤ᵀ F X ⊕ code`  (realize, recover, invariance).
    refine hxX.2.trans ((Tr.recover x hxmem).trans ?_)
    exact Cantor.join_le (((hF x X hxX).1).trans (Cantor.left_le_join (F X) Tr.code))
      (Cantor.right_le_join (F X) Tr.code)

/-- **The strict half from a pointed injective tree** (given `MartinPPT`): `PointedInjectiveTree F`
⟹ `StrictHalfFor F` (`U_M ≤_RK F_*U_M`).  A *sufficient* route: it factors through `DominatedInvertible F`,
to which the strict half is equivalent (`strictHalf_iff_dominatedInvertible`).

**Honest scope (delimited by `pointedInjectiveTree_fiber_le` below): this interface captures exactly the
COUNTABLE-fiber case.**  The `recover` field forces every fiber of `F` restricted to the cone to be *bounded*
(`≤ᵀ F x ⊕ code`), hence countable — so `Nonempty (PointedInjectiveTree F)` implies `F` is countable-fibered,
the case already **proved** by MSS (`strictHalf_of_countableFibered`).  It does **not** reach the open part of
Question 3, which is *uncountable* cone-null fibers (e.g. the jump), where recovery must be *reals*-level
(distinguishing same-degree reals by their `F`-values) rather than the degree-level `≤ᵀ` here.  So this is the
combinatorial-`countable` fragment made an interface, not a reduction of open Q3. -/
theorem strictHalf_of_pointedInjectiveTree (hM : MartinPPT) (hF : TuringInvariant F)
    (Tr : PointedInjectiveTree F) : StrictHalfFor F :=
  (strictHalf_iff_dominatedInvertible hM hF).mpr (dominatedInvertible_of_pointedInjectiveTree hF Tr)

/-- **`recover` bounds the fibers: the interface only fits COUNTABLE-fibered `F`.**  Any two branches `x, y`
with `F y ≡ᵀ F x` satisfy `y ≤ᵀ F x ⊕ code` (recover for `y`, then `F y ≡ᵀ F x`).  So the `F`-fiber through a
branch is bounded by `F x ⊕ code`, hence has only countably many degrees (a degree has countably many
predecessors).  This *delimits* `PointedInjectiveTree`: it exists only when `F` is countable-fibered — exactly
the MSS-proved case — confirming the open Q3 residue (uncountable fibers) lies genuinely outside this
degree-level recovery interface. -/
theorem pointedInjectiveTree_fiber_le (Tr : PointedInjectiveTree F) {x y : ℕ → Bool}
    (hy : Tr.mem y) (h : F y ≡ₜ F x) : y ≤ₜ Cantor.join (F x) Tr.code :=
  (Tr.recover y hy).trans
    (Cantor.join_le (h.1.trans (Cantor.left_le_join (F x) Tr.code)) (Cantor.right_le_join (F x) Tr.code))

/-- **The equivalence half for `F`** (Lutz–Siskind open **Question 4**): if `F_*U_M` is RK-above `U_M`
(`StrictHalfFor F`, so `U_M ≤_RK F_*U_M ≤_RK U_M`) then it equals `U_M` (`F` is measure-preserving).  The
open content is the `g`-inversion gap (`gcomp_mp_recovers`): `g∘F` MP gives `g(F X) ≥ᵀ X`, which does not
force `F` MP. -/
def EquivHalfFor (F : (ℕ → Bool) → ℕ → Bool) : Prop := StrictHalfFor F → MeasurePreserving F

/-- **Both halves ⟹ Part 1** (Lutz–Siskind Thm 5.15: *"a negative answer to Questions 3 and 4 together would
imply Part 1"*), machine-checked.  If every non-constant invariant `F` satisfies the strict half (Q3:
`U_M ≤_RK F_*U_M`) and every invariant `F` satisfies the equivalence half (Q4), then every invariant `F` is
constant-on-a-cone or measure-preserving — Part 1 (in the `escaping ⟹ MP` form).  This is the per-`F`
composition; combined with `partI_iff_escapingMP` it is Part 1 proper. -/
theorem partI_of_halves
    (hstrict : ∀ G, TuringInvariant G → ¬ ConstantOnCone G → StrictHalfFor G)
    (hequiv : ∀ G, TuringInvariant G → EquivHalfFor G) :
    ∀ G, TuringInvariant G → ConstantOnCone G ∨ MeasurePreserving G := by
  intro G hG
  by_cases hc : ConstantOnCone G
  · exact Or.inl hc
  · exact Or.inr (hequiv G hG (hstrict G hG hc))

/-- **Soundness / non-vacuity**: the identity admits a pointed injective tree (the full space, `code`
computable), so the interface is not jointly contradictory.  `recover` for `F = id` is `x ≤ᵀ x ⊕ code`. -/
theorem pointedInjectiveTree_id : Nonempty (PointedInjectiveTree (fun x => x)) :=
  ⟨{ code := fun _ => false
     mem := fun _ => True
     pointed := fun x _ => Cantor.le_of_computable (Computable.const false)
     realizes := fun d _ => ⟨d, trivial, Cantor.equiv.refl d⟩
     recover := fun x _ => Cantor.left_le_join x _ }⟩

/-! ### The countable-fiber case — the STRICT half's *combinatorial* fragment (Marks–Slaman–Steel)

Localization (this session, via the pointed-injectivity route): for invariant `F`,
`strict half ⟺ Marks-for-invariant-F = [countable fibers: a THEOREM] + [uncountable cone-null fibers: OPEN]`.
The countable case is already proved (MSS), and plugs into the reduction above; the open residue is precisely
the uncountable-fiber pointed-Silver step (Silver gives injectivity on a *perfect* set; making it *pointed*
is open).  A non-constant invariant `F` always has cone-null fibers (no fiber contains a cone), but cone-null
`≠` countable — the Turing jump has uncountable fibers in every cone. -/

/-- `F` has **countable fibers**: each `≡ᵀ`-fiber `{x | F x ≡ᵀ c}` is countable (i.e. countably many degrees
map to any value `c`; recall each `≡ᵀ`-class of reals is itself countable). -/
def CountableFibered (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ c, {x | F x ≡ₜ c}.Countable

/-- **Marks–Slaman–Steel countable-fiber theorem** (MSS arXiv:1109.1875, Thm 3.6): a Turing-invariant `F`
with countable fibers admits a pointed injective tree — via **Lusin–Novikov** (countable sections ⟹ `F` is a
countable union of injective Borel pieces) and **Martin's pointed-tree lemma** (an `ℕ`-valued function is
constant on a pointed perfect tree, landing one inside a single injective piece).  Unlike `GroszekSlaman`,
this is a *proved* classical theorem; it is named here as the classical input, its descriptive-set-theoretic
content being future formalization. -/
def CountableFiberMarks : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → CountableFibered F → Nonempty (PointedInjectiveTree F)

/-- **The strict half for countable-fibered `F`** — the *combinatorial* fragment of Lutz–Siskind Question 3,
complementary to the measure-theoretic route.  From the classically-proved `CountableFiberMarks` input and
the machine-checked `strictHalf_of_pointedInjectiveTree`, a countable-fibered invariant `F` satisfies the
strict half `U_M ≤_RK F_*U_M`.  **The residual open content of Q3 is exactly UNCOUNTABLE cone-null fibers**
(the pointed-Silver step) — a combinatorial wall, genuinely different from the equivalence half's inner-model
wall. -/
theorem strictHalf_of_countableFibered (hMSS : CountableFiberMarks) (hM : MartinPPT)
    (hF : TuringInvariant F) (hcf : CountableFibered F) : StrictHalfFor F :=
  strictHalf_of_pointedInjectiveTree hM hF (hMSS F hF hcf).some

#print axioms dominatedInvertible_of_pointedInjectiveTree
#print axioms strictHalf_of_pointedInjectiveTree
#print axioms pointedInjectiveTree_fiber_le
#print axioms partI_of_halves
#print axioms strictHalf_of_countableFibered

end Martin
