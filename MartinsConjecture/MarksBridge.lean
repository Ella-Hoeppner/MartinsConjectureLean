/-
**Proposition 5.37 (Lutz thesis): Marks's conjecture gives the strict half of RK-rigidity.**

Lutz–Siskind reduce the strict half of Part 1's open core (`U_M` is RK-minimal — no nonprincipal
`V` strictly `≤_RK U_M`) to **Marks's conjecture**:

> (Marks) every function `f : 2^ω → 2^ω` is either *constant on a pointed perfect tree* or
> *injective on a pointed perfect tree*.

This file formalizes that reduction against the repo's existing strict-half machinery
(`MartinStrictHalf.lean` / `MeasurePreservingCK.lean`).  For an invariant `F`:

* the **constant** alternative makes `F` constant on the cone the tree realizes (`ConstantOnCone F`
  — the pushforward `F_*U_M` is principal); while
* the **injective** alternative makes `F` injective on that cone, hence dominated-invertible
  (`dominatedInvertible_of_injectiveOnCone`), hence `StrictHalfFor F` (`U_M ≤_RK F_*U_M`) — so the
  pushforward is *not* strictly below `U_M`.

The bridge is `PPT.realizes`: a pointed perfect tree realizes every degree above its code, so the
constancy / injectivity of `F` on the *branches* transports to the *cone*.  The Marks conjecture
itself (that such a tree always exists) is the honest open input — kept as the hypothesis
`MarksTree F` / `MarksConjecture` and never assumed proved.  The open difficulty is exactly making
the tree **pointed** for a non-uniform `F` (Lutz Lemma 2.7's tree-thinning needs `f` to be a Turing
functional, which the incomparable core is not — the `ℕ`-range wall of `uniformization-engine-wall`).
-/
import MartinsConjecture.MartinStrictHalf
import MartinsConjecture.MartinTree
import MartinsConjecture.MartinOmega1Approach
import MartinsConjecture.Lemma210

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **A Marks tree for `F`**: a pointed perfect tree on whose branch-degrees `F` is either constant
(`F x ≡ᵀ F y` for all branches) or injective (`F x ≡ᵀ F y → x ≡ᵀ y`).  This is the conclusion of
Marks's conjecture applied to the invariant function inducing `F`. -/
def MarksTree (F : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ T : PPT,
    (∀ x y, T.mem x → T.mem y → F x ≡ₜ F y) ∨
    (∀ x y, T.mem x → T.mem y → F x ≡ₜ F y → x ≡ₜ y)

/-- **Prop 5.37, core dichotomy.**  A Marks tree for an invariant `F` forces `F` to be constant on a
cone or dominated-invertible.  (The tree realizes a cone above its code; constancy / injectivity on
branches transports to that cone by invariance.) -/
theorem constantOrDominatedInvertible_of_marksTree
    (hF : TuringInvariant F) (hMarks : MarksTree F) :
    ConstantOnCone F ∨ DominatedInvertible F := by
  obtain ⟨T, hconst | hinj⟩ := hMarks
  · -- Constant on the branches ⟹ constant on the cone above `T.code`.
    left
    obtain ⟨x0, hx0mem, _⟩ := T.realizes T.code (Cantor.le.refl T.code)
    refine ⟨F x0, T.code, fun X hX => ?_⟩
    obtain ⟨x, hxmem, hxX⟩ := T.realizes X hX
    exact (hF X x hxX.symm).trans (hconst x x0 hxmem hx0mem)
  · -- Injective on the branches ⟹ injective on the cone ⟹ dominated-invertible.
    right
    refine dominatedInvertible_of_injectiveOnCone hF (base := T.code) ?_
    intro X Y hX hY hFXY
    obtain ⟨x, hxmem, hxX⟩ := T.realizes X hX
    obtain ⟨y, hymem, hyY⟩ := T.realizes Y hY
    have hxy : x ≡ₜ y :=
      hinj x y hxmem hymem ((hF x X hxX).trans (hFXY.trans (hF y Y hyY).symm))
    exact hxX.symm.trans (hxy.trans hyY)

/-- **Prop 5.37, packaged with the strict half.**  A Marks tree for an invariant `F` gives
`ConstantOnCone F ∨ StrictHalfFor F` — i.e. the pushforward `F_*U_M` is principal or is *not* strictly
below `U_M`.  This is exactly the injective case of Lutz Prop 5.37, machine-checked. -/
theorem constantOrStrictHalf_of_marksTree (hM : MartinPPT)
    (hF : TuringInvariant F) (hMarks : MarksTree F) :
    ConstantOnCone F ∨ StrictHalfFor F :=
  (constantOrDominatedInvertible_of_marksTree hF hMarks).imp id
    (fun hdi => (strictHalf_iff_dominatedInvertible hM hF).mpr hdi)

/-- **Marks's conjecture** (the honest open input): every invariant function has a Marks tree. -/
def MarksConjecture : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → MarksTree F

/-- **The strict half of RK-rigidity, from Marks's conjecture** (Lutz Prop 5.37).  If Marks's
conjecture holds then every non-constant invariant `F` satisfies the strict half `StrictHalfFor F`
(`U_M ≤_RK F_*U_M`); equivalently `U_M` has no nonprincipal strict `≤_RK`-predecessor. -/
theorem strictHalf_of_marksConjecture (hM : MartinPPT) (hMarks : MarksConjecture)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) : StrictHalfFor F :=
  (constantOrStrictHalf_of_marksTree hM hF (hMarks F hF)).resolve_left hnc

/-- **Part 1 from Marks's conjecture and the equivalence half** (Lutz–Siskind Thm 5.15 route).  Marks's
conjecture supplies the strict half for every non-constant invariant `F` (Prop 5.37); with the
equivalence half (Q4) for every `F`, `partI_of_halves` yields Part 1 in the `escaping ⟹ MP` form:
every invariant `F` is constant on a cone or measure-preserving.  So the two honest open inputs to
Part 1's core are **Marks's conjecture** (the strict half / Q3) and the **equivalence half** (Q4). -/
theorem partI_of_marksConjecture_and_equivHalf (hM : MartinPPT) (hMarks : MarksConjecture)
    (hequiv : ∀ G, TuringInvariant G → EquivHalfFor G) :
    ∀ G, TuringInvariant G → ConstantOnCone G ∨ MeasurePreserving G :=
  partI_of_halves (fun _G hG hnc => strictHalf_of_marksConjecture hM hMarks hG hnc) hequiv

/-- **Marks's conjecture holds for functions injective on a cone.**  If `F` is injective on
`cone(base)` then any pointed perfect tree inside that cone (supplied by `MartinPPT`, since a cone is
cofinal) is a Marks tree — its branches lie in the cone, where `F` is injective.  So the *only* open
content of Marks's conjecture is the case where `F` is injective on **no** cone: one must find a
pointed tree on which a globally-non-injective `F` becomes injective (the tree-thinning Lemma 2.7,
which needs `F` to be a Turing functional — the wall). -/
theorem marksTree_of_injectiveOnCone (hM : MartinPPT) {base : ℕ → Bool}
    (hinj : ∀ x y, base ≤ₜ x → base ≤ₜ y → F x ≡ₜ F y → x ≡ₜ y) : MarksTree F := by
  obtain ⟨T, hTsub⟩ :=
    hM (fun x => base ≤ₜ x)
      (fun z => ⟨Cantor.join base z, Cantor.right_le_join _ _, Cantor.left_le_join _ _⟩)
  exact ⟨T, Or.inr fun x y hx hy hFxy => hinj x y (hTsub x hx) (hTsub y hy) hFxy⟩

/-- **Marks's conjecture holds for `F` with a countable degree-range** (via the constant disjunct).  If
every value `F X` is `≡ᵀ` to one of countably many reals `e n`, then the value-index `X ↦ (the n with
F X ≡ᵀ e n)` is **ℕ-valued**, so by Lemma 2.10 (`cofinal_fiber` + `MartinPPT`) it is constant `= n` on a
pointed perfect tree — on which `F` is constant (`≡ᵀ e n`).  This is the engine of
`uniformization-engine-wall` in action: countable range ⟹ the value collapses on a pointed tree.

*Scope:* this needs no invariance, so it is a genuine instance of the **full** Marks conjecture (all
functions).  For an *invariant* `F` it adds nothing new — a countable-degree-range invariant `F` is
already constant on a cone (cone theorem), so it coincides with `marksTree_of_constantOnCone`.  Its point
here is the mechanism: the incomparable core is invariant *and non-constant*, hence has **uncountable**
value-range, which is exactly what defeats this (and every `ℕ`-range) route. -/
theorem marksTree_of_countableDegreeRange (hM : MartinPPT)
    (e : ℕ → (ℕ → Bool)) (hrange : ∀ X, ∃ n, F X ≡ₜ e n) : MarksTree F := by
  classical
  obtain ⟨n, hcof⟩ :=
    cofinal_fiber (fun _ => True) (fun z => ⟨z, Cantor.le.refl z, trivial⟩)
      (fun X => (hrange X).choose)
  obtain ⟨T, hTsub⟩ := hM (fun X => True ∧ (fun X => (hrange X).choose) X = n) hcof
  refine ⟨T, Or.inl fun x y hx hy => ?_⟩
  have hFx : F x ≡ₜ e ((hrange x).choose) := (hrange x).choose_spec
  have hFy : F y ≡ₜ e ((hrange y).choose) := (hrange y).choose_spec
  have hxn : (hrange x).choose = n := (hTsub x hx).2
  have hyn : (hrange y).choose = n := (hTsub y hy).2
  rw [hxn] at hFx
  rw [hyn] at hFy
  exact hFx.trans hFy.symm

/-- **Sanity / non-vacuity: the identity has a Marks tree** (it is injective on every cone). -/
theorem marksTree_id (hM : MartinPPT) : MarksTree (fun x => x) :=
  marksTree_of_injectiveOnCone hM (base := fun _ => false) (fun _ _ _ _ h => h)

/-- **Marks's conjecture also holds for constant-on-a-cone `F`** (via the constant disjunct on any
pointed tree inside the cone).  Together with `marksTree_of_injectiveOnCone`, Marks holds whenever `F`
is *constant on a cone* OR *injective on a cone*; so its sole open content is an `F` that is **neither**
constant nor injective on any cone.  (Within the incomparable core this is the *non-injective* case: an
injective-incomparable `F` — the Q4 target — is injective on a cone, so Marks already gives it a tree;
the genuinely open Marks case is the *non-injective* incomparable `F`, i.e. the Q3/`¬DI` hard case.) -/
theorem marksTree_of_constantOnCone (hM : MartinPPT) (hc : ConstantOnCone F) : MarksTree F := by
  obtain ⟨C, cbase, hC⟩ := hc
  obtain ⟨T, hTsub⟩ :=
    hM (fun x => cbase ≤ₜ x)
      (fun z => ⟨Cantor.join cbase z, Cantor.right_le_join _ _, Cantor.left_le_join _ _⟩)
  exact ⟨T, Or.inl fun x y hx hy => (hC x (hTsub x hx)).trans (hC y (hTsub y hy)).symm⟩

/-- **An incomparable `F` is not constant on a cone.**  If `F X ≡ᵀ C` on a cone, then above `C` we get
`F X ≡ᵀ C ≤ᵀ X`, so `F X ≤ᵀ X` — contradicting `¬ F X ≤ᵀ X`. -/
theorem incomparable_not_constantOnCone
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ¬ ConstantOnCone F := by
  rintro ⟨C, ceqBase, hceq⟩
  obtain ⟨incBase, hinc'⟩ := hinc
  set b := Cantor.join C (Cantor.join ceqBase incBase) with hb
  have hCb : C ≤ₜ b := Cantor.left_le_join _ _
  have hceqb : ceqBase ≤ₜ b :=
    (Cantor.left_le_join _ _).trans (Cantor.right_le_join C _)
  have hincb : incBase ≤ₜ b :=
    (Cantor.right_le_join _ _).trans (Cantor.right_le_join C _)
  exact (hinc' b hincb).1 (((hceq b hceqb).1).trans hCb)

/-- **The incomparable core from Marks's conjecture and the equivalence half.**  If Marks's conjecture
holds and every invariant `F` satisfies the equivalence half (Q4), then **no** invariant `F` is
incomparable to its argument on a cone — Part 1's sole open content.  (Marks + Q4 give constant-or-MP;
an incomparable `F` is neither.) -/
theorem no_incomparable_of_marksConjecture_and_equivHalf (hM : MartinPPT) (hMarks : MarksConjecture)
    (hequiv : ∀ G, TuringInvariant G → EquivHalfFor G) (hF : TuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : False := by
  rcases partI_of_marksConjecture_and_equivHalf hM hMarks hequiv F hF with hc | hmp
  · exact incomparable_not_constantOnCone hinc hc
  · exact incomparable_not_measurePreserving hM hF hinc hmp

#print axioms constantOrDominatedInvertible_of_marksTree
#print axioms constantOrStrictHalf_of_marksTree
#print axioms strictHalf_of_marksConjecture
#print axioms partI_of_marksConjecture_and_equivHalf
#print axioms marksTree_of_injectiveOnCone
#print axioms marksTree_of_countableDegreeRange
#print axioms no_incomparable_of_marksConjecture_and_equivHalf

end Martin
