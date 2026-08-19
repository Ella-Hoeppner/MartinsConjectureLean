/-
**Theorem 3.4 of Lutz–Siskind, reduced to the Groszek–Slaman construction.**

Lutz–Siskind's central theorem — *a Turing-invariant measure-preserving function
is above the identity on a cone* — is proved (their §3) from:

* **Lemma 3.3** (measure-preserving ⟹ has an increasing modulus) — already
  formalized here as `measurePreserving_hasModulus`;
* **Corollary 2.6** (an increasing function is right-inverted, on a *pointed
  perfect tree* by a computable map) — itself the Groszek–Slaman uniformization
  **Lemma 2.5**;
* **Lemma 2.1** (a computable injective map on a perfect tree lets the branch be
  recovered from its image together with the tree);
* the standard fact that a **pointed perfect tree realizes a cone of degrees**
  (every degree above the tree is the degree of a branch).

This file isolates the recursion-theoretic *output* of that tree machinery into a
single interface `InvertingTree` (one per increasing `F`), and then gives a **fully
rigorous, `sorry`-free proof of Theorem 3.4** — and its consequences for Part 1 —
*from* that interface.  The only remaining input is `GroszekSlaman`: the existence
of an `InvertingTree` for every increasing function.  That is exactly the
Groszek–Slaman pointed-perfect-tree construction (Lemmas 2.1 + 2.5), the one
classical ingredient this project does not yet build from scratch.

The point: everything in Lutz–Siskind §3 *except* the tree construction is now
machine-checked, and the whole of Theorem 3.4 rests on one clearly-named, standard
existence statement.
-/
import MartinsConjecture.MeasurePreserving

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- The recursion-theoretic **output of the Groszek–Slaman construction** applied
to an increasing function `F` (`x ≤ᵀ F x` for all `x`).  It presents a *pointed
perfect tree* by its code `code` (a real that every branch computes) and a branch
predicate `mem`, together with a map `h` right-inverting `F` on the branches.  The
four fields are exactly the recursion-theoretic facts Lutz–Siskind use:

* `pointed` — the tree is **pointed**: every branch computes the tree (Def 1.9);
* `realizes` — a **pointed perfect tree realizes a cone of degrees**: every degree
  `≥ᵀ code` is the degree of a branch;
* `invert` — `h` **right-inverts `F`** on the branches (Cor 2.6): `F (h x) = x`;
* `recover` — **Lemma 2.1**: the branch is recovered from `h x` together with the
  tree, `x ≤ᵀ h x ⊕ code`  (`h` is computable and injective on `[T]`, so this is
  the effective-injectivity conclusion). -/
structure InvertingTree (F : (ℕ → Bool) → (ℕ → Bool)) where
  /-- The tree, coded as a real that every branch computes. -/
  code : ℕ → Bool
  /-- Membership in the set of branches `[T]`. -/
  mem : (ℕ → Bool) → Prop
  /-- The computable right inverse of `F` on the branches. -/
  h : (ℕ → Bool) → (ℕ → Bool)
  /-- Pointedness: every branch computes the tree. -/
  pointed : ∀ x, mem x → code ≤ₜ x
  /-- The tree realizes a cone of degrees: every degree above `code` is a branch's. -/
  realizes : ∀ d, code ≤ₜ d → ∃ x, mem x ∧ x ≡ₜ d
  /-- `h` right-inverts `F` on the branches. -/
  invert : ∀ x, mem x → F (h x) = x
  /-- Lemma 2.1: the branch is recovered from its `h`-image and the tree. -/
  recover : ∀ x, mem x → x ≤ₜ Cantor.join (h x) code

/-- **Groszek–Slaman uniformization** (Lutz–Siskind Lemma 2.5 / Cor 2.6, together
with Lemma 2.1): every increasing function admits an `InvertingTree`.  This is the
single classical existence statement on which Theorem 3.4 rests. -/
def GroszekSlaman : Prop :=
  ∀ F : (ℕ → Bool) → (ℕ → Bool), (∀ x, x ≤ₜ F x) → Nonempty (InvertingTree F)

/-- **Theorem 3.4 (Lutz–Siskind), from the Groszek–Slaman construction.**  A
Turing-invariant measure-preserving function is above the identity on a cone.

Proof (their §3, machine-checked here modulo `GroszekSlaman`): take an increasing
modulus `g` (Lemma 3.3); it satisfies `x ≤ᵀ g x`, so `GroszekSlaman` supplies an
`InvertingTree` for `g`, with branch recovery `x ≤ᵀ h x ⊕ code`, pointedness, and
cone-realization.  For a degree `d` above `code` and above the measure-preserving
base for `code`, realize `d` by a branch `x ≡ᵀ d`.  The modulus turns the inverse
into `h x ≤ᵀ F x`; measure-preservation gives `code ≤ᵀ F x`; so `x ≤ᵀ h x ⊕ code
≤ᵀ F x`.  Invariance transports `x ≤ᵀ F x` across `x ≡ᵀ d` to `d ≤ᵀ F d`. -/
theorem measurePreservingAboveId_of_groszekSlaman (hGS : GroszekSlaman)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : TuringInvariant F) (hmp : MeasurePreserving F) :
    AboveIdOnCone F := by
  -- Lemma 3.3: an increasing modulus.
  obtain ⟨g, hg1, hg2⟩ := measurePreserving_hasModulus hmp
  -- Groszek–Slaman: an inverting tree for the increasing modulus `g`.
  obtain ⟨Tr⟩ := hGS g hg1
  -- Measure-preservation puts `F` above the tree code on a cone.
  obtain ⟨bmp, hbmp⟩ := hmp Tr.code
  refine ⟨Cantor.join Tr.code bmp, fun d hd => ?_⟩
  have hcode_d : Tr.code ≤ₜ d := (Cantor.left_le_join _ _).trans hd
  have hbmp_d : bmp ≤ₜ d := (Cantor.right_le_join _ _).trans hd
  -- Realize `d` by a branch `x ≡ᵀ d`.
  obtain ⟨x, hxmem, hxd⟩ := Tr.realizes d hcode_d
  -- Modulus inversion: `h x ≤ᵀ F x`.
  have hgx : g (Tr.h x) = x := Tr.invert x hxmem
  have hhx_Fx : Tr.h x ≤ₜ F x := hg2 (Tr.h x) x (by rw [hgx]; exact Cantor.le.refl x)
  -- Measure-preservation: `code ≤ᵀ F x`  (since `x ≡ᵀ d ≥ᵀ bmp`).
  have hcode_Fx : Tr.code ≤ₜ F x := hbmp x (hbmp_d.trans hxd.2)
  -- Recovery: `x ≤ᵀ h x ⊕ code ≤ᵀ F x`.
  have hx_Fx : x ≤ₜ F x :=
    (Tr.recover x hxmem).trans (Cantor.join_le hhx_Fx hcode_Fx)
  -- Transport across `x ≡ᵀ d` by invariance.
  exact hxd.2.trans (hx_Fx.trans (hF x d hxd).1)

/-- Packaged as `MeasurePreservingAboveId` (Lutz–Siskind Thm 1.39). -/
theorem measurePreservingAboveId_of_groszekSlaman' (hGS : GroszekSlaman) :
    MeasurePreservingAboveId :=
  fun _F hF hmp => measurePreservingAboveId_of_groszekSlaman hGS hF hmp

/-- **Part 1 from the Groszek–Slaman construction and the class half.**  Combined
with `partI_of_measurePreserving`, Part 1 of Martin's conjecture follows from
`GroszekSlaman` (Theorem 3.4's tree construction) together with "non-constant ⟹
measure-preserving".  By `nonconstant_mp_iff_escaping_mp` the latter is exactly
"escaping ⟹ measure-preserving"; so the *entire* remaining content of Part 1 is
these two standard/open inputs. -/
theorem partI_of_groszekSlaman (hGS : GroszekSlaman)
    (hclass : ∀ F, TuringInvariant F → ¬ ConstantOnCone F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_measurePreserving (measurePreservingAboveId_of_groszekSlaman' hGS) hclass

/-! ### Soundness of the interface

The `InvertingTree` interface is a *hypothesis* feeding the reduction, so it is
worth checking it is satisfiable — that the four fields are not jointly
contradictory.  The identity function (which is increasing) admits an inverting
tree: the full space `2^ω` as a (computable, hence pointed) tree with `h = id`. -/

/-- The interface is non-vacuous: the identity admits an inverting tree. -/
theorem inverting_tree_id : Nonempty (InvertingTree (fun x => x)) :=
  ⟨{ code := fun _ => false
     mem := fun _ => True
     h := fun x => x
     pointed := fun x _ => Cantor.le_of_computable (Computable.const false)
     realizes := fun d _ => ⟨d, trivial, Cantor.equiv.refl d⟩
     invert := fun _ _ => rfl
     recover := fun x _ => Cantor.left_le_join x _ }⟩

#print axioms measurePreservingAboveId_of_groszekSlaman
#print axioms partI_of_groszekSlaman

end Martin
