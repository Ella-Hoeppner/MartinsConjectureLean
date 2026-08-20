/-
**`recover` is a theorem, not an axiom: `MartinPPT` from a weaker `MartinPPT'`.**

`MartinTree.lean` reduced Part 1 to `MartinPPT`: every cofinal set contains a
*pointed perfect tree*, bundled as a `PPT`.  That structure carried **three**
recursion-theoretic promises about the tree — `pointed` (Def 1.9), `realizes`
(Prop 1.10), and `recover` (Lemma 2.1).  Of these, `recover` is *not* part of
Martin's cited theorem (Lemma 2.3): Lutz–Siskind prove it separately, as their
Lemma 2.1 (a computable injective functional on the branches is invertible from
its image and the tree).

`EffectiveTreeReduction.lean` now proves that lemma in full (`lemma21`).  So the
`recover` field can be *discharged*, not assumed: we introduce `RawPPT` — a
genuine downward-closed tree that is only `pointed` and `realizes` — and the
weaker `MartinPPT'`, and show `MartinPPT' → MartinPPT`.  The bridge is `lemma21`.

Consequently Part 1 rests on `MartinPPT'`, which is *exactly* Martin's Lemma 2.3
in a concrete tree representation, with no recursion-theoretic content beyond
pointedness and cone-realization smuggled in.
-/
import MartinsConjecture.MartinTree
import MartinsConjecture.EffectiveTreeReduction

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- A **raw pointed perfect tree**: a genuine downward-closed tree (its set of
finite strings coded by the real `code` via `treePos`), that is `pointed`
(computable from each of its branches, Def 1.9) and `realizes` every degree above
its code (Prop 1.10).  Unlike `PPT`, it carries **no** `recover` field — that is
supplied for free by `lemma21`. -/
structure RawPPT where
  /-- The tree, coded as the characteristic real of its set of finite strings. -/
  code : ℕ → Bool
  /-- The set of strings is downward closed (a genuine tree). -/
  closed : ∀ σ b, treeMem code (σ ++ [b]) → treeMem code σ
  /-- Pointedness (Def 1.9): every branch computes the tree. -/
  pointed : ∀ x, IsBranch (treeMem code) x → code ≤ₜ x
  /-- Prop 1.10: the tree realizes every degree above its code. -/
  realizes : ∀ d, code ≤ₜ d → ∃ x, IsBranch (treeMem code) x ∧ x ≡ₜ d

/-- **Every raw pointed perfect tree is a full `PPT`.**  The three abstract `PPT`
fields are read off directly, and the fourth — `recover` (Lemma 2.1) — is
supplied by `lemma21`: on a downward-closed tree, a computable injective
functional on the branches lets each branch be recovered from its image and the
tree.  No new hypothesis is needed. -/
def RawPPT.toPPT (T : RawPPT) : PPT where
  code := T.code
  mem := IsBranch (treeMem T.code)
  pointed := T.pointed
  realizes := T.realizes
  recover := by
    rintro g ⟨c, hc⟩ hinj x hx
    exact lemma21 (Tr := T.code) (e := c) (g := g) T.closed hc
      (fun y y' hy hy' => hinj y y' hy hy') hx

/-- **Martin's pointed-perfect-tree theorem, weakened** — every cofinal set
contains a *raw* pointed perfect tree.  This is `MartinPPT` with the `recover`
promise removed; it is exactly Lemma 2.3 (Martin, ZF+AD) in a concrete tree
representation. -/
def MartinPPT' : Prop :=
  ∀ A : (ℕ → Bool) → Prop, Cofinal A →
    ∃ T : RawPPT, ∀ x, IsBranch (treeMem T.code) x → A x

/-- **`MartinPPT` follows from the weaker `MartinPPT'`.**  The only gap between
them — the `recover` field — is closed by `lemma21`.  Hence assuming Martin's
theorem in the honest, recover-free form `MartinPPT'` suffices for everything the
development derives from `MartinPPT`. -/
theorem martinPPT_of_martinPPT' (h : MartinPPT') : MartinPPT := by
  intro A hA
  obtain ⟨T, hT⟩ := h A hA
  exact ⟨T.toPPT, hT⟩

/-! ### Part 1 from the recover-free hypothesis -/

/-- **Groszek–Slaman uniformization from `MartinPPT'`.** -/
theorem groszekSlaman_of_martinPPT' (h : MartinPPT') : GroszekSlaman :=
  groszekSlaman_of_martinPPT (martinPPT_of_martinPPT' h)

/-- **Theorem 3.4 from `MartinPPT'`.** -/
theorem measurePreservingAboveId_of_martinPPT' (h : MartinPPT')
    {F : (ℕ → Bool) → ℕ → Bool} (hF : TuringInvariant F) (hmp : MeasurePreserving F) :
    AboveIdOnCone F :=
  measurePreservingAboveId_of_martinPPT (martinPPT_of_martinPPT' h) hF hmp

/-- **The sharpest recover-free statement of Part 1's dependencies.**  Part 1 of
Martin's conjecture follows from exactly:

* `MartinPPT'` — Martin's Lemma 2.3 with **no** recursion-theoretic content beyond
  pointedness and cone-realization (the `recover` promise of the old `MartinPPT`
  is now a theorem, `lemma21`); and
* **escaping ⟹ measure-preserving** — the class-specific content.

Everything else, including Lutz–Siskind's Lemma 2.1, is machine-checked. -/
theorem partI_of_martinPPT'_escaping (h : MartinPPT')
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_martinPPT_escaping (martinPPT_of_martinPPT' h) hTD hesc

#print axioms martinPPT_of_martinPPT'
#print axioms partI_of_martinPPT'_escaping

end Martin
