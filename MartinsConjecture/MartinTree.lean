/-
**Reducing `GroszekSlaman` to Martin's pointed-perfect-tree theorem.**

`PointedTree.lean` reduced Lutz–Siskind's Theorem 3.4 to `GroszekSlaman` (an
`InvertingTree` for every increasing function).  Here that hypothesis is reduced
further, to the *standard, cited* determinacy input, following Lutz–Siskind §2:

* **Lemma 2.3 (Martin, ZF+AD)** — every set cofinal in the Turing degrees contains
  a pointed perfect tree.  Lutz–Siskind cite this without proof; here it is the
  primitive `MartinPPT` (a `PPT` bundles the tree with its two standard properties,
  Prop 1.10 `realizes` and Lemma 2.1 `recover`).
* **Corollary 2.4** — a countable union that is cofinal has a *single* piece
  containing a pointed perfect tree.  Proved here (`exists_cofinal_of_iUnion`,
  a σ-pigeonhole on the cone filter, plus `MartinPPT`).
* **Lemma 2.5 / Corollary 2.6** — the uniformizing map is a *computable functional*
  `Φ_n`; applied to an increasing `F`, the relevant sets `A_n = {x : Φ_n(x)↓ ∧
  F(Φ_n(x)) = x}` have cofinal union (because `x ≤ᵀ F x`), so Cor 2.4 supplies the
  tree and the inverting functional.

The result `groszekSlaman_of_martinPPT : MartinPPT → GroszekSlaman` is proved in
full; composing with `PointedTree.lean` gives Theorem 3.4 and Part 1 from
`MartinPPT` alone.  `MartinPPT` is a named, standard consequence of determinacy —
the honest endpoint of the reduction.
-/
import MartinsConjecture.PointedTree

open scoped Computability
open OracleCode Cantor
open Classical

namespace Martin

/-! ### Extracting the real computed by a code from an oracle -/

/-- `outReal n x` is the real that code `n`, run with oracle `x`, computes bit by
bit (junk where the computation diverges).  When code `n` *does* compute a total
real `y` from `x`, `outReal n x = y` (`outReal_eq`). -/
noncomputable def outReal (n : ℕ) (x : ℕ → Bool) : ℕ → Bool :=
  fun k => if 1 ∈ eval (toPFun x) (ofNatCode n) k then true else false

/-- If code `n` computes the (total) real `y` from oracle `x`, then `outReal n x`
is exactly `y`. -/
theorem outReal_eq {n : ℕ} {x y : ℕ → Bool}
    (h : eval (toPFun x) (ofNatCode n) = toPFun y) : outReal n x = y := by
  funext k
  simp only [outReal, h, toPFun]
  cases hyk : y k <;> simp [hyk, Part.mem_some_iff]

/-- Turing reductions are witnessed by codes: `X ≤ᵀ Y` gives a numeral `n` with
`Φ_n^Y = X`. -/
theorem exists_code {X Y : ℕ → Bool} (h : X ≤ₜ Y) :
    ∃ n : ℕ, eval (toPFun Y) (ofNatCode n) = toPFun X := by
  obtain ⟨c, hc⟩ := OracleCode.exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  exact ⟨encodeCode c, by rw [ofNatCode_encodeCode]; exact hc⟩

/-! ### Pointed perfect trees and Martin's theorem -/

/-- A functional `g` is a **computable functional on the branches** `mem` if a
single code computes `g x` from `x` for every branch `x`. -/
def CompFunctionalOn (mem : (ℕ → Bool) → Prop) (g : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  ∃ c : ℕ, ∀ x, mem x → eval (toPFun x) (ofNatCode c) = toPFun (g x)

/-- A **pointed perfect tree**, presented by the recursion-theoretic facts about
it that the development uses: its code `code`, its branch predicate `mem`,
pointedness (`pointed`, Def 1.9), that it **realizes a cone of degrees** (`realizes`,
Prop 1.10), and the **effective-injectivity recovery** (`recover`, Lemma 2.1: a
computable injective functional on the branches lets the branch be recovered from
its image and the tree). -/
structure PPT where
  /-- The tree, coded as a real every branch computes. -/
  code : ℕ → Bool
  /-- Membership in `[T]`. -/
  mem : (ℕ → Bool) → Prop
  /-- Pointedness (Def 1.9). -/
  pointed : ∀ x, mem x → code ≤ₜ x
  /-- Prop 1.10: the tree realizes every degree above its code. -/
  realizes : ∀ d, code ≤ₜ d → ∃ x, mem x ∧ x ≡ₜ d
  /-- Lemma 2.1: a computable injective functional on the branches is invertible
  from its image together with the tree. -/
  recover : ∀ g, CompFunctionalOn mem g →
    (∀ x y, mem x → mem y → g x = g y → x = y) →
    ∀ x, mem x → x ≤ₜ Cantor.join (g x) code

/-- A set is **cofinal** in the Turing degrees if it meets every cone. -/
def Cofinal (A : (ℕ → Bool) → Prop) : Prop := ∀ z, ∃ x, z ≤ₜ x ∧ A x

/-- **Martin's pointed-perfect-tree theorem** (Lutz–Siskind Lemma 2.3, ZF+AD):
every cofinal set contains a pointed perfect tree.  A named, standard consequence
of determinacy; the endpoint of the reduction. -/
def MartinPPT : Prop :=
  ∀ A : (ℕ → Bool) → Prop, Cofinal A → ∃ T : PPT, ∀ x, T.mem x → A x

/-- **σ-pigeonhole for cofinality (Corollary 2.4, combinatorial half).**  If a
countable union of sets is cofinal, then one of the sets is cofinal.  (If each
`A n` missed a cone with base `zₙ`, nothing above `⨁ₙ zₙ` could lie in the
union.) -/
theorem exists_cofinal_of_iUnion {A : ℕ → (ℕ → Bool) → Prop}
    (h : Cofinal (fun x => ∃ n, A n x)) : ∃ n, Cofinal (A n) := by
  by_contra hcon
  push_neg at hcon
  -- each `A n` misses a cone, with base `z n`
  have : ∀ n, ∃ z, ∀ x, z ≤ₜ x → ¬ A n x := by
    intro n
    have := hcon n
    unfold Cofinal at this
    push_neg at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, fun x hzx => (by simpa using hz x hzx)⟩
  choose z hz using this
  obtain ⟨x, hZx, m, hAmx⟩ := h (bigJoin z)
  exact hz m x ((le_bigJoin z m).trans hZx) hAmx

/-! ### The reduction -/

/-- **Groszek–Slaman uniformization from Martin's theorem** (Lutz–Siskind Lemma 2.5
/ Cor 2.6, fully proved here).  For an increasing `F`, the sets `A n = {x : Φ_n(x)
computes a real `y` with `F y = x`}` have cofinal union (`x = F z ≥ᵀ z` lands in
`A c` for the code `c` witnessing `z ≤ᵀ F z`); Cor 2.4 extracts a pointed perfect
tree inside one `A n`, and `Φ_n` is the inverting functional. -/
theorem groszekSlaman_of_martinPPT (hM : MartinPPT) : GroszekSlaman := by
  intro F hFinc
  -- `A n x`: code `n` computes a real from `x`, and `F` of it is `x`.
  set A : ℕ → (ℕ → Bool) → Prop := fun n x =>
    eval (toPFun x) (ofNatCode n) = toPFun (outReal n x) ∧ F (outReal n x) = x with hA
  -- The union is cofinal: `F z` witnesses cofinality at `z`.
  have hcof : Cofinal (fun x => ∃ n, A n x) := by
    intro z
    obtain ⟨c, hc⟩ := exists_code (hFinc z)
    refine ⟨F z, hFinc z, c, ?_, ?_⟩
    · rw [outReal_eq hc]; exact hc
    · rw [outReal_eq hc]
  -- Pigeonhole + Martin's theorem: a pointed perfect tree inside some `A n`.
  obtain ⟨n, hAn_cof⟩ := exists_cofinal_of_iUnion hcof
  obtain ⟨T, hTsub⟩ := hM (A n) hAn_cof
  -- Assemble the inverting tree with `h = outReal n`.
  refine ⟨{ code := T.code, mem := T.mem, h := outReal n
            pointed := T.pointed, realizes := T.realizes
            invert := fun x hx => (hTsub x hx).2
            recover := ?_ }⟩
  intro x hx
  refine T.recover (outReal n) ⟨n, fun y hy => (hTsub y hy).1⟩ ?_ x hx
  -- `outReal n` is injective on branches: `F ∘ (outReal n) = id` there.
  intro a b ha hb hab
  rw [← (hTsub a ha).2, ← (hTsub b hb).2, hab]

/-- **Theorem 3.4 from Martin's theorem.**  Composing the reduction with
`PointedTree.lean`: a Turing-invariant measure-preserving function is above the
identity on a cone, assuming only `MartinPPT`. -/
theorem measurePreservingAboveId_of_martinPPT (hM : MartinPPT)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : TuringInvariant F) (hmp : MeasurePreserving F) :
    AboveIdOnCone F :=
  measurePreservingAboveId_of_groszekSlaman (groszekSlaman_of_martinPPT hM) hF hmp

/-- **Part 1 from Martin's theorem and the class half.** -/
theorem partI_of_martinPPT (hM : MartinPPT)
    (hclass : ∀ F, TuringInvariant F → ¬ ConstantOnCone F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_groszekSlaman (groszekSlaman_of_martinPPT hM) hclass

/-- **The sharpest statement of what Part 1 rests on.**  Combining the two threads
of this development, Part 1 of Martin's conjecture follows from exactly two
standard/open inputs:

* `MartinPPT` — Martin's pointed-perfect-tree theorem (a *standard* determinacy
  consequence), which discharges the general Theorem 3.4; and
* **escaping ⟹ measure-preserving** — the class-specific content ("a function that
  avoids every degree from below on a cone reaches every degree from above on a
  cone"), which by `escaping_iff_not_constant` is equivalent to the more familiar
  "non-constant ⟹ measure-preserving".

Everything else — the Slaman–Steel/Bard uniform theory, the cone theorem, the
reduction to cores, the whole of Lutz–Siskind §§2–3 except Martin's cited theorem —
is machine-checked in this project. -/
theorem partI_of_martinPPT_escaping (hM : MartinPPT)
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_martinPPT hM ((nonconstant_mp_iff_escaping_mp hTD).mpr hesc)

#print axioms groszekSlaman_of_martinPPT
#print axioms measurePreservingAboveId_of_martinPPT
#print axioms partI_of_martinPPT_escaping

end Martin
