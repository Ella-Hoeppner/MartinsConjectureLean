/-
Cones are Borel, the cone filter is countably directed, and the ω-initial
segment of the Martin order predicted by Part II is realized.

* `Martin.measurableSet_cone` — every cone `{X | C ≤ₜ X}` is a Borel set
  (so "on a cone" is a Borel notion of largeness).
* `Cantor.le_bigJoin` / `Martin.cone_bigJoin_subset` — countable joins exist,
  so the cone filter is countably closed: this is the combinatorial basis of
  *Martin measure*.
* `Martin.regular_jumpIter`, `Martin.martinLT_jumpIter`,
  `Martin.martinLT_const_id` — inside the class `Regular` of Borel
  Turing-invariant above-the-identity functions, the chain

      (const C) <ₘ id <ₘ (·′) <ₘ (·″) <ₘ ⋯

  is strictly increasing in the Martin order.  Part II of Martin's conjecture
  asserts that (above `id`) this chain enumerates *all* of `Regular` up to
  Martin equivalence, in order type ω (below the hyperjump); the chain itself
  — the provable half — is verified here.
-/
import MartinsConjecture.MeasurableJump

open scoped Computability
open OracleCode

namespace Cantor

/-- Countable join: interleave countably many points along `Nat.pair`. -/
def bigJoin (f : ℕ → (ℕ → Bool)) : ℕ → Bool :=
  fun m => f (Nat.unpair m).1 (Nat.unpair m).2

theorem le_bigJoin (f : ℕ → (ℕ → Bool)) (n : ℕ) : f n ≤ₜ bigJoin f := by
  refine le_of_precomp (g := fun k => Nat.pair n k)
    (Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.const n) Primrec.id))
    fun k => ?_
  simp [bigJoin, Nat.unpair_pair]

end Cantor

namespace Martin

open Cantor

/-! ### Cones are Borel -/

/-- **Cones are Borel sets**: membership in a cone is a countable union
(over codes) of countable intersections (over inputs) of Borel conditions. -/
theorem measurableSet_cone (C : ℕ → Bool) : MeasurableSet (cone C) := by
  have hset : cone C = ⋃ e : ℕ, ⋂ n,
      {Y : ℕ → Bool | cond (C n) 1 0 ∈ eval (toPFun Y) (ofNatCode e) n} := by
    ext Y
    simp only [cone, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
      refine ⟨encodeCode c, fun n => ?_⟩
      rw [ofNatCode_encodeCode, hc]
      exact Part.mem_some_iff.mpr rfl
    · rintro ⟨e, he⟩
      have hcode : eval (toPFun Y) (ofNatCode e) = toPFun C := by
        funext n
        exact Part.eq_some_iff.mpr (he n)
      exact RecursiveIn.iff_nat.mpr (hcode ▸ eval_recursiveIn (toPFun Y) (ofNatCode e))
  rw [hset]
  exact MeasurableSet.iUnion fun e => MeasurableSet.iInter fun n =>
    measurableSet_mem_eval _ _ _

/-! ### The cone filter is countably directed (basis of Martin measure) -/

/-- Countably many cones contain a common cone: the cone "filter" is
countably closed.  (With the cone theorem, this is what makes *Martin
measure* a countably complete ultrafilter-like measure on the degrees.) -/
theorem cone_bigJoin_subset (f : ℕ → (ℕ → Bool)) (n : ℕ) :
    cone (bigJoin f) ⊆ cone (f n) :=
  fun _X hX => (le_bigJoin f n).trans hX

/-- "On a cone" is closed under conjunction (via the join). -/
theorem onCone_and {P Q : (ℕ → Bool) → Prop} (hP : OnCone P) (hQ : OnCone Q) :
    OnCone fun X => P X ∧ Q X := by
  obtain ⟨A, hA⟩ := hP
  obtain ⟨B, hB⟩ := hQ
  exact ⟨join A B, fun X hX =>
    ⟨hA X ((left_le_join A B).trans hX), hB X ((right_le_join A B).trans hX)⟩⟩

/-- "On a cone" is closed under **countable** conjunction (via the countable
join): the cone filter is countably complete. -/
theorem onCone_forall {P : ℕ → (ℕ → Bool) → Prop} (h : ∀ n, OnCone (P n)) :
    OnCone fun X => ∀ n, P n X := by
  choose f hf using h
  exact ⟨bigJoin f, fun X hX n => hf n X ((le_bigJoin f n).trans hX)⟩

/-! ### The ω-chain `const <ₘ id <ₘ jump <ₘ jump² <ₘ ⋯` inside `Regular` -/

/-- The class `Regular` is closed under composing with the jump. -/
theorem Regular.jumpComp {F : (ℕ → Bool) → ℕ → Bool} (hF : Regular F) :
    Regular (fun X => Cantor.jump (F X)) := by
  obtain ⟨hB, hTI, B, hcone⟩ := hF
  exact ⟨measurable_jump.comp hB,
    fun X Y h => Cantor.jump_congr (hTI X Y h),
    B, fun X hX => (hcone X hX).trans (le_jump (F X))⟩

/-- The identity is `Regular`. -/
theorem regular_id : Regular (fun X : ℕ → Bool => X) :=
  ⟨measurable_id, fun _ _ h => h, ⟨fun _ => false, fun X _ => le.refl X⟩⟩

/-- Every finite jump iterate is `Regular`. -/
theorem regular_jumpIter : ∀ n, Regular (fun X => Cantor.jump^[n] X)
  | 0 => regular_id
  | n + 1 => by
      simp only [Function.iterate_succ_apply']
      exact (regular_jumpIter n).jumpComp

/-- The jump iterates are strictly increasing in the Martin order. -/
theorem martinLT_jumpIter (n : ℕ) :
    MartinLT (fun X => Cantor.jump^[n] X) (fun X => Cantor.jump^[n + 1] X) := by
  simp only [Function.iterate_succ_apply']
  exact martinLT_jump _

/-- Every constant function is strictly Martin below the identity. -/
theorem martinLT_const_id (C : ℕ → Bool) :
    MartinLT (fun _ => C) (fun X : ℕ → Bool => X) := by
  constructor
  · exact ⟨C, fun X hX => hX⟩
  · rintro ⟨B, hB⟩
    exact not_jump_le (join C B)
      ((hB (Cantor.jump (join C B))
        ((right_le_join C B).trans (le_jump _))).trans (left_le_join C B))

/-- The provable half of the Part II successor claim, packaged: for every
regular `F`, its jump-composition is again regular and strictly Martin above
it.  (The open half of `PartII_Borel_Succ` is *minimality*: that nothing
regular fits strictly between `F` and `jump ∘ F`.) -/
theorem partII_succ_provable_half (F : (ℕ → Bool) → ℕ → Bool) (hF : Regular F) :
    Regular (fun X => Cantor.jump (F X)) ∧ MartinLT F (fun X => Cantor.jump (F X)) :=
  ⟨hF.jumpComp, martinLT_jump F⟩

#print axioms measurableSet_cone
#print axioms onCone_forall
#print axioms martinLT_jumpIter
#print axioms martinLT_const_id
#print axioms partII_succ_provable_half

end Martin
