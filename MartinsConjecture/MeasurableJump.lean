/-
The jump is Borel.

For each oracle code `c` and numbers `x, y`, the set of oracles `X` for which
the computation `eval (toPFun X) c x` converges to `y` is Borel (measurable
for the product σ-algebra): by induction on `c`, convergence decomposes into
countable unions and intersections of conditions on subcomputations, with the
base `oracle` case depending on a single coordinate of `X`.

Consequences: the jump predicate is Borel in the oracle
(`Martin.measurableSet_jumpP`), the jump function on Cantor space is Borel
(`Martin.measurable_jump`), and hence — combining with `JumpInvariance` and
jump strictness — **the jump belongs to the class `Martin.Regular` of Borel,
Turing-invariant, above-the-identity functions that Part II of Martin's
conjecture describes** (`Martin.regular_jump`), and it is strictly Martin
below no... rather: together with `martinLT_jump` it realizes the successor
pattern the conjecture asserts.
-/
import MartinsConjecture.UniformJump

open scoped Computability
open OracleCode

namespace Martin

open Cantor

private theorem measurableSet_setOf_const (p : Prop) :
    MeasurableSet {_X : ℕ → Bool | p} := by
  by_cases hp : p
  · simp only [hp, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [hp, Set.setOf_false]
    exact MeasurableSet.empty

/-- For every code and input/output pair, the set of oracles on which the
computation converges to that output is Borel. -/
theorem measurableSet_mem_eval :
    ∀ (c : OracleCode) (x y : ℕ),
      MeasurableSet {X : ℕ → Bool | y ∈ eval (toPFun X) c x} := by
  intro c
  induction c with
  | zero =>
    intro x y
    exact measurableSet_setOf_const (y ∈ (0 : Part ℕ))
  | succ =>
    intro x y
    exact measurableSet_setOf_const (y ∈ ((Nat.succ : ℕ →. ℕ) x))
  | left =>
    intro x y
    exact measurableSet_setOf_const (y ∈ (((Nat.unpair x).1 : ℕ) : Part ℕ))
  | right =>
    intro x y
    exact measurableSet_setOf_const (y ∈ (((Nat.unpair x).2 : ℕ) : Part ℕ))
  | oracle =>
    intro x y
    have hset : {X : ℕ → Bool | y ∈ eval (toPFun X) .oracle x}
        = (fun X : ℕ → Bool => X x) ⁻¹' {b : Bool | y = cond b 1 0} := by
      ext X
      simp [toPFun, Part.mem_some_iff]
    rw [hset]
    exact measurable_pi_apply x trivial
  | pair cf cg ihf ihg =>
    intro x y
    have hset : {X : ℕ → Bool | y ∈ eval (toPFun X) (.pair cf cg) x}
        = ⋃ a, ⋃ b,
            ({X | a ∈ eval (toPFun X) cf x} ∩ {X | b ∈ eval (toPFun X) cg x})
              ∩ {_X : ℕ → Bool | Nat.pair a b = y} := by
      ext X
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [mem_eval_pair]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        exact ⟨a, b, ⟨ha, hb⟩, hab⟩
      · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
        exact ⟨a, ha, b, hb, hab⟩
    rw [hset]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      ((ihf x a).inter (ihg x b)).inter (measurableSet_setOf_const _)
  | comp cf cg ihf ihg =>
    intro x y
    have hset : {X : ℕ → Bool | y ∈ eval (toPFun X) (.comp cf cg) x}
        = ⋃ b, {X | b ∈ eval (toPFun X) cg x} ∩ {X | y ∈ eval (toPFun X) cf b} := by
      ext X
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [mem_eval_comp]
    rw [hset]
    exact MeasurableSet.iUnion fun b => (ihg x b).inter (ihf b y)
  | prec cf cg ihf ihg =>
    intro x y
    have H : ∀ (a n y₀ : ℕ), MeasurableSet {X : ℕ → Bool |
        y₀ ∈ Nat.rec (motive := fun _ => Part ℕ) (eval (toPFun X) cf a)
          (fun k IH => IH >>= fun i =>
            eval (toPFun X) cg (Nat.pair a (Nat.pair k i))) n} := by
      intro a n
      induction n with
      | zero =>
        intro y₀
        exact ihf a y₀
      | succ n ihn =>
        intro y₀
        have hset : {X : ℕ → Bool |
            y₀ ∈ Nat.rec (motive := fun _ => Part ℕ) (eval (toPFun X) cf a)
              (fun k IH => IH >>= fun i =>
                eval (toPFun X) cg (Nat.pair a (Nat.pair k i))) (n + 1)}
            = ⋃ i,
                {X : ℕ → Bool |
                  i ∈ Nat.rec (motive := fun _ => Part ℕ) (eval (toPFun X) cf a)
                    (fun k IH => IH >>= fun i' =>
                      eval (toPFun X) cg (Nat.pair a (Nat.pair k i'))) n}
                ∩ {X | y₀ ∈ eval (toPFun X) cg (Nat.pair a (Nat.pair n i))} := by
          ext X
          simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro h
            exact Part.mem_bind_iff.mp h
          · rintro ⟨i, hi, hy⟩
            exact Part.mem_bind_iff.mpr ⟨i, hi, hy⟩
        rw [hset]
        exact MeasurableSet.iUnion fun i => (ihn i).inter (ihg _ _)
    exact H (Nat.unpair x).1 (Nat.unpair x).2 y
  | rfind cf ihf =>
    intro x y
    have hset : {X : ℕ → Bool | y ∈ eval (toPFun X) (.rfind cf) x}
        = {X | 0 ∈ eval (toPFun X) cf (Nat.pair x y)}
            ∩ ⋂ m, ⋂ _h : m < y, ⋃ z,
                {X | z ∈ eval (toPFun X) cf (Nat.pair x m)}
                  ∩ {_X : ℕ → Bool | z ≠ 0} := by
      ext X
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
      rw [mem_eval_rfind]
    rw [hset]
    exact (ihf _ _).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
        MeasurableSet.iUnion fun z => (ihf _ _).inter (measurableSet_setOf_const _))

/-- The jump predicate is Borel in the oracle. -/
theorem measurableSet_jumpP (e : ℕ) :
    MeasurableSet {X : ℕ → Bool | jumpP (toPFun X) e} := by
  have hset : {X : ℕ → Bool | jumpP (toPFun X) e}
      = ⋃ y, {X | y ∈ eval (toPFun X) (ofNatCode e) e} := by
    ext X
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, jumpP, Part.dom_iff_mem]
  rw [hset]
  exact MeasurableSet.iUnion fun y => measurableSet_mem_eval _ _ _

/-- **The jump is a Borel function** on Cantor space. -/
theorem measurable_jump : Measurable Cantor.jump := by
  apply measurable_pi_lambda
  intro e
  apply measurable_to_countable'
  intro b
  cases b
  · have hset : (fun X : ℕ → Bool => Cantor.jump X e) ⁻¹' {false}
        = {X : ℕ → Bool | jumpP (toPFun X) e}ᶜ := by
      ext X
      simp [Cantor.jump]
    rw [hset]
    exact (measurableSet_jumpP e).compl
  · have hset : (fun X : ℕ → Bool => Cantor.jump X e) ⁻¹' {true}
        = {X : ℕ → Bool | jumpP (toPFun X) e} := by
      ext X
      simp [Cantor.jump]
    rw [hset]
    exact measurableSet_jumpP e

/-- **The jump is `Regular`**: Borel, Turing invariant, and Martin above the
identity — a bona fide member of the class of functions that Part II of
Martin's conjecture describes, realizing (via `martinLT_jump`) the successor
pattern the conjecture asserts. -/
theorem regular_jump : Regular Cantor.jump :=
  ⟨measurable_jump, turingInvariant_jump,
    ⟨fun _ => false, fun X _ => le_jump X⟩⟩

#print axioms measurable_jump
#print axioms regular_jump

end Martin
