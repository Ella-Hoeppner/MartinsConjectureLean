/-
The use principle: oracle computations are local.

If a computation with oracle `X` converges, it consults only finitely many
bits of `X`: any oracle agreeing with `X` on a long enough prefix yields the
same converging computation (`OracleCode.eval_locality`).  Proved by
induction on codes — no step-indexed universal machine needed; the finite
"use" is extracted from the convergence derivation itself.

Consequences (effective topology):
* `Martin.isOpen_mem_eval` — convergence-to-a-value is an *open* condition
  on the oracle (upgrading `measurableSet_mem_eval`);
* `Martin.isOpen_jumpP` — the jump predicate is open (Σ⁰₁) in the oracle;
* `Martin.eval_continuous_in_oracle` is implicit: reductions are continuous.

This is the foundation any future finite-extension (Kleene–Post style) or
forcing argument will stand on.
-/
import MartinsConjecture.TopologicalTriviality

open scoped Computability
open OracleCode

namespace OracleCode

/-- **The use principle**: a converging oracle computation depends only on a
finite prefix of the oracle. -/
theorem eval_locality :
    ∀ (c : OracleCode) (x y : ℕ) (X : ℕ → Bool),
      y ∈ eval (Cantor.toPFun X) c x →
      ∃ L, ∀ X' : ℕ → Bool, (∀ n, n < L → X' n = X n) →
        y ∈ eval (Cantor.toPFun X') c x := by
  intro c
  induction c with
  | zero => exact fun x y X h => ⟨0, fun X' _ => h⟩
  | succ => exact fun x y X h => ⟨0, fun X' _ => h⟩
  | left => exact fun x y X h => ⟨0, fun X' _ => h⟩
  | right => exact fun x y X h => ⟨0, fun X' _ => h⟩
  | oracle =>
    intro x y X h
    refine ⟨x + 1, fun X' hX' => ?_⟩
    have hx : X' x = X x := hX' x (Nat.lt_succ_self x)
    simpa [Cantor.toPFun, hx] using h
  | pair cf cg ihf ihg =>
    intro x y X h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_eval_pair.mp h
    obtain ⟨L1, hL1⟩ := ihf x a X ha
    obtain ⟨L2, hL2⟩ := ihg x b X hb
    refine ⟨max L1 L2, fun X' hX' => ?_⟩
    exact mem_eval_pair.mpr
      ⟨a, hL1 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_left _ _))),
       b, hL2 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_right _ _))), rfl⟩
  | comp cf cg ihf ihg =>
    intro x y X h
    obtain ⟨b, hb, hy⟩ := mem_eval_comp.mp h
    obtain ⟨L1, hL1⟩ := ihg x b X hb
    obtain ⟨L2, hL2⟩ := ihf b y X hy
    refine ⟨max L1 L2, fun X' hX' => ?_⟩
    exact mem_eval_comp.mpr
      ⟨b, hL1 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_left _ _))),
       hL2 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_right _ _)))⟩
  | prec cf cg ihf ihg =>
    intro x y X
    have H : ∀ (a m y₀ : ℕ),
        y₀ ∈ Nat.rec (motive := fun _ => Part ℕ) (eval (Cantor.toPFun X) cf a)
          (fun k IH => IH >>= fun i =>
            eval (Cantor.toPFun X) cg (Nat.pair a (Nat.pair k i))) m →
        ∃ L, ∀ X' : ℕ → Bool, (∀ n, n < L → X' n = X n) →
          y₀ ∈ Nat.rec (motive := fun _ => Part ℕ) (eval (Cantor.toPFun X') cf a)
            (fun k IH => IH >>= fun i =>
              eval (Cantor.toPFun X') cg (Nat.pair a (Nat.pair k i))) m := by
      intro a m
      induction m with
      | zero => exact fun y₀ h => ihf a y₀ X h
      | succ m ihm =>
        intro y₀ h
        obtain ⟨i, hi, hy⟩ := Part.mem_bind_iff.mp h
        obtain ⟨L1, hL1⟩ := ihm i hi
        obtain ⟨L2, hL2⟩ := ihg (Nat.pair a (Nat.pair m i)) y₀ X hy
        refine ⟨max L1 L2, fun X' hX' => ?_⟩
        exact Part.mem_bind_iff.mpr
          ⟨i, hL1 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_left _ _))),
           hL2 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_right _ _)))⟩
    exact H (Nat.unpair x).1 (Nat.unpair x).2 y
  | rfind cf ihf =>
    intro x y X h
    obtain ⟨h0, hmin⟩ := mem_eval_rfind.mp h
    obtain ⟨L0, hL0⟩ := ihf (Nat.pair x y) 0 X h0
    -- Choose, for each stage `m < y`, a nonzero witness and a use bound.
    have key : ∀ m, ∃ Lm, ∀ X' : ℕ → Bool, (∀ n, n < Lm → X' n = X n) →
        m < y → ∃ z ∈ eval (Cantor.toPFun X') cf (Nat.pair x m), z ≠ 0 := by
      intro m
      by_cases hm : m < y
      · obtain ⟨z, hz, hnz⟩ := hmin m hm
        obtain ⟨Lm, hLm⟩ := ihf (Nat.pair x m) z X hz
        exact ⟨Lm, fun X' hX' _ => ⟨z, hLm X' hX', hnz⟩⟩
      · exact ⟨0, fun X' _ hm' => absurd hm' hm⟩
    choose Lw hLw using key
    refine ⟨max L0 ((Finset.range y).sup Lw), fun X' hX' => ?_⟩
    refine mem_eval_rfind.mpr
      ⟨hL0 X' (fun n hn => hX' n (lt_of_lt_of_le hn (le_max_left _ _))), fun m hm => ?_⟩
    refine hLw m X' (fun n hn => hX' n (lt_of_lt_of_le hn ?_)) hm
    exact le_trans (Finset.le_sup (Finset.mem_range.mpr hm)) (le_max_right _ _)

end OracleCode

namespace Martin

open Cantor

/-- Convergence-to-a-value is an **open** condition on the oracle. -/
theorem isOpen_mem_eval (c : OracleCode) (x y : ℕ) :
    IsOpen {X : ℕ → Bool | y ∈ eval (toPFun X) c x} := by
  rw [isOpen_pi_iff]
  intro X hX
  obtain ⟨L, hL⟩ := eval_locality c x y X hX
  refine ⟨Finset.range L, fun i => {X i}, fun i _ => ⟨isOpen_discrete _, rfl⟩, ?_⟩
  intro X' hX'
  exact hL X' fun n hn => hX' n (Finset.mem_range.mpr hn)

/-- **The jump predicate is open (Σ⁰₁) in the oracle** — sharpening
`measurableSet_jumpP`. -/
theorem isOpen_jumpP (e : ℕ) : IsOpen {X : ℕ → Bool | jumpP (toPFun X) e} := by
  have hset : {X : ℕ → Bool | jumpP (toPFun X) e}
      = ⋃ y, {X | y ∈ eval (toPFun X) (ofNatCode e) e} := by
    ext X
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, jumpP, Part.dom_iff_mem]
  rw [hset]
  exact isOpen_iUnion fun y => isOpen_mem_eval _ _ _

#print axioms eval_locality
#print axioms isOpen_jumpP

end Martin
