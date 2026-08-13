/-
Degree theory on Cantor space.

Points of Cantor space `2^ω` are represented as `X : ℕ → Bool`; they embed
into oracles via `Cantor.toPFun` (total 0/1-valued partial functions), which
induces Turing reducibility `≤ₜ`, equivalence `≡ₜ`, and the jump on points.

Main results:
* `Cantor.lt_jump : X <ₜ Cantor.jump X` — jump strictness on Cantor space.
* `Cantor.le_bot_iff` — the bottom degree consists exactly of the computable
  points (sanity anchor: the reducibility is not vacuous).
-/
import MartinsConjecture.Jump

open scoped Computability
open OracleCode

attribute [local instance] Classical.propDecidable

namespace Cantor

/-- Embed a point of Cantor space as a (total, 0/1-valued) oracle. -/
def toPFun (X : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (cond (X n) 1 0)

/-- Turing reducibility between points of Cantor space. -/
def le (X Y : ℕ → Bool) : Prop := toPFun X ≤ᵀ toPFun Y

@[inherit_doc] scoped infix:50 " ≤ₜ " => Cantor.le

/-- Turing equivalence between points of Cantor space. -/
def equiv (X Y : ℕ → Bool) : Prop := X ≤ₜ Y ∧ Y ≤ₜ X

@[inherit_doc] scoped infix:50 " ≡ₜ " => Cantor.equiv

/-- Strict Turing reducibility between points of Cantor space. -/
def lt (X Y : ℕ → Bool) : Prop := X ≤ₜ Y ∧ ¬ Y ≤ₜ X

@[inherit_doc] scoped infix:50 " <ₜ " => Cantor.lt

protected theorem le.refl (X : ℕ → Bool) : X ≤ₜ X := TuringReducible.refl _

protected theorem le.trans {X Y Z : ℕ → Bool} (h1 : X ≤ₜ Y) (h2 : Y ≤ₜ Z) : X ≤ₜ Z :=
  TuringReducible.trans h1 h2

protected theorem equiv.refl (X : ℕ → Bool) : X ≡ₜ X := ⟨le.refl X, le.refl X⟩

protected theorem equiv.symm {X Y : ℕ → Bool} (h : X ≡ₜ Y) : Y ≡ₜ X := ⟨h.2, h.1⟩

protected theorem equiv.trans {X Y Z : ℕ → Bool} (h1 : X ≡ₜ Y) (h2 : Y ≡ₜ Z) : X ≡ₜ Z :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- The Turing jump of a point of Cantor space, as a point of Cantor space. -/
noncomputable def jump (X : ℕ → Bool) : ℕ → Bool :=
  fun e => decide (jumpP (toPFun X) e)

theorem toPFun_jump (X : ℕ → Bool) : toPFun (jump X) = jumpFn (toPFun X) := by
  funext e
  by_cases h : jumpP (toPFun X) e <;> simp [toPFun, jump, jumpFn, h]

theorem le_jump (X : ℕ → Bool) : X ≤ₜ jump X := by
  unfold le
  rw [toPFun_jump]
  exact turingReducible_jumpFn _

theorem not_jump_le (X : ℕ → Bool) : ¬ jump X ≤ₜ X := by
  unfold le
  rw [toPFun_jump]
  exact jumpFn_not_turingReducible _

/-- **Jump strictness on Cantor space.** -/
theorem lt_jump (X : ℕ → Bool) : X <ₜ jump X := ⟨le_jump X, not_jump_le X⟩

/-- If `X` is obtained from `Z` by precomposition with a primitive recursive
index transformation, then `X ≤ₜ Z`. -/
theorem le_of_precomp {X Z : ℕ → Bool} {g : ℕ → ℕ} (hg : Nat.Primrec g)
    (h : ∀ n, X n = Z (g n)) : X ≤ₜ Z := by
  refine RecursiveIn.iff_nat.mpr ?_
  have h1 : Nat.RecursiveIn {toPFun Z} (fun n : ℕ => ((g n : ℕ) : Part ℕ) >>= toPFun Z) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) hg.recursiveIn
  refine h1.of_eq fun n => ?_
  rw [Part.coe_some,
    show (Part.some (g n) >>= toPFun Z) = toPFun Z (g n) from Part.bind_some _ _]
  simp [toPFun, h n]

/-! ### Join: the upper semilattice structure -/

/-- The join (recursive join) of two points: even bits from `X`, odd from `Y`. -/
def join (X Y : ℕ → Bool) : ℕ → Bool :=
  fun n => if n % 2 = 0 then X (n / 2) else Y (n / 2)

theorem left_le_join (X Y : ℕ → Bool) : X ≤ₜ join X Y := by
  refine le_of_precomp (g := fun n => 2 * n)
    (Primrec.nat_iff.mp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    fun n => ?_
  rw [join, if_pos (by omega)]
  congr 1
  omega

theorem right_le_join (X Y : ℕ → Bool) : Y ≤ₜ join X Y := by
  refine le_of_precomp (g := fun n => 2 * n + 1)
    (Primrec.nat_iff.mp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
    fun n => ?_
  rw [join, if_neg (by omega)]
  congr 1
  omega

/-- The join is a least upper bound: anything computing both `X` and `Y`
computes their join. -/
theorem join_le {X Y Z : ℕ → Bool} (hX : X ≤ₜ Z) (hY : Y ≤ₜ Z) : join X Y ≤ₜ Z := by
  refine RecursiveIn.iff_nat.mpr ?_
  obtain ⟨cX, hcX⟩ := OracleCode.exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp hX)
  obtain ⟨cY, hcY⟩ := OracleCode.exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp hY)
  set g : ℕ → ℕ := fun n => n / 2 with hg
  have hgP : Nat.Primrec g := Primrec.nat_iff.mp
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  set comb : ℕ → ℕ := fun w =>
    (1 - (Nat.unpair w).1 % 2) * (Nat.unpair (Nat.unpair w).2).1
      + ((Nat.unpair w).1 % 2) * (Nat.unpair (Nat.unpair w).2).2 with hcomb
  have hcombP : Nat.Primrec comb := by
    rw [hcomb]
    refine Primrec.nat_iff.mp ?_
    have hn : Primrec fun w : ℕ => (Nat.unpair w).1 := Primrec.fst.comp Primrec.unpair
    have hs : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have ht : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp (Primrec.const 1)
          (Primrec.nat_mod.comp hn (Primrec.const 2))) hs)
      (Primrec.nat_mul.comp (Primrec.nat_mod.comp hn (Primrec.const 2)) ht)
  have hsX : Nat.RecursiveIn {toPFun Z}
      (fun n : ℕ => ((g n : ℕ) : Part ℕ) >>= OracleCode.eval (toPFun Z) cX) :=
    Nat.RecursiveIn.comp (OracleCode.eval_recursiveIn (toPFun Z) cX) hgP.recursiveIn
  have hsY : Nat.RecursiveIn {toPFun Z}
      (fun n : ℕ => ((g n : ℕ) : Part ℕ) >>= OracleCode.eval (toPFun Z) cY) :=
    Nat.RecursiveIn.comp (OracleCode.eval_recursiveIn (toPFun Z) cY) hgP.recursiveIn
  have hid : Nat.RecursiveIn {toPFun Z} (fun n : ℕ => ((n : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hP : Nat.RecursiveIn {toPFun Z} (fun n : ℕ =>
      Nat.pair <$> ((n : ℕ) : Part ℕ) <*>
        (Nat.pair <$> (((g n : ℕ) : Part ℕ) >>= OracleCode.eval (toPFun Z) cX)
          <*> (((g n : ℕ) : Part ℕ) >>= OracleCode.eval (toPFun Z) cY))) :=
    Nat.RecursiveIn.pair hid (Nat.RecursiveIn.pair hsX hsY)
  have hF := Nat.RecursiveIn.comp hcombP.recursiveIn hP
  refine hF.of_eq fun n => ?_
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [hcX, hcY,
    show (Part.some (g n) >>= toPFun X) = toPFun X (g n) from Part.bind_some _ _,
    show (Part.some (g n) >>= toPFun Y) = toPFun Y (g n) from Part.bind_some _ _]
  simp only [toPFun, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind,
    Part.bind_some]
  simp only [hcomb, Nat.unpair_pair, hg, join]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [if_pos hn]
    cases hX2 : X (n / 2) <;> simp [hn, hX2]
  · rw [if_neg (by omega)]
    cases hY2 : Y (n / 2) <;> simp [hn, hY2]

/-! ### The bottom degree: sanity anchors -/

theorem toPFun_const_false : toPFun (fun _ => false) = fun _ => Part.some 0 := by
  funext n
  simp [toPFun]

/-- A point is below the constantly-`false` point iff its characteristic
function is partial recursive: the bottom degree consists exactly of the
computable points. -/
theorem le_bot_iff {X : ℕ → Bool} : X ≤ₜ (fun _ => false) ↔ Partrec (toPFun X) := by
  constructor
  · intro h
    unfold le at h
    rw [toPFun_const_false] at h
    exact TuringReducible.partrec_of_const h
  · intro h
    exact h.turingReducible

/-- Computable points are in the bottom degree. -/
theorem le_of_computable {X Y : ℕ → Bool} (h : Computable X) : X ≤ₜ Y := by
  have h1 : Computable fun n => (cond (X n) 1 0 : ℕ) :=
    Computable.cond h (Computable.const 1) (Computable.const 0)
  exact Partrec.turingReducible h1.partrec

/-- The jump of any point is strictly above every computable point;
in particular `∅′` is not computable. -/
theorem not_computable_jump (X : ℕ → Bool) : ¬ Computable (jump X) := by
  intro h
  exact not_jump_le X (le_of_computable h)

end Cantor
