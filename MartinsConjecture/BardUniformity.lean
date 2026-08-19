/-
**Toward Bard's Lemma 3.4** (arXiv:1907.10766): a uniformly-invariant function
has a *computable* uniformity function.  Removing this lemma's hypothesis would
upgrade both Lachlan's theorem and Part I (for uniform functions) from
computable uniformity to bare uniform invariance.

Bard's construction encodes an equivalence-witness pair `(i,j)` into unary
prefixes and processes it with fixed machines, so that applying the (arbitrary)
uniformity `u` to *fixed* index pairs yields fixed `f`-level transforms whose
composition is computable in `(i,j)`.

This file builds the reusable fixed machines — **strip-first-bit**, **prepend-0**,
**prepend-1** — as explicit oracle-generic codes, with their `EquivVia` witnesses
`w ≡ᵀ 0⌢w` and `w ≡ᵀ 1⌢w`.  Feeding these fixed equivalences through any
uniformity `u` gives the fixed `f`-level "shift" transforms `β, γ`
(`beta_transform`, `gamma_transform`) that are the load-bearing pieces of the
computable-uniformity construction. -/
import MartinsConjecture.BardLocal

open scoped Computability
open OracleCode Cantor

namespace Martin

attribute [local instance] Classical.propDecidable

/-- Strip the first bit: `shiftReal w n = w (n+1)`. -/
def shiftReal (w : ℕ → Bool) : ℕ → Bool := fun n => w (n + 1)

/-- Prepend bit `b`: `preReal b w 0 = b`, `preReal b w (n+1) = w n`. -/
def preReal (b : Bool) (w : ℕ → Bool) : ℕ → Bool := fun n => if n = 0 then b else w (n - 1)

/-- **Strip machine**: `Φ_s^w = shiftReal w`, i.e. query the oracle at `n+1`. -/
def sCode : OracleCode := .comp .oracle .succ

theorem eval_sCode (w : ℕ → Bool) : eval (toPFun w) sCode = toPFun (shiftReal w) := by
  funext n
  rw [sCode, eval_comp,
    show eval (toPFun w) OracleCode.succ n = Part.some (n + 1) from rfl,
    show (Part.some (n + 1) >>= eval (toPFun w) OracleCode.oracle)
      = eval (toPFun w) OracleCode.oracle (n + 1) from Part.bind_some _ _, eval_oracle,
    toPFun_eq_bitg]
  rfl

/-- **Prepend machine** for bit `b`: `Φ_{preCode b}^w = preReal b w`, built with a
`prec` (`n = 0 ↦ b`, `n+1 ↦ w n`). -/
def preCode (b : Bool) : OracleCode :=
  .comp (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
    (.pair (const 0) idCode)

theorem eval_preCode (b : Bool) (w : ℕ → Bool) :
    eval (toPFun w) (preCode b) = toPFun (preReal b w) := by
  have key : ∀ n, eval (toPFun w)
      (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
      (Nat.pair 0 n) = Part.some (bitg (preReal b w) n) := by
    intro n
    induction n with
    | zero =>
      rw [eval_prec_pair]
      show eval (toPFun w) (const (bitg (fun _ => b) 0)) 0 = Part.some (bitg (preReal b w) 0)
      rw [eval_const]; cases b <;> rfl
    | succ m ih =>
      rw [eval_prec_pair] at ih ⊢
      show ((Nat.rec (motive := fun _ => Part ℕ) (eval (toPFun w) (const (bitg (fun _ => b) 0)) 0)
          (fun y IH => IH >>= fun i =>
            eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair y i))) m)
          >>= fun i => eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair m i)))
        = Part.some (bitg (preReal b w) (m + 1))
      rw [ih,
        show (Part.some (bitg (preReal b w) m) >>= fun i =>
            eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair m i)))
          = eval (toPFun w) (.comp .oracle (.comp .left .right))
              (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m))) from Part.bind_some _ _,
        eval_comp,
        show eval (toPFun w) (.comp OracleCode.left OracleCode.right)
            (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m))) = Part.some m from by
          rw [eval_comp,
            show eval (toPFun w) OracleCode.right (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m)))
              = Part.some (Nat.pair m (bitg (preReal b w) m)) from by
                show Part.some (Nat.unpair (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m)))).2 = _
                rw [Nat.unpair_pair],
            show (Part.some (Nat.pair m (bitg (preReal b w) m)) >>= eval (toPFun w) OracleCode.left)
              = eval (toPFun w) OracleCode.left (Nat.pair m (bitg (preReal b w) m)) from Part.bind_some _ _,
            eval_left_val]
          show Part.some (Nat.unpair (Nat.pair m (bitg (preReal b w) m))).1 = Part.some m
          rw [Nat.unpair_pair],
        show (Part.some m >>= eval (toPFun w) OracleCode.oracle)
          = eval (toPFun w) OracleCode.oracle m from Part.bind_some _ _, eval_oracle, toPFun_eq_bitg]
      congr 1
  funext n
  rw [preCode, eval_comp, eval_pair_eq, eval_const, eval_idCode]
  simp only [Part.map_some, Part.bind_some]
  rw [show (Part.some (Nat.pair 0 n) >>= eval (toPFun w)
        (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right))))
      = eval (toPFun w) (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
          (Nat.pair 0 n) from Part.bind_some _ _, key n, toPFun_eq_bitg]

/-- Stripping the prepended bit is the identity: `shiftReal (preReal b w) = w`. -/
theorem shiftReal_preReal (b : Bool) (w : ℕ → Bool) : shiftReal (preReal b w) = w := by
  funext n; simp [shiftReal, preReal]

/-- **The prepend/strip equivalence**: `w ≡ᵀ (b⌢w)` via the fixed index pair
`(preCode b, sCode)`, for *every* `w`. -/
theorem equivVia_preReal (b : Bool) (w : ℕ → Bool) :
    EquivVia w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) := by
  constructor
  · rw [ofNatCode_encodeCode, eval_preCode]
  · rw [ofNatCode_encodeCode, eval_sCode, shiftReal_preReal]

/-- **The fixed `f`-level "shift" transform** `β` (for `b = false`) / `γ`
(for `b = true`).  Because `(preCode b, sCode)` witnesses `w ≡ᵀ (b⌢w)` for *every*
`w`, applying *any* uniformity function `u` for `F` yields a single fixed index —
`u(⟨preCode b, sCode⟩).1` — that computes `F(b⌢w)` from `F(w)` uniformly in `w`.
This is the load-bearing step of Bard's computable-uniformity construction. -/
theorem shift_transform {F : (ℕ → Bool) → ℕ → Bool} {u : ℕ × ℕ → ℕ × ℕ}
    (hu : ∀ X Y i j, EquivVia X Y i j → EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2)
    (b : Bool) (w : ℕ → Bool) :
    eval (toPFun (F w))
        (ofNatCode (u (encodeCode (preCode b), encodeCode sCode)).1) = toPFun (F (preReal b w)) :=
  (hu w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) (equivVia_preReal b w)).1

/-- The backward fixed transform `β'`/`γ'`: `u(⟨preCode b, sCode⟩).2` computes
`F(w)` from `F(b⌢w)` uniformly in `w`. -/
theorem unshift_transform {F : (ℕ → Bool) → ℕ → Bool} {u : ℕ × ℕ → ℕ × ℕ}
    (hu : ∀ X Y i j, EquivVia X Y i j → EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2)
    (b : Bool) (w : ℕ → Bool) :
    eval (toPFun (F (preReal b w)))
        (ofNatCode (u (encodeCode (preCode b), encodeCode sCode)).2) = toPFun (F w) :=
  (hu w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) (equivVia_preReal b w)).2

/-! ### The `e`-fold composition of the monoid

To build `β^e` (apply the fixed transform `β` `e` times) we iterate the computable
composition `trE (ofNatCode g)` — keeping the *accumulator* in `trE`'s second
(primrec-friendly) slot, so the fixed step `g` stays in the first slot. -/

/-- `iterTrE g base e` : the index of "run `Φ_base`, with `Φ_g` applied to the
oracle `e` times first".  `Φ_{iterTrE g base e}^Y = Φ_base^{(Φ_g)^e Y}`. -/
def iterTrE (g base : ℕ) (e : ℕ) : ℕ :=
  Nat.rec base (fun _ prev => trE (ofNatCode g) prev) e

@[simp] theorem iterTrE_zero (g base : ℕ) : iterTrE g base 0 = base := rfl

theorem iterTrE_succ (g base e : ℕ) :
    iterTrE g base (e + 1) = trE (ofNatCode g) (iterTrE g base e) := rfl

/-- **The `e`-fold transform.**  If the fixed index `g` transforms `F w ↦ F (σ w)`
for every `w`, then `iterTrE g ⟨oracle⟩ e` transforms `F w ↦ F (σ^[e] w)` — the
`e`-fold iterate of `σ` — uniformly in `w`. -/
theorem eval_iterTrE {F : (ℕ → Bool) → ℕ → Bool} {g : ℕ} {σ : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ w, eval (toPFun (F w)) (ofNatCode g) = toPFun (F (σ w))) :
    ∀ (e : ℕ) (w : ℕ → Bool),
      eval (toPFun (F w)) (ofNatCode (iterTrE g (encodeCode OracleCode.oracle) e))
        = toPFun (F (σ^[e] w)) := by
  intro e
  induction e with
  | zero =>
    intro w
    rw [iterTrE_zero, Function.iterate_zero, id, ofNatCode_encodeCode, eval_oracle]
  | succ e ih =>
    intro w
    rw [iterTrE_succ, eval_trE_comp (hg w) (iterTrE g (encodeCode OracleCode.oracle) e), ih (σ w),
      Function.iterate_succ_apply]

#print axioms eval_preCode
#print axioms equivVia_preReal
#print axioms shift_transform
#print axioms eval_iterTrE

end Martin
