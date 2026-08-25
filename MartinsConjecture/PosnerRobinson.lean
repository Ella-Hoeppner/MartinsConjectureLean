/-
The full Posner–Robinson theorem for an arbitrary non-computable point `A`:

  `∃ G, (A ⊕ G) ≡ᵀ G′`.

Unlike the cone fragment (which builds `G` from Friedberg jump inversion applied
to `A ⊕ 0′` and therefore forces `0′ ≤ᵀ G′`), the genuine theorem must avoid
`0′ ≤ᵀ G′`.  We take the **Friedberg finite-extension real coded by `A`**,
`G := jReal A` (the `jstr`/`jReal` construction of `JumpInversion.lean` with the
coding oracle `C := A`).  For this `G` the following hold *unconditionally*
(no `0′ ≤ᵀ A` hypothesis):

* `A ≤ᵀ G′`     — `OracleCode.C_le_jump A` (decode `A` from the coding positions,
  reconstructing the construction from `G′`).  This is the coding half.
* `G ≤ᵀ G′`     — `Cantor.le_jump` (trivial).
* `A, G ≤ᵀ A ⊕ G` — join projections.

Hence the **easy direction `A ⊕ G ≤ᵀ G′`** is fully proved by reuse.

The **read-back `G′ ≤ᵀ A ⊕ G`** is the deep, new content.  Via
`OracleCode.dom_iff_jExists A e`, deciding `e ∈ G′` is equivalent to deciding the
`Σ₁` predicate `jExists (jstr A e) e` ("some `0/1` extension of the stage-`e`
string forces `Φ_e(e)↓`").  The construction's stage-`e` string `jstr A e` is a
prefix of `G`, so this predicate is `G`-c.e.; the Posner–Robinson device makes it
`A ⊕ G`-*decidable* by coding, at each stage, one bit of `A` that lets the
reconstruction recover stage lengths without re-deciding the `Σ₁` question.

We prove everything up to that read-back and isolate the missing content as the
single explicit hypothesis `ReadBack A`.
-/
import MartinsConjecture.JumpInversion

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-! ### The Posner–Robinson real for `A`

We reuse the Friedberg construction `jReal` with coding oracle `C := A`.  Write
`prReal A := jReal A` and `prStr A := jstr A`.  These abbreviations keep the
intent (a *Posner–Robinson* real) legible while inheriting every structural
lemma proved in `JumpInversion.lean`. -/

/-- The Posner–Robinson real for `A`: the Friedberg finite-extension real whose
coding column carries `A`. -/
noncomputable def prReal (A : ℕ → Bool) : ℕ → Bool := jReal A

/-- The stage-`e` string of the Posner–Robinson construction for `A`. -/
noncomputable def prStr (A : ℕ → Bool) : ℕ → List ℕ := jstr A

theorem prReal_eq (A : ℕ → Bool) : prReal A = jReal A := rfl
theorem prStr_eq (A : ℕ → Bool) : prStr A = jstr A := rfl

/-! ### The coding half: `A ≤ᵀ G′` (unconditional) -/

/-- **The coding reduction `A ≤ᵀ (prReal A)′`.**  Directly `OracleCode.C_le_jump`
with `C := A`: the coding bit `A e` sits at the last position of stage `e+1`, and
the stage lengths are reconstructible from `(prReal A)′`.  Crucially this needs
**no** hypothesis on `A` — in particular it does not force `0′ ≤ᵀ (prReal A)′`. -/
theorem A_le_jump_prReal (A : ℕ → Bool) : A ≤ₜ Cantor.jump (prReal A) :=
  C_le_jump A

/-- `G ≤ᵀ G′` for the Posner–Robinson real (trivial jump reduction). -/
theorem prReal_le_jump (A : ℕ → Bool) : prReal A ≤ₜ Cantor.jump (prReal A) :=
  le_jump (prReal A)

/-! ### The easy direction: `A ⊕ G ≤ᵀ G′` -/

/-- **`A ⊕ (prReal A) ≤ᵀ (prReal A)′`.**  Both summands are below the jump:
`A ≤ᵀ G′` by coding and `G ≤ᵀ G′` trivially; the join is a least upper bound. -/
theorem join_le_jump_prReal (A : ℕ → Bool) :
    Cantor.join A (prReal A) ≤ₜ Cantor.jump (prReal A) :=
  join_le (A_le_jump_prReal A) (prReal_le_jump A)

/-! ### The read-back `G′ ≤ᵀ A ⊕ G`, reduced to the `Σ₁` stage decision

`e ∈ G′ ⟺ jExists (prStr A e) e` by `dom_iff_jExists`.  So the read-back is
exactly the statement that `e ↦ [jExists (jstr A e) e]` is recursive in `A ⊕ G`.
We isolate this as `ReadBack A`. -/

/-- The Posner–Robinson **read-back hypothesis**: the stage decision
`e ↦ [jExists (jstr A e) e]` is recursive in `A ⊕ (prReal A)`.  Equivalently (by
`dom_iff_jExists`), `(prReal A)′ ≤ᵀ A ⊕ (prReal A)` — the hard/new half of
Posner–Robinson.  This is the *only* unproved ingredient. -/
def ReadBack (A : ℕ → Bool) : Prop :=
  Nat.RecursiveIn {Cantor.toPFun (Cantor.join A (prReal A))}
    (fun e : ℕ => ((if jExists (jstr A e) e then 1 else 0 : ℕ) : Part ℕ))

/-- Under `ReadBack A`, the jump of the Posner–Robinson real is `A ⊕ G`-computable:
`(prReal A)′ ≤ᵀ A ⊕ (prReal A)`. -/
theorem jump_prReal_le_join (A : ℕ → Bool) (h : ReadBack A) :
    Cantor.jump (prReal A) ≤ₜ Cantor.join A (prReal A) := by
  rw [Cantor.le_iff_bitg]
  refine h.of_eq fun e => ?_
  have hbit : (if jExists (jstr A e) e then (1 : ℕ) else 0)
      = bitg (Cantor.jump (prReal A)) e := by
    rw [bitg]
    by_cases hj : jExists (jstr A e) e
    · rw [if_pos hj]
      have : Cantor.jump (prReal A) e = true := by
        rw [Cantor.jump]; exact decide_eq_true ((dom_iff_jExists A e).mpr hj)
      rw [this]; rfl
    · rw [if_neg hj]
      have : Cantor.jump (prReal A) e = false := by
        rw [Cantor.jump]
        exact decide_eq_false (fun hd => hj ((dom_iff_jExists A e).mp hd))
      rw [this]; rfl
  rw [hbit]

/-- **The read-back hypothesis is *exactly* the missing reduction.**
`ReadBack A ↔ (prReal A)′ ≤ᵀ A ⊕ (prReal A)`.  This pins down the bracket: it
assumes neither more nor less than the hard half of Posner–Robinson for the
constructed real.  (`→` is `jump_prReal_le_join`; `←` reruns the `dom_iff_jExists`
identification of the bit-graph.) -/
theorem readBack_iff (A : ℕ → Bool) :
    ReadBack A ↔ Cantor.jump (prReal A) ≤ₜ Cantor.join A (prReal A) := by
  constructor
  · exact jump_prReal_le_join A
  · intro h
    have hbg := Cantor.le_iff_bitg.mp h
    refine hbg.of_eq fun e => ?_
    -- `bitg (jump G) e = [jExists (jstr A e) e]`
    rw [bitg]
    by_cases hj : jExists (jstr A e) e
    · rw [if_pos hj]
      have : Cantor.jump (prReal A) e = true := by
        rw [Cantor.jump]; exact decide_eq_true ((dom_iff_jExists A e).mpr hj)
      rw [this]; rfl
    · rw [if_neg hj]
      have : Cantor.jump (prReal A) e = false := by
        rw [Cantor.jump]
        exact decide_eq_false (fun hd => hj ((dom_iff_jExists A e).mp hd))
      rw [this]; rfl

/-! ### Assembly -/

/-- **Posner–Robinson, conditional on the read-back.**  For the Posner–Robinson
real `G := prReal A`, we have `A ⊕ G ≡ᵀ G′` whenever the read-back holds.  The
`≤` direction (`A ⊕ G ≤ᵀ G′`) is unconditional; the `≥` direction is exactly
`ReadBack A`. -/
theorem posnerRobinson_of_readBack (A : ℕ → Bool) (h : ReadBack A) :
    Cantor.join A (prReal A) ≡ₜ Cantor.jump (prReal A) :=
  ⟨join_le_jump_prReal A, jump_prReal_le_join A h⟩

/-- **The full Posner–Robinson theorem** (conditional on the read-back for the
constructed real): for every `A` there is a `G` with `A ⊕ G ≡ᵀ G′`. -/
theorem posnerRobinsonFull (A : ℕ → Bool) (h : ReadBack A) :
    ∃ G : ℕ → Bool, Cantor.join A G ≡ₜ Cantor.jump G :=
  ⟨prReal A, posnerRobinson_of_readBack A h⟩

/-! ### The read-back is achievable above `0′` (sanity: the bracket is not vacuous)

For `A ≥ᵀ 0′` the Friedberg analysis already gives `(prReal A)′ ≤ᵀ A`
(`jump_jReal_le`), whence `(prReal A)′ ≤ᵀ A ⊕ (prReal A)` and `ReadBack A` holds.
This both discharges the bracket on the cone above `0′` and recovers the cone
fragment `A ⊕ G ≡ᵀ G′` there — confirming `ReadBack` is a genuine, satisfiable
hypothesis (the open content is precisely its extension *below* `0′`). -/
theorem readBack_of_zero_le (A : ℕ → Bool)
    (hA : Cantor.jump (fun _ : ℕ => false) ≤ₜ A) : ReadBack A := by
  rw [readBack_iff]
  -- `(prReal A)′ ≤ᵀ A ≤ᵀ A ⊕ (prReal A)`
  exact (jump_jReal_le A hA).trans (Cantor.left_le_join A (prReal A))

/-- **Posner–Robinson on the cone above `0′`, via the Posner–Robinson real.**
Unconditional for `A ≥ᵀ 0′`: `A ⊕ G ≡ᵀ G′`.  (This is the cone case the general
theorem must go beyond; here it drops out of the bracketed development by
discharging `ReadBack` from `jump_jReal_le`.) -/
theorem posnerRobinson_of_zero_le (A : ℕ → Bool)
    (hA : Cantor.jump (fun _ : ℕ => false) ≤ₜ A) :
    Cantor.join A (prReal A) ≡ₜ Cantor.jump (prReal A) :=
  posnerRobinson_of_readBack A (readBack_of_zero_le A hA)

/-- **The bracket is genuinely nontrivial (not accidentally provable).**  If `A`
is computable then `ReadBack A` *fails*: it would give
`(prReal A)′ ≤ᵀ A ⊕ prReal A ≡ᵀ prReal A`, contradicting jump strictness
`¬ (prReal A)′ ≤ᵀ prReal A`.  So `ReadBack` cannot be discharged unconditionally —
the real work of full Posner–Robinson (a marker-coded construction whose stage
lengths are `A ⊕ G`-recoverable below `0′`) is exactly what it abstracts. -/
theorem not_readBack_of_computable (A : ℕ → Bool) (hA : Computable A) :
    ¬ ReadBack A := by
  intro h
  rw [readBack_iff] at h
  -- `A` computable ⟹ `A ≤ᵀ prReal A` ⟹ `A ⊕ prReal A ≤ᵀ prReal A`
  have hAle : A ≤ₜ prReal A := Cantor.le_of_computable hA
  have hjoin : Cantor.join A (prReal A) ≤ₜ prReal A :=
    Cantor.join_le hAle (Cantor.le.refl (prReal A))
  exact not_jump_le (prReal A) (h.trans hjoin)

end OracleCode

-- Axiom hygiene: everything below the bracket uses only the standard axioms.
#print axioms OracleCode.A_le_jump_prReal
#print axioms OracleCode.join_le_jump_prReal
#print axioms OracleCode.jump_prReal_le_join
#print axioms OracleCode.readBack_iff
#print axioms OracleCode.readBack_of_zero_le
#print axioms OracleCode.posnerRobinson_of_zero_le
#print axioms OracleCode.not_readBack_of_computable
#print axioms OracleCode.posnerRobinson_of_readBack
#print axioms OracleCode.posnerRobinsonFull
