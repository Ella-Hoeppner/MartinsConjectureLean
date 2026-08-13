/-
Uniformly pointed join-cones: controlled congruence of canonical
representatives.

The map `X ↦ join W X` embeds Cantor space onto a "uniformly pointed tree"
inside the cone above `W`: every degree above `W` is realized (`join` lemmas
in `CantorPoints.lean`), the base `W` is recovered from any branch by one
fixed machine (the even bits), and — the substantive result here —

**controlled congruence** (`equivVia_join_uniform`): index witnesses for
`X ≡ₜ X'` are transformed into index witnesses for
`join W X ≡ₜ join W X'` by a computable function of the indices that does
not depend on `W`, `X`, or `X'`.

This is the standard mechanism by which uniform-invariance arguments
(Steel's classification of jump operators; Slaman–Steel) control the
behaviour of a function across different representatives of the same degree:
on canonical representatives, equivalence witnesses are computable data.
Built from the oracle-splicing machinery of `Jump.lean`/`JumpInvariance.lean`
and the s-m-n layer of `UniformJump.lean`.
-/
import MartinsConjecture.UniformJump
import MartinsConjecture.OrderPreservingCase

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Explicit codes for the join-reduction -/

/-- A fixed code for the primitive recursive map `k ↦ 2k + 1` (odd position). -/
private noncomputable def cOdd : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1))))).choose

private theorem cOdd_spec (O : ℕ →. ℕ) (k : ℕ) :
    eval O cOdd k = Part.some (2 * k + 1) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1))))).choose_spec O) k

/-- A fixed code for `k ↦ k / 2`. -/
private noncomputable def cHalf : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2))))).choose

private theorem cHalf_spec (O : ℕ →. ℕ) (k : ℕ) :
    eval O cHalf k = Part.some (k / 2) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2))))).choose_spec O) k

/-- The fixed "mixer": on `w = pair (pair v₁ v₂) n`, return `v₁` if `n` is
even and `v₂` if `n` is odd. -/
private noncomputable def cMix : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp (Primrec.const 1)
          (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 2)))
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.nat_mul.comp
        (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 2))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))))).choose

private theorem cMix_spec (O : ℕ →. ℕ) (w : ℕ) :
    eval O cMix w = Part.some
      ((1 - (Nat.unpair w).2 % 2) * (Nat.unpair (Nat.unpair w).1).1
        + (Nat.unpair w).2 % 2 * (Nat.unpair (Nat.unpair w).1).2) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp (Primrec.const 1)
          (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 2)))
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.nat_mul.comp
        (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 2))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))))).choose_spec O) w

/-- The right-projection code: with oracle `toPFun (join W X)`, computes
`toPFun X` (odd bits). -/
private noncomputable def cRight : OracleCode := .comp .oracle cOdd

private theorem cRight_spec (W X : ℕ → Bool) :
    eval (toPFun (join W X)) cRight = toPFun X := by
  funext k
  rw [cRight, eval_comp, cOdd_spec, eval_oracle,
    show (Part.some (2 * k + 1) >>= toPFun (join W X))
      = toPFun (join W X) (2 * k + 1) from Part.bind_some _ _]
  have : join W X (2 * k + 1) = X k := by
    rw [join, if_neg (by omega)]
    congr 1
    omega
  simp [toPFun, this]

/-- The join-reduction code built from an index `j` (computing `X` from
`X'`): with oracle `toPFun (join W X')`, computes `toPFun (join W X)`. -/
private noncomputable def cJoinRed (j : ℕ) : OracleCode :=
  .comp cMix (.pair (.pair .oracle (.comp (trOracle cRight (ofNatCode j)) cHalf)) idCode)

private theorem cJoinRed_spec (W X X' : ℕ → Bool) (j : ℕ)
    (hj : eval (toPFun X') (ofNatCode j) = toPFun X) :
    eval (toPFun (join W X')) (cJoinRed j) = toPFun (join W X) := by
  have hspliced : eval (toPFun (join W X')) (trOracle cRight (ofNatCode j))
      = toPFun X := by
    rw [eval_trOracle (cRight_spec W X'), hj]
  funext n
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain ⟨w, hw, hyMix⟩ := mem_eval_comp.mp hy
    obtain ⟨p, hp, m, hm, rfl⟩ := mem_eval_pair.mp hw
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := mem_eval_pair.mp hp
    -- values of the components
    rw [eval_idCode, Part.mem_some_iff] at hm
    rw [hm] at hyMix
    rw [show eval (toPFun (join W X')) OracleCode.oracle n
        = toPFun (join W X') n from rfl, toPFun, Part.mem_some_iff] at hv₁
    subst hv₁
    obtain ⟨h, hh, hv₂'⟩ := mem_eval_comp.mp hv₂
    rw [cHalf_spec, Part.mem_some_iff] at hh
    subst hh
    rw [hspliced, toPFun, Part.mem_some_iff] at hv₂'
    subst hv₂'
    rw [cMix_spec, Part.mem_some_iff] at hyMix
    subst hyMix
    simp only [Nat.unpair_pair]
    rw [toPFun, Part.mem_some_iff]
    have hjE : ∀ (Y : ℕ → Bool), n % 2 = 0 → join W Y n = W (n / 2) :=
      fun Y h => by rw [join, if_pos h]
    have hjO : ∀ (Y : ℕ → Bool), n % 2 = 1 → join W Y n = Y (n / 2) :=
      fun Y h => by rw [join, if_neg (by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [hjE X hn, hjE X' hn, hn]
      cases W (n / 2) <;> simp
    · rw [hjO X hn, hn]
      cases X (n / 2) <;> simp
  · intro hy
    rw [toPFun, Part.mem_some_iff] at hy
    subst hy
    refine mem_eval_comp.mpr ⟨Nat.pair
      (Nat.pair (cond (join W X' n) 1 0) (cond (X (n / 2)) 1 0)) n, ?_, ?_⟩
    · refine mem_eval_pair.mpr ⟨_, ?_, n, ?_, rfl⟩
      · refine mem_eval_pair.mpr ⟨_, ?_, _, ?_, rfl⟩
        · exact Part.mem_some_iff.mpr rfl
        · refine mem_eval_comp.mpr ⟨n / 2, ?_, ?_⟩
          · rw [cHalf_spec]
            exact Part.mem_some_iff.mpr rfl
          · rw [hspliced]
            exact Part.mem_some_iff.mpr rfl
      · rw [eval_idCode]
        exact Part.mem_some_iff.mpr rfl
    · rw [cMix_spec, Part.mem_some_iff]
      simp only [Nat.unpair_pair]
      have hjE : ∀ (Y : ℕ → Bool), n % 2 = 0 → join W Y n = W (n / 2) :=
        fun Y h => by rw [join, if_pos h]
      have hjO : ∀ (Y : ℕ → Bool), n % 2 = 1 → join W Y n = Y (n / 2) :=
        fun Y h => by rw [join, if_neg (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · rw [hjE X hn, hjE X' hn, hn]
        cases W (n / 2) <;> simp
      · rw [hjO X hn, hn]
        cases X (n / 2) <;> simp

/-! ### Controlled congruence -/

/-- **Uniformly pointed join-cones**: a computable transformation of index
witnesses, independent of `W`, `X`, `X'`, turning witnesses for `X ≡ₜ X'`
into witnesses for `join W X ≡ₜ join W X'`. -/
theorem equivVia_join_uniform :
    ∃ t : ℕ × ℕ → ℕ × ℕ, Computable t ∧
      ∀ (W X X' : ℕ → Bool) (i j : ℕ), EquivVia X X' i j →
        EquivVia (join W X) (join W X') (t (i, j)).1 (t (i, j)).2 := by
  refine ⟨fun p => (encodeCode (cJoinRed p.1), encodeCode (cJoinRed p.2)), ?_, ?_⟩
  · -- computability of the index transformation
    have henc : Primrec fun j : ℕ => encodeCode (cJoinRed j) := by
      have hval : ∀ j, encodeCode (cJoinRed j)
          = compEnc (encodeCode cMix)
              (pairEnc
                (pairEnc 4 (compEnc (trE cRight j) (encodeCode cHalf)))
                (encodeCode idCode)) := fun j => rfl
      exact ((compEnc_prim.comp (Primrec.const (encodeCode cMix))
        (pairEnc_prim.comp
          (pairEnc_prim.comp (Primrec.const 4)
            (compEnc_prim.comp (trE_primrec cRight) (Primrec.const (encodeCode cHalf))))
          (Primrec.const (encodeCode idCode)))).of_eq fun j => (hval j).symm)
    exact Primrec.to_comp (Primrec.pair (henc.comp Primrec.fst) (henc.comp Primrec.snd))
  · rintro W X X' i j ⟨hi, hj⟩
    constructor
    · -- witness for `join W X'` from `join W X`
      rw [ofNatCode_encodeCode]
      exact cJoinRed_spec W X' X i hi
    · rw [ofNatCode_encodeCode]
      exact cJoinRed_spec W X X' j hj

/-- Consequence for uniformly invariant functions: on canonical
representatives `join W ·`, the induced function is again **uniformly**
invariant, with a uniformity function computed from the original one. -/
theorem uniformlyTuringInvariant_comp_join {F : (ℕ → Bool) → ℕ → Bool}
    (hF : UniformlyTuringInvariant F) (W : ℕ → Bool) :
    UniformlyTuringInvariant fun X => F (join W X) := by
  obtain ⟨u, hu⟩ := hF
  obtain ⟨t, -, ht⟩ := equivVia_join_uniform
  exact ⟨fun p => u (t p), fun X Y i j h => hu _ _ _ _ (ht W X Y i j h)⟩

/-- Realization: above the base, canonical representatives realize every
degree.  Together with `equivVia_join_uniform` this says the family
`X ↦ join W X` is a *uniformly pointed* copy of Cantor space inside
`cone W`. -/
theorem join_realizes {W X : ℕ → Bool} (h : W ≤ₜ X) : join W X ≡ₜ X :=
  ⟨join_le h (le.refl X), right_le_join W X⟩

#print axioms equivVia_join_uniform
#print axioms uniformlyTuringInvariant_comp_join
#print axioms join_realizes

end Martin
