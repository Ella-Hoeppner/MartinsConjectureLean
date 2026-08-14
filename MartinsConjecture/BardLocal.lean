/-
**Bard's local theorem** (Vittorio Bard, "Uniform Martin's conjecture, locally",
arXiv:1907.10766) and, from it, **Part I of Martin's conjecture for
computably-uniformly-invariant functions** (Slaman–Steel 1988, effective form).

Bard's insight: Part I is a *local* phenomenon.  His Theorem 2.2 says a
uniformly-invariant `f` restricted to a single degree `[x]` is either constant
there or satisfies `f(x) ≥ᵀ x`.  Globalizing with Martin's cone theorem gives
Part I.

This file formalizes that argument for the **computable-uniformity** hypothesis
(`ComputablyUniformlyTuringInvariant`):

* `joinFam_le_computable` — Bard's Fact 3.1 with a *computable* index family
  (the uniformity transformer `u` is computable, not primitive recursive);
* `const_on_degrees_constOnCone` — Bard's Fact 2.3: if `f` is literally constant
  on each degree in a cone, it is constant on a cone (per-digit cone dichotomy +
  `onCone_forall`);
* `bard_local` — Bard's Theorem 2.2 (effective form): a computably-uniform `f`
  that is not constant on `[x]` satisfies `x ≤ᵀ f(x)` — via the selector family
  `y_n = x` or `z` (by the `n`-th bit of `x`), whose `f`-images join above `x`
  yet stay below `f(x)` by uniformity + Fact 3.1;
* `steel_kernel_computable` — globalization: a non-constant computably-uniform
  function is above the identity on a cone.  This *proves* `SteelUniformKernel`
  for the computable-uniformity class, discharging both Part I open cores there.
-/
import MartinsConjecture.UniformCores
import MartinsConjecture.UniformFunctionals
import MartinsConjecture.RegularChain

open scoped Computability
open OracleCode Cantor

namespace Martin

attribute [local instance] Classical.propDecidable

/-- **Bard's Fact 3.1, computable form.**  If a family `R n` is uniformly
computable from `A` via a *computable* index map `t` (`Φ_{t n}^A = R n`), the join
`⨁ₙ R n` is Turing-below `A`.  (The uniformity transformer produced by Bard's
Lemma 3.4 is computable, not primitive recursive, so we need this strengthening
of `joinFam_le`.) -/
theorem joinFam_le_computable {A : ℕ → Bool} {t : ℕ → ℕ} (ht : Computable t)
    {R : ℕ → ℕ → Bool}
    (hR : ∀ n, eval (toPFun A) (ofNatCode (t n)) = toPFun (R n)) :
    joinFam R ≤ₜ A := by
  rw [le_iff_bitg]
  have hbuilder : Computable (fun m : ℕ => Nat.pair (t (Nat.unpair m).1) (Nat.unpair m).2) :=
    Primrec₂.natPair.to_comp.comp (ht.comp (Primrec.fst.comp Primrec.unpair).to_comp)
      (Primrec.snd.comp Primrec.unpair).to_comp
  refine (Nat.RecursiveIn.comp (eval_universal A)
    (Partrec.nat_iff.mp hbuilder.partrec).recursiveIn).of_eq fun m => ?_
  show (Part.some (Nat.pair (t (Nat.unpair m).1) (Nat.unpair m).2)).bind
      (fun p => eval (toPFun A) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2)
      = Part.some (bitg (joinFam R) m)
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  rw [hR (Nat.unpair m).1]
  rfl

/-- **Bard's Fact 2.3.**  If `F` is literally constant on every degree in a cone
(base `w`: for `X ≥ᵀ w`, `Y ≡ᵀ X ⟹ F Y = F X`), then `F` is constant on a cone.
Proof: each digit `i` of `F X` is Turing-invariant on the cone, so the cone
theorem fixes it on a sub-cone; `onCone_forall` intersects the (countably many)
digit-cones. -/
theorem const_on_degrees_constOnCone (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} {w : ℕ → Bool}
    (h : ∀ X, w ≤ₜ X → ∀ Y, Y ≡ₜ X → F Y = F X) :
    ConstantOnCone F := by
  -- for each digit `i`, `F X i` is constant on a cone
  have hpd : ∀ i : ℕ, ∃ b : Bool, OnCone (fun X => F X i = b) := by
    intro i
    have hAinv : TuringInvariantSet {X | w ≤ₜ X → F X i = true} := by
      intro X Y hXY
      have hwiff : w ≤ₜ X ↔ w ≤ₜ Y := ⟨fun hw => hw.trans hXY.1, fun hw => hw.trans hXY.2⟩
      constructor
      · intro hX hwY
        have hwX : w ≤ₜ X := hwiff.mpr hwY
        have := h X hwX Y hXY.symm
        rw [this]; exact hX hwX
      · intro hY hwX
        have hwY : w ≤ₜ Y := hwiff.mp hwX
        have := h Y hwY X hXY
        rw [this]; exact hY hwY
    rcases cone_theorem_onCone {X | w ≤ₜ X → F X i = true} hAinv (hTD _ trivial hAinv)
      with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨true, Cantor.join c w, fun X hX => ?_⟩
      have hwX : w ≤ₜ X := (Cantor.right_le_join c w).trans hX
      exact hc X ((Cantor.left_le_join c w).trans hX) hwX
    · refine ⟨false, Cantor.join c w, fun X hX => ?_⟩
      have hwX : w ≤ₜ X := (Cantor.right_le_join c w).trans hX
      have hmem : ¬ (w ≤ₜ X → F X i = true) := hc X ((Cantor.left_le_join c w).trans hX)
      cases hFX : F X i with
      | false => exact hFX
      | true => exact absurd (fun _ => hFX) hmem
  choose b hb using hpd
  obtain ⟨W, hW⟩ := onCone_forall hb
  refine ⟨b, W, fun X hX => ?_⟩
  have hFXb : F X = b := funext (fun i => hW X hX i)
  show F X ≡ₜ b
  rw [hFXb]
  exact Cantor.equiv.refl b

/-! ### The selector witness family (Bard's Theorem 2.2, code construction)

The `n`-th selector real is `y n = x` if `x n = true`, else `z`.  We need, uniformly
in `n`, an equivalence witness `x ≡ᵀ y n` with a computable forward index and a *fixed*
backward index.

* forward `iₙ`: on oracle `x`, output `x` or `z` by the `n`-th bit of `x` — an
  `x`-recursive functional, coded once and specialized in `n` by s-m-n (`curry`);
* backward `j` (fixed): on oracle `w ∈ {x, z}`, recover `x` by branching on the
  distinguishing bit `p` (`x p ≠ z p`).  A `prec` gives the branch *and*
  short-circuits: the base (an oracle query, always halts) runs always, the
  `z → x` reduction runs only on the `z` side, so `j` converges on both oracles. -/

/-- The distinguishing-bit indicator `[v ≠ bp]` for `v, bp ∈ {0,1}`, as an
oracle-free code — arithmetic (truncated subtraction) to avoid `Decidable`
instance friction: `0` iff `v = bp`, `1` iff they differ. -/
private def cmpFn (bp : ℕ) (v : ℕ) : ℕ := (v - bp) + (bp - v)

private theorem cmpFn_prim (bp : ℕ) : Nat.Primrec (cmpFn bp) :=
  Primrec.nat_iff.mp (Primrec.nat_add.comp
    (Primrec.nat_sub.comp Primrec.id (Primrec.const bp))
    (Primrec.nat_sub.comp (Primrec.const bp) Primrec.id))

/-- `prec` evaluation, unfolded on a paired input (local copy). -/
private theorem eval_prec_pair (O : ℕ →. ℕ) (cf cg : OracleCode) (a n : ℕ) :
    eval O (.prec cf cg) (Nat.pair a n)
      = Nat.rec (motive := fun _ => Part ℕ) (eval O cf a)
          (fun y IH => IH >>= fun i => eval O cg (Nat.pair a (Nat.pair y i))) n := by
  show Nat.rec (motive := fun _ => Part ℕ) (eval O cf (Nat.unpair (Nat.pair a n)).1)
      (fun y IH => IH >>= fun i =>
        eval O cg (Nat.pair (Nat.unpair (Nat.pair a n)).1 (Nat.pair y i)))
      (Nat.unpair (Nat.pair a n)).2 = _
  rw [Nat.unpair_pair]

private theorem eval_left_val (O : ℕ →. ℕ) (a : ℕ) :
    eval O OracleCode.left a = Part.some (Nat.unpair a).1 := rfl

/-- **Bard's selector witness family** (Theorem 2.2, code half).  For `z ≡ᵀ x`
differing at bit `p`, there is a computable forward index map `idx` and a fixed
backward index `jb` witnessing `x ≡ᵀ (x or z by the n-th bit of x)` for every `n`. -/
theorem bard_witness_family {x z : ℕ → Bool} (hzx : z ≡ₜ x) {p : ℕ} (hp : x p ≠ z p) :
    ∃ (idx : ℕ → ℕ) (jb : ℕ), Computable idx ∧
      ∀ n, EquivVia x (fun m => if x n = true then x m else z m) (idx n) jb := by
  classical
  -- forward functional: `selFn ⟨n,m⟩ = bitg (y n) m`, recursive in `x`
  set selFn : ℕ → ℕ := fun q =>
    bitg x (Nat.unpair q).1 * bitg x (Nat.unpair q).2
      + (1 - bitg x (Nat.unpair q).1) * bitg z (Nat.unpair q).2 with hselFn
  have hqx : Nat.RecursiveIn {toPFun x} (fun q => (bitg x q : Part ℕ)) :=
    le_iff_bitg.mp (Cantor.le.refl x)
  have hqz : Nat.RecursiveIn {toPFun x} (fun q => (bitg z q : Part ℕ)) :=
    le_iff_bitg.mp hzx.1
  have hA : Nat.RecursiveIn {toPFun x} (fun q => (bitg x (Nat.unpair q).1 : Part ℕ)) :=
    (Nat.RecursiveIn.comp hqx
      ((Primrec.nat_iff.mp (Primrec.fst.comp Primrec.unpair)).recursiveIn)).of_eq fun q => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hB : Nat.RecursiveIn {toPFun x} (fun q => (bitg x (Nat.unpair q).2 : Part ℕ)) :=
    (Nat.RecursiveIn.comp hqx
      ((Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)).recursiveIn)).of_eq fun q => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hC : Nat.RecursiveIn {toPFun x} (fun q => (bitg z (Nat.unpair q).2 : Part ℕ)) :=
    (Nat.RecursiveIn.comp hqz
      ((Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)).recursiveIn)).of_eq fun q => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hsel : Nat.RecursiveIn {toPFun x} (fun q => (selFn q : Part ℕ)) := by
    have harith := (Primrec.nat_iff.mp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
        (Primrec.nat_mul.comp
          (Primrec.nat_sub.comp (Primrec.const 1) (Primrec.fst.comp Primrec.unpair))
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))).recursiveIn
      (O := {toPFun x})
    exact (Nat.RecursiveIn.comp harith
      (Nat.RecursiveIn.pair hA (Nat.RecursiveIn.pair hB hC))).of_eq fun q => by
      simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
        Nat.unpair_pair, Part.coe_some, hselFn]
  obtain ⟨selC, hselC⟩ := exists_code_of_recursiveIn hsel
  -- backward: reduction `dC : z → x`, and the branch code
  obtain ⟨dC, hdC⟩ := exists_code_of_recursiveIn (le_iff_bitg.mp hzx.2)
  set bp : ℕ := bitg x p with hbp
  set cmpC : OracleCode := (exists_code_of_partrec
    (Nat.Partrec.of_primrec (cmpFn_prim bp))).choose with hcmpC
  have hcmpC_spec : ∀ (O : ℕ →. ℕ) (v : ℕ), eval O cmpC v = Part.some (cmpFn bp v) := fun O v =>
    congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec (cmpFn_prim bp))).choose_spec O) v
  set jC : OracleCode :=
    .comp (.prec .oracle (.comp dC .left))
      (.pair idCode (.comp cmpC (.comp .oracle (const p)))) with hjC
  -- forward correctness: `Φ_{iₙ}^x = y n`
  have hy_fwd : ∀ n, eval (toPFun x) (curry selC n) = toPFun (fun m => if x n = true then x m else z m) := by
    intro n
    funext m
    rw [eval_curry, hselC]
    show Part.some (selFn (Nat.pair n m)) = _
    rw [toPFun_eq_bitg]
    congr 1
    rcases Bool.eq_false_or_eq_true (x n) with h | h <;>
      simp [hselFn, bitg, h, Nat.unpair_pair]
  -- backward correctness: `Φ_j^w = x` for oracle `w ∈ {x, z}` (branch on `w p`)
  have hjC_eval : ∀ (w : ℕ → Bool) (m : ℕ), eval (toPFun w) jC m
      = Nat.rec (motive := fun _ => Part ℕ) (Part.some (bitg w m))
          (fun _ IH => IH >>= fun _ => eval (toPFun w) dC m) (cmpFn bp (bitg w p)) := by
    intro w m
    have htest : eval (toPFun w) (.comp cmpC (.comp .oracle (const p))) m
        = Part.some (cmpFn bp (bitg w p)) := by
      rw [eval_comp, eval_comp,
        show eval (toPFun w) (const p) m = Part.some p from eval_const _ _ _,
        show (Part.some p >>= eval (toPFun w) OracleCode.oracle)
          = eval (toPFun w) OracleCode.oracle p from Part.bind_some _ _, eval_oracle,
        toPFun_eq_bitg,
        show (Part.some (bitg w p) >>= eval (toPFun w) cmpC)
          = eval (toPFun w) cmpC (bitg w p) from Part.bind_some _ _, hcmpC_spec]
    rw [hjC, eval_comp]
    rw [show eval (toPFun w) (.pair idCode (.comp cmpC (.comp .oracle (const p)))) m
        = Part.some (Nat.pair m (cmpFn bp (bitg w p))) from by
      rw [eval_pair_eq, eval_idCode, htest]
      simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_some]]
    rw [show (Part.some (Nat.pair m (cmpFn bp (bitg w p)))
          >>= eval (toPFun w) (.prec .oracle (.comp dC .left)))
        = eval (toPFun w) (.prec .oracle (.comp dC .left)) (Nat.pair m (cmpFn bp (bitg w p)))
        from Part.bind_some _ _, eval_prec_pair]
    have hbase : eval (toPFun w) OracleCode.oracle m = Part.some (bitg w m) := by
      rw [eval_oracle, toPFun_eq_bitg]
    have hstep : (fun (y : ℕ) (IH : Part ℕ) =>
          IH >>= fun i => eval (toPFun w) (.comp dC .left) (Nat.pair m (Nat.pair y i)))
        = (fun (_ : ℕ) (IH : Part ℕ) => IH >>= fun _ => eval (toPFun w) dC m) := by
      funext y IH
      congr 1
      funext i
      rw [eval_comp, eval_left_val,
        show (Part.some (Nat.unpair (Nat.pair m (Nat.pair y i))).1 >>= eval (toPFun w) dC)
          = eval (toPFun w) dC (Nat.unpair (Nat.pair m (Nat.pair y i))).1 from Part.bind_some _ _,
        Nat.unpair_pair]
    rw [hbase, hstep]
  have hbne : bitg z p ≠ bitg x p := by
    cases hx : x p <;> cases hz : z p <;> simp_all [bitg]
  have hxle : bitg x p ≤ 1 := by
    rcases Bool.eq_false_or_eq_true (x p) with h | h <;> simp [bitg, h]
  have hzle : bitg z p ≤ 1 := by
    rcases Bool.eq_false_or_eq_true (z p) with h | h <;> simp [bitg, h]
  have hbp_ne : cmpFn bp (bitg z p) = 1 := by
    show (bitg z p - bp) + (bp - bitg z p) = 1
    rw [hbp]; omega
  have hbp_x : cmpFn bp (bitg x p) = 0 := by
    show (bitg x p - bp) + (bp - bitg x p) = 0
    rw [hbp]; omega
  have hjx : eval (toPFun x) jC = toPFun x := by
    funext m; rw [hjC_eval x m, hbp_x]
    show Part.some (bitg x m) = toPFun x m
    exact (toPFun_eq_bitg x m).symm
  have hjz : eval (toPFun z) jC = toPFun x := by
    funext m
    rw [hjC_eval z m, hbp_ne]
    show (Part.some (bitg z m) >>= fun _ => eval (toPFun z) dC m) = toPFun x m
    rw [show (Part.some (bitg z m) >>= fun _ => eval (toPFun z) dC m)
        = eval (toPFun z) dC m from Part.bind_some _ _, congrFun hdC m]
    exact (toPFun_eq_bitg x m).symm
  refine ⟨fun n => encodeCode (curry selC n), encodeCode jC, ?_, ?_⟩
  · have heq : (fun n => encodeCode (curry selC n)) = fun n => curryEnc (encodeCode selC) n :=
      funext (fun n => encodeCode_curry selC n)
    rw [heq]
    exact Primrec.to_comp (curryEnc_prim.comp (Primrec.const (encodeCode selC)) Primrec.id)
  · intro n
    refine ⟨?_, ?_⟩
    · rw [ofNatCode_encodeCode]; exact hy_fwd n
    · rw [ofNatCode_encodeCode]
      rcases Bool.eq_false_or_eq_true (x n) with h | h
      · have hyx : (fun m => if x n = true then x m else z m) = x := by
          funext m; rw [h]; exact if_pos rfl
        rw [hyx]; exact hjx
      · have hyz : (fun m => if x n = true then x m else z m) = z := by
          funext m; rw [h]; exact if_neg (by decide)
        rw [hyz]; exact hjz

/-- **Bard's Theorem 2.2** (effective form).  A computably-uniformly-invariant
`F` that is *not constant* on the degree of `x` (some `z ≡ᵀ x` with `F z ≠ F x`)
satisfies `x ≤ᵀ F x`.

The `n`-th selector real `y n` is `x` or `z` by the `n`-th bit of `x`.  Reading
the *fixed* distinguishing bit `k` of `F x, F z` off `⨁ₙ F(y n)` recovers `x`, so
`x ≤ᵀ ⨁ₙ F(y n)`; and by computable uniformity each `F(y n) = Φ_{u(iₙ,j).1}^{F x}`,
so Bard's Fact 3.1 gives `⨁ₙ F(y n) ≤ᵀ F x`.  Chaining: `x ≤ᵀ F x`. -/
theorem bard_local (F : (ℕ → Bool) → ℕ → Bool)
    (hu : ComputablyUniformlyTuringInvariant F)
    {x : ℕ → Bool} (hnc : ∃ z, z ≡ₜ x ∧ F z ≠ F x) :
    x ≤ₜ F x := by
  classical
  obtain ⟨u, hu_comp, hu_spec⟩ := hu
  obtain ⟨z, hzx, hFne⟩ := hnc
  have hxz : x ≠ z := fun h => hFne (by rw [h])
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hxz
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hFne
  obtain ⟨idx, jb, hidx_comp, hEV⟩ := bard_witness_family hzx hp
  set y : ℕ → (ℕ → Bool) := fun n m => if x n = true then x m else z m with hy
  set R : ℕ → (ℕ → Bool) := fun n => F (y n) with hR
  have ha_comp : Computable (fun n => (u (idx n, jb)).1) :=
    Computable.fst.comp (hu_comp.comp (Computable.pair hidx_comp (Computable.const jb)))
  have hFy : ∀ n, eval (toPFun (F x)) (ofNatCode ((u (idx n, jb)).1)) = toPFun (R n) :=
    fun n => (hu_spec x (y n) (idx n) jb (hEV n)).1
  have hjoin_le : joinFam R ≤ₜ F x := joinFam_le_computable ha_comp hFy
  have hjoinval : ∀ n, joinFam R (Nat.pair n k) = R n k := fun n => by
    simp [joinFam, Nat.unpair_pair]
  have hcbit : ∀ (Y : ℕ → Bool) (i : ℕ), bitg Y i ≤ 1 := fun Y i => by
    rcases Bool.eq_false_or_eq_true (Y i) with h | h <;> simp [bitg, h]
  -- the pure-ℕ decode: reading the fixed bit `k` recovers `x n`
  have hdec : ∀ n, 1 - ((bitg (joinFam R) (Nat.pair n k) - bitg (F x) k)
        + (bitg (F x) k - bitg (joinFam R) (Nat.pair n k))) = bitg x n := by
    intro n
    have hqn : bitg (joinFam R) (Nat.pair n k) = bitg (F (y n)) k := by
      simp only [bitg, joinFam, Nat.unpair_pair, hR]
    rw [hqn]
    rcases Bool.eq_false_or_eq_true (x n) with h | h
    · have hyx : y n = x := funext (fun m => by simp [hy, h])
      have hbxn : bitg x n = 1 := by simp [bitg, h]
      rw [hyx, hbxn]
      omega
    · have hyz : y n = z := funext (fun m => by simp [hy, h])
      have hbxn : bitg x n = 0 := by simp [bitg, h]
      have hne : bitg (F z) k ≠ bitg (F x) k := by
        intro hc; apply hk
        cases hfz : F z k <;> cases hfx : F x k <;> simp_all [bitg]
      rw [hyz, hbxn]
      have h1 := hcbit (F z) k
      have h2 := hcbit (F x) k
      omega
  have hx_le : x ≤ₜ joinFam R := by
    rw [le_iff_bitg]
    have hq : Nat.RecursiveIn {toPFun (joinFam R)}
        (fun n => (bitg (joinFam R) (Nat.pair n k) : Part ℕ)) :=
      (Nat.RecursiveIn.comp (le_iff_bitg.mp (Cantor.le.refl (joinFam R)))
        ((Primrec.nat_iff.mp (Primrec₂.natPair.comp Primrec.id
          (Primrec.const k))).recursiveIn)).of_eq fun n => by
        simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, id_eq]
    refine (Nat.RecursiveIn.comp
      ((Primrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1)
        (Primrec.nat_add.comp
          (Primrec.nat_sub.comp Primrec.id (Primrec.const (bitg (F x) k)))
          (Primrec.nat_sub.comp (Primrec.const (bitg (F x) k)) Primrec.id)))).recursiveIn)
        hq).of_eq fun n => by
      simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, id_eq, hdec n]
  exact hx_le.trans hjoin_le

/-! ### Part I of Martin's conjecture for computably-uniformly-invariant functions

Globalizing Bard's local theorem with the cone theorem (on the pivot set
`{X | X ≤ᵀ F X}`) gives Part I for the computable-uniformity class — the effective
form of Slaman–Steel 1988. -/

/-- **The Steel kernel holds for computably-uniform functions**: a non-constant
computably-uniformly-invariant `F` is above the identity on a cone.  Discharges
the hypothesis `SteelUniformKernel` for the computable-uniformity class. -/
theorem steel_kernel_computable (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hu : ComputablyUniformlyTuringInvariant F)
    (hnc : ¬ ConstantOnCone F) : AboveIdOnCone F := by
  have hinv : TuringInvariant F := hu.toUniformly.turingInvariant
  have hBinv : TuringInvariantSet {X | X ≤ₜ F X} := by
    intro X Y hXY
    have hF := hinv X Y hXY
    exact ⟨fun h => hXY.2.trans (h.trans hF.1), fun h => hXY.1.trans (h.trans hF.2)⟩
  rcases cone_theorem_onCone {X | X ≤ₜ F X} hBinv (hTD _ trivial hBinv) with hB | hBc
  · exact hB
  · exfalso
    obtain ⟨w, hw⟩ := hBc
    apply hnc
    apply const_on_degrees_constOnCone hTD (w := w)
    intro X hX Y hYX
    by_contra hne
    exact hw X hX (bard_local F hu ⟨Y, hYX, hne⟩)

/-- **Part I of Martin's conjecture for computably-uniformly-invariant functions**
(Slaman–Steel 1988, effective form): every such `F` is constant on a cone or above
the identity on a cone. -/
theorem partI_computablyUniform (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hu : ComputablyUniformlyTuringInvariant F) :
    ConstantOnCone F ∨ AboveIdOnCone F := by
  by_cases hc : ConstantOnCone F
  · exact Or.inl hc
  · exact Or.inr (steel_kernel_computable hTD hu hc)

/-- **The regressive core, for computably-uniform functions.** -/
theorem regressive_computablyUniform (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hu : ComputablyUniformlyTuringInvariant F)
    (hreg : OnCone (fun X => F X <ₜ X)) : ConstantOnCone F := by
  by_contra hnc
  obtain ⟨B1, hB1⟩ := hreg
  obtain ⟨B2, hB2⟩ := steel_kernel_computable hTD hu hnc
  exact (hB1 _ (Cantor.left_le_join B1 B2)).2 (hB2 _ (Cantor.right_le_join B1 B2))

/-- **The incomparable core, for computably-uniform functions.** -/
theorem incomparable_computablyUniform (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hu : ComputablyUniformlyTuringInvariant F)
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ConstantOnCone F := by
  by_contra hnc
  obtain ⟨B1, hB1⟩ := hinc
  obtain ⟨B2, hB2⟩ := steel_kernel_computable hTD hu hnc
  exact (hB1 _ (Cantor.left_le_join B1 B2)).2 (hB2 _ (Cantor.right_le_join B1 B2))

#print axioms bard_local
#print axioms steel_kernel_computable
#print axioms partI_computablyUniform

end Martin
