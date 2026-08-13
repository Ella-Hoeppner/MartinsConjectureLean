/-
Σ₁-completeness of the jump, and the Shoenfield limit lemma.

* `ofNatCode_compEnc` — decoding a `compEnc`-number yields a composition
  (needed to turn halting questions into diagonal jump questions).
* **`dom_iff_jumpP`** — Σ₁-completeness: the halting problem for machine `e`
  on input `n`, relative to any oracle, is (uniformly primitively) reducible
  to the diagonal jump of that oracle.
* **`recursiveIn_jump_of_limit`** — the substantive direction of the
  Shoenfield limit lemma, relativized: a function with an `X`-computable
  approximation converging pointwise is computable from `X′`.
-/
import MartinsConjecture.Universal

open scoped Computability
open OracleCode Cantor

namespace OracleCode

/-- Decoding a `compEnc` number yields the composition of the decodings. -/
theorem ofNatCode_compEnc (a b : ℕ) :
    ofNatCode (compEnc a b) = .comp (ofNatCode a) (ofNatCode b) := by
  have hd : compEnc a b = (4 * Nat.pair a b + 2) + 5 := by
    rw [compEnc]
    omega
  rw [hd, ofNatCode.eq_6]
  have hb1 : (4 * Nat.pair a b + 2).bodd = false := by
    have := Nat.mod_two_of_bodd (4 * Nat.pair a b + 2)
    rcases hbb : (4 * Nat.pair a b + 2).bodd with _ | _
    · rfl
    · rw [hbb] at this
      simp only [Bool.toNat_true] at this
      omega
  have hb2 : (4 * Nat.pair a b + 2).div2.bodd = true := by
    have h2 := Nat.mod_two_of_bodd (4 * Nat.pair a b + 2).div2
    rw [Nat.div2_val] at h2
    rcases hbb : (4 * Nat.pair a b + 2).div2.bodd with _ | _
    · rw [Nat.div2_val] at hbb
      rw [hbb] at h2
      simp only [Bool.toNat_false] at h2
      omega
    · rfl
  have hdd : (4 * Nat.pair a b + 2).div2.div2 = Nat.pair a b := by
    simp only [Nat.div2_val, Nat.div_div_eq_div_mul]
    omega
  simp only [hb1, hb2, hdd, Nat.unpair_pair]

/-- The composition-with-constant code evaluates as expected. -/
theorem eval_compEnc_constEnc (O : ℕ →. ℕ) (e n x : ℕ) :
    eval O (ofNatCode (compEnc e (constEnc n))) x
      = eval O (ofNatCode e) n := by
  rw [ofNatCode_compEnc, show ofNatCode (constEnc n) = const n from by
    rw [constEnc, ofNatCode_encodeCode]]
  rw [eval_comp, eval_const]
  exact Part.bind_some _ _

/-- **Σ₁-completeness of the jump**: halting of machine `e` on input `n`
relative to `O` is a diagonal jump question at a code computed primitively
from `(e, n)`. -/
theorem dom_iff_jumpP (O : ℕ →. ℕ) (e n : ℕ) :
    (eval O (ofNatCode e) n).Dom ↔ jumpP O (compEnc e (constEnc n)) := by
  rw [jumpP, eval_compEnc_constEnc]

end OracleCode

namespace OracleCode

variable {X : ℕ → Bool} {g : ℕ → ℕ → ℕ} {f : ℕ → ℕ}

/-- Stability of the approximation `g` at `(n, s)`. -/
def Stable (g : ℕ → ℕ → ℕ) (n s : ℕ) : Prop :=
  ∀ t, g n (s + t + 1) = g n s

/-- **The Shoenfield limit lemma** (substantive direction, relativized):
a pointwise convergent `X`-computable approximation has `X′`-computable
limit. -/
theorem recursiveIn_jump_of_limit
    (hg : Nat.RecursiveIn {toPFun X}
      (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)))
    (hlim : ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = f n) :
    Nat.RecursiveIn {toPFun (Cantor.jump X)}
      (fun n : ℕ => ((f n : ℕ) : Part ℕ)) := by
  -- The change-detector, recursive in `X`:
  -- on `v = pair w t` with `w = pair n s`, output `0` iff
  -- `g n (s + t + 1) ≠ g n s`.
  have hq1 : Nat.RecursiveIn {toPFun X} (fun v : ℕ =>
      ((g (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2 : ℕ)
        : Part ℕ)) :=
    Nat.RecursiveIn.comp hg (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.fst.comp Primrec.unpair)))))) |>.of_eq fun v => by
      simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hq2 : Nat.RecursiveIn {toPFun X} (fun v : ℕ =>
      ((g (Nat.unpair (Nat.unpair v).1).1
        ((Nat.unpair (Nat.unpair v).1).2 + (Nat.unpair v).2 + 1) : ℕ)
        : Part ℕ)) :=
    Nat.RecursiveIn.comp hg (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.snd.comp (Primrec.unpair.comp
              (Primrec.fst.comp Primrec.unpair)))
            (Primrec.snd.comp Primrec.unpair))
          (Primrec.const 1))))) |>.of_eq fun v => by
      simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  -- pair the two values and post-process:
  -- output `1 - min 1 (dist)`: `0` iff the two values differ.
  have hpairq : Nat.RecursiveIn {toPFun X} (fun v : ℕ =>
      Nat.pair <$>
        ((g (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2 : ℕ)
          : Part ℕ) <*>
        ((g (Nat.unpair (Nat.unpair v).1).1
          ((Nat.unpair (Nat.unpair v).1).2 + (Nat.unpair v).2 + 1) : ℕ)
          : Part ℕ)) :=
    Nat.RecursiveIn.pair hq1 hq2
  have hmixP : Nat.Primrec fun z : ℕ =>
      1 - min 1 (((Nat.unpair z).1 - (Nat.unpair z).2)
        + ((Nat.unpair z).2 - (Nat.unpair z).1)) := by
    refine Primrec.nat_iff.mp ?_
    have hd : Primrec fun z : ℕ => ((Nat.unpair z).1 - (Nat.unpair z).2)
        + ((Nat.unpair z).2 - (Nat.unpair z).1) :=
      Primrec.nat_add.comp
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec.snd.comp Primrec.unpair))
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair)
          (Primrec.fst.comp Primrec.unpair))
    exact Primrec.nat_sub.comp (Primrec.const 1)
      (Primrec.nat_min.comp (Primrec.const 1) hd)
  have hdelta : Nat.RecursiveIn {toPFun X} (fun v : ℕ =>
      (Nat.pair <$>
        ((g (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2 : ℕ)
          : Part ℕ) <*>
        ((g (Nat.unpair (Nat.unpair v).1).1
          ((Nat.unpair (Nat.unpair v).1).2 + (Nat.unpair v).2 + 1) : ℕ)
          : Part ℕ))
      >>= fun z : ℕ =>
        ((1 - min 1 (((Nat.unpair z).1 - (Nat.unpair z).2)
          + ((Nat.unpair z).2 - (Nat.unpair z).1)) : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hmixP.recursiveIn hpairq
  have hDelta := Nat.RecursiveIn.rfind hdelta
  obtain ⟨cΔ, hcΔ⟩ := exists_code_of_recursiveIn hDelta
  -- Values of the change-detector.
  have hdval : ∀ w t : ℕ,
      ((Nat.pair <$>
        ((g (Nat.unpair (Nat.unpair (Nat.pair w t)).1).1
          (Nat.unpair (Nat.unpair (Nat.pair w t)).1).2 : ℕ) : Part ℕ) <*>
        ((g (Nat.unpair (Nat.unpair (Nat.pair w t)).1).1
          ((Nat.unpair (Nat.unpair (Nat.pair w t)).1).2
            + (Nat.unpair (Nat.pair w t)).2 + 1) : ℕ) : Part ℕ))
      >>= fun z : ℕ =>
        ((1 - min 1 (((Nat.unpair z).1 - (Nat.unpair z).2)
          + ((Nat.unpair z).2 - (Nat.unpair z).1)) : ℕ) : Part ℕ))
      = Part.some (1 - min 1
          ((g (Nat.unpair w).1 (Nat.unpair w).2
            - g (Nat.unpair w).1 ((Nat.unpair w).2 + t + 1))
          + (g (Nat.unpair w).1 ((Nat.unpair w).2 + t + 1)
            - g (Nat.unpair w).1 (Nat.unpair w).2))) := by
    intro w t
    simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
      Seq.seq, Part.map_eq_map, Part.map_some]
  -- Domain of the change-detector = instability.
  have hdom : ∀ w : ℕ, (eval (toPFun X) cΔ w).Dom
      ↔ ¬ Stable g (Nat.unpair w).1 (Nat.unpair w).2 := by
    intro w
    rw [hcΔ]
    constructor
    · intro h
      obtain ⟨t, ht, -⟩ := Nat.rfind_dom.mp h
      rw [hdval w t] at ht
      simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff] at ht
      intro hst
      rw [hst t] at ht
      simp at ht
    · intro hst
      rw [Stable] at hst
      push_neg at hst
      obtain ⟨t, ht⟩ := hst
      refine Nat.rfind_dom.mpr ⟨t, ?_, fun {m} _ => ?_⟩
      · rw [hdval w t]
        simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
        symm
        rw [decide_eq_true_eq]
        omega
      · rw [hdval w m]
        trivial
  -- The jump question deciding stability, primitively in `w`.
  set hcode : ℕ → ℕ := fun w =>
    compEnc (encodeCode cΔ) (constEnc w) with hhcode
  have hcodeP : Nat.Primrec hcode := by
    rw [hhcode]
    exact Primrec.nat_iff.mp (compEnc_prim.comp
      (Primrec.const (encodeCode cΔ)) constEnc_prim)
  have hjq : ∀ w : ℕ, jumpP (toPFun X) (hcode w)
      ↔ ¬ Stable g (Nat.unpair w).1 (Nat.unpair w).2 := by
    intro w
    rw [hhcode, ← dom_iff_jumpP,
      show ofNatCode (encodeCode cΔ) = cΔ from ofNatCode_encodeCode cΔ]
    exact hdom w
  -- Assemble relative to the jump oracle.
  have horacle : Nat.RecursiveIn {toPFun (Cantor.jump X)} (fun v : ℕ =>
      ((hcode (Nat.pair (Nat.unpair v).1 (Nat.unpair v).2) : ℕ) : Part ℕ)
        >>= toPFun (Cantor.jump X)) :=
    Nat.RecursiveIn.comp (.oracle _ rfl)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        ((Primrec.nat_iff.mpr hcodeP).comp
          (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
            (Primrec.snd.comp Primrec.unpair)))))
  have hRfind := Nat.RecursiveIn.rfind horacle
  -- lift `g` along `X ≤ᵀ X′`
  have hgJ : Nat.RecursiveIn {toPFun (Cantor.jump X)}
      (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) := by
    refine Nat.RecursiveIn.subst hg fun O hO => ?_
    rw [Set.mem_singleton_iff.mp hO]
    have := le_jump X
    rw [Cantor.le] at this
    rw [show toPFun (Cantor.jump X) = jumpFn (toPFun X) from toPFun_jump X] at *
    exact RecursiveIn.iff_nat.mp this
  have hpairns : Nat.RecursiveIn {toPFun (Cantor.jump X)} (fun n : ℕ =>
      Nat.pair <$> ((n : ℕ) : Part ℕ) <*>
        (Nat.rfind fun s => (fun m => m = 0) <$>
          (((hcode (Nat.pair (Nat.unpair (Nat.pair n s)).1
            (Nat.unpair (Nat.pair n s)).2) : ℕ) : Part ℕ)
            >>= toPFun (Cantor.jump X)))) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hRfind
  have hFinal := Nat.RecursiveIn.comp hgJ hpairns
  refine hFinal.of_eq fun n => ?_
  -- Value analysis.
  have hjval : ∀ w : ℕ, toPFun (Cantor.jump X) w
      = Part.some (cond (Cantor.jump X w) 1 0) := fun w => rfl
  have htestval : ∀ s : ℕ,
      (((hcode (Nat.pair (Nat.unpair (Nat.pair n s)).1
        (Nat.unpair (Nat.pair n s)).2) : ℕ) : Part ℕ)
        >>= toPFun (Cantor.jump X))
      = Part.some (cond (Cantor.jump X (hcode (Nat.pair n s))) 1 0) := by
    intro s
    simp only [Nat.unpair_pair, Part.coe_some]
    rw [show (Part.some (hcode (Nat.pair n s)) >>= toPFun (Cantor.jump X))
      = toPFun (Cantor.jump X) (hcode (Nat.pair n s)) from Part.bind_some _ _]
    exact hjval _
  have hbit : ∀ s : ℕ,
      Cantor.jump X (hcode (Nat.pair n s)) = false ↔ Stable g n s := by
    intro s
    rw [Cantor.jump, decide_eq_false_iff_not, hjq (Nat.pair n s)]
    simp [Nat.unpair_pair]
  obtain ⟨s₀, hs₀⟩ := hlim n
  have hstab₀ : Stable g n s₀ := fun t => by
    rw [hs₀ _ (by omega), hs₀ _ (le_refl _)]
  have hdomR : (Nat.rfind fun s => (fun m => m = 0) <$>
      (((hcode (Nat.pair (Nat.unpair (Nat.pair n s)).1
        (Nat.unpair (Nat.pair n s)).2) : ℕ) : Part ℕ)
        >>= toPFun (Cantor.jump X))).Dom := by
    refine Nat.rfind_dom.mpr ⟨s₀, ?_, fun {m} _ => ?_⟩
    · rw [htestval s₀]
      rw [hbit s₀ |>.mpr hstab₀]
      simp
    · rw [htestval m]
      trivial
  obtain ⟨s', hs'⟩ := Part.dom_iff_mem.mp hdomR
  have hsbit : Cantor.jump X (hcode (Nat.pair n s')) = false := by
    have := Nat.rfind_spec hs'
    rw [htestval s'] at this
    simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff] at this
    cases hb : Cantor.jump X (hcode (Nat.pair n s'))
    · rfl
    · rw [hb] at this
      simp at this
  have hstab' : Stable g n s' := (hbit s').mp hsbit
  have hval : g n s' = f n :=
    (hstab' s₀).symm.trans (hs₀ _ (by omega))
  rw [show (Nat.rfind fun s => (fun m => m = 0) <$>
      (((hcode (Nat.pair (Nat.unpair (Nat.pair n s)).1
        (Nat.unpair (Nat.pair n s)).2) : ℕ) : Part ℕ)
        >>= toPFun (Cantor.jump X))) = Part.some s' from
    Part.eq_some_iff.mpr hs']
  simp only [Part.coe_some, Seq.seq, Part.map_eq_map, Part.map_some,
    Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  rw [hval]

end OracleCode
