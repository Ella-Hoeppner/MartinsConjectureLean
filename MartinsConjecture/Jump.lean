/-
The Turing jump and jump strictness.

Defines the jump `O′` of an oracle `O : ℕ →. ℕ` as the (diagonal) halting
problem relativized to `O`, packaged as the total 0/1-valued function
`jumpFn O`.  Main results:

* `jumpFn_not_turingReducible : ¬ jumpFn O ≤ᵀ O` — by diagonalization, using
  only the `exists_code` enumeration theorem and the `Nat.RecursiveIn`
  constructors (no universal machine needed).
* `turingReducible_jumpFn : O ≤ᵀ jumpFn O` — by unbounded search: `O(a)` is
  the unique `n` for which the jump answers "halts" on the code
  "compute `O(a)`, halt iff the result equals `n`".  The code family is a
  *primitive recursive* function of `(a, n)`, built from the numbering
  arithmetic in `OracleCode.lean`.
* strictness `O <ᵀ O′` packaged as `jumpFn_gt`, and the sanity anchor
  `jumpFn_not_partrec` (no jump is computable; in particular `∅′` is not).

`jumpFn O` is typed as `ℕ → Part ℕ` (definitionally equal to `ℕ →. ℕ`) so
that `Part` simp lemmas apply to `Part.some _ >>= jumpFn O` without fighting
the non-reducible `PFun`.
-/
import MartinsConjecture.OracleCode

open scoped Computability
open OracleCode

attribute [local instance] Classical.propDecidable

/-- The jump predicate: `e` is in the jump of `O` iff the `e`-th oracle machine
with oracle `O` halts on input `e` (diagonal halting problem relative to `O`). -/
def jumpP (O : ℕ →. ℕ) (e : ℕ) : Prop :=
  (eval O (ofNatCode e) e).Dom

/-- The jump of `O`, as a total 0/1-valued function: the characteristic
function of the diagonal halting problem relative to `O`. -/
noncomputable def jumpFn (O : ℕ →. ℕ) : ℕ → Part ℕ :=
  fun e => Part.some (if jumpP O e then 1 else 0)

theorem jumpFn_eq_one {O : ℕ →. ℕ} {e : ℕ} (h : jumpP O e) :
    jumpFn O e = Part.some 1 := by simp [jumpFn, h]

theorem jumpFn_eq_zero {O : ℕ →. ℕ} {e : ℕ} (h : ¬ jumpP O e) :
    jumpFn O e = Part.some 0 := by simp [jumpFn, h]

theorem jumpFn_dom (O : ℕ →. ℕ) (e : ℕ) : (jumpFn O e).Dom := trivial

/-! ### The jump is not reducible to the oracle (diagonalization) -/

theorem jumpFn_not_turingReducible (O : ℕ →. ℕ) : ¬ jumpFn O ≤ᵀ O := by
  intro h
  have hnat : Nat.RecursiveIn {O} (jumpFn O) := RecursiveIn.iff_nat.mp h
  -- The diagonal function `D a = μ n [jumpFn O a = 0]`:
  -- halts (with value 0) iff `a ∉ O′`.  It is recursive in `O` by assumption.
  have hin : Nat.RecursiveIn {O} (fun p : ℕ => ((Nat.unpair p).1 : Part ℕ) >>= jumpFn O) :=
    Nat.RecursiveIn.comp hnat Nat.RecursiveIn.left
  have hD : Nat.RecursiveIn {O}
      (fun a => Nat.rfind fun n => (fun m => m = 0) <$>
        (((Nat.unpair (Nat.pair a n)).1 : Part ℕ) >>= jumpFn O)) :=
    Nat.RecursiveIn.rfind hin
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn hD
  -- Compute the values of `D`.
  have hval : ∀ a, eval O c a = if jumpP O a then Part.none else Part.some 0 := by
    intro a
    rw [hc]
    by_cases hj : jumpP O a
    · rw [if_pos hj, Part.eq_none_iff']
      intro hdom
      obtain ⟨n, htrue, -⟩ := Nat.rfind_dom.mp hdom
      simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
        jumpFn_eq_one hj] at htrue
    · rw [if_neg hj, Part.eq_some_iff]
      refine Nat.mem_rfind.mpr ⟨?_, fun {m} hm => absurd hm (Nat.not_lt_zero m)⟩
      simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
        jumpFn_eq_zero hj]
  -- Diagonalize at the code of `D`.
  have hdom : jumpP O (encodeCode c) ↔ (eval O c (encodeCode c)).Dom := by
    unfold jumpP
    rw [ofNatCode_encodeCode]
  by_cases hj : jumpP O (encodeCode c)
  · have h1 : eval O c (encodeCode c) = Part.none := by rw [hval, if_pos hj]
    have h2 : (eval O c (encodeCode c)).Dom := hdom.mp hj
    rw [h1] at h2
    exact h2
  · have h1 : eval O c (encodeCode c) = Part.some 0 := by rw [hval, if_neg hj]
    exact hj (hdom.mpr (by rw [h1]; trivial))

/-! ### The oracle is reducible to its jump (unbounded search) -/

theorem turingReducible_jumpFn (O : ℕ →. ℕ) : O ≤ᵀ jumpFn O := by
  refine RecursiveIn.iff_nat.mpr ?_
  -- An "equality test" code: `eval O cEq w` halts iff the two components of
  -- the pair `w` are equal.  Built as `rfind` over the primitive recursive
  -- distance function, so we get it from `exists_code` for free.
  have hdista : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair p).1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hdistb : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair p).1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hdist : Primrec fun p : ℕ =>
      ((Nat.unpair (Nat.unpair p).1).1 - (Nat.unpair (Nat.unpair p).1).2)
        + ((Nat.unpair (Nat.unpair p).1).2 - (Nat.unpair (Nat.unpair p).1).1) :=
    Primrec.nat_add.comp (Primrec.nat_sub.comp hdista hdistb)
      (Primrec.nat_sub.comp hdistb hdista)
  obtain ⟨cDist, hcDist⟩ := exists_code_of_recursiveIn
    ((Nat.Partrec.of_primrec (Primrec.nat_iff.mp hdist)).recursiveIn (O := {O}))
  have hEqDom : ∀ w : ℕ, (eval O (.rfind cDist) w).Dom
      ↔ (Nat.unpair w).1 = (Nat.unpair w).2 := by
    intro w
    rw [dom_eval_rfind]
    constructor
    · rintro ⟨n, h0, -⟩
      rw [hcDist] at h0
      simp only [PFun.coe_val, Part.mem_some_iff, Nat.unpair_pair] at h0
      omega
    · intro hw
      refine ⟨0, ?_, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
      rw [hcDist]
      simp only [PFun.coe_val, Part.mem_some_iff, Nat.unpair_pair]
      omega
  -- The primitive recursive code family `k a n` = "compute `O a`, halt iff = n".
  set k : ℕ → ℕ → ℕ := fun a n =>
    compEnc (encodeCode (OracleCode.rfind cDist))
      (pairEnc (constEnc n) (compEnc 4 (constEnc a))) with hk
  have hkcode : ∀ a n, ofNatCode (k a n)
      = OracleCode.comp (.rfind cDist) (.pair (const n) (.comp .oracle (const a))) := by
    intro a n
    have hval : k a n = encodeCode
        (OracleCode.comp (.rfind cDist) (.pair (const n) (.comp .oracle (const a)))) := by
      simp only [hk, constEnc, compEnc, pairEnc, encodeCode]
    rw [hval, ofNatCode_encodeCode]
  -- The key equivalence: the jump answers "halts" at `k a n` iff `O a = n`.
  have hkey : ∀ a n, jumpP O (k a n) ↔ n ∈ O a := by
    intro a n
    unfold jumpP
    rw [hkcode a n, Part.dom_iff_mem]
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨w, hw, hrEq⟩ := mem_eval_comp.mp hr
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_eval_pair.mp hw
      rw [eval_const, Part.mem_some_iff] at hx
      subst hx
      obtain ⟨b, hb, hyO⟩ := mem_eval_comp.mp hy
      rw [eval_const, Part.mem_some_iff] at hb
      subst hb
      have hd := (hEqDom (Nat.pair x y)).mp (Part.dom_iff_mem.mpr ⟨r, hrEq⟩)
      simp only [Nat.unpair_pair] at hd
      exact hd ▸ hyO
    · intro hn
      obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp
        ((hEqDom (Nat.pair n n)).mpr (by rw [Nat.unpair_pair]))
      exact ⟨r, mem_eval_comp.mpr ⟨Nat.pair n n,
        mem_eval_pair.mpr ⟨n, by rw [eval_const]; exact Part.mem_some_iff.mpr rfl,
          n, mem_eval_comp.mpr ⟨a, by rw [eval_const]; exact Part.mem_some_iff.mpr rfl, hn⟩,
          rfl⟩, hr⟩⟩
  -- Primitive recursiveness of the code family, as a function of one paired input.
  have hqPrim : Primrec fun p : ℕ => k (Nat.unpair p).1 (Nat.unpair p).2 := by
    simp only [hk]
    exact compEnc_prim.comp (Primrec.const (encodeCode (OracleCode.rfind cDist)))
      (pairEnc_prim.comp
        (constEnc_prim.comp (Primrec.snd.comp Primrec.unpair))
        (compEnc_prim.comp (Primrec.const 4)
          (constEnc_prim.comp (Primrec.fst.comp Primrec.unpair))))
  have hq : Nat.RecursiveIn {jumpFn O}
      (fun p : ℕ => ((k (Nat.unpair p).1 (Nat.unpair p).2 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp hqPrim)
  -- Chain: query the jump at `k a n`, flip the answer, and search.
  have hF1 : Nat.RecursiveIn {jumpFn O}
      (fun p : ℕ => ((k (Nat.unpair p).1 (Nat.unpair p).2 : ℕ) : Part ℕ) >>= jumpFn O) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) hq
  have hsub : Nat.RecursiveIn {jumpFn O} (fun v : ℕ => ((1 - v : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn
      (Primrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id))
  have hF2 : Nat.RecursiveIn {jumpFn O}
      (fun p : ℕ => (((k (Nat.unpair p).1 (Nat.unpair p).2 : ℕ) : Part ℕ) >>= jumpFn O)
        >>= fun v : ℕ => ((1 - v : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hsub hF1
  have hF3 := Nat.RecursiveIn.rfind hF2
  refine hF3.of_eq fun a => ?_
  -- Value computation: the search returns exactly `O a`.
  have hquery : ∀ n : ℕ,
      ((((k (Nat.unpair (Nat.pair a n)).1 (Nat.unpair (Nat.pair a n)).2 : ℕ)
        : Part ℕ) >>= jumpFn O) >>= fun v : ℕ => ((1 - v : ℕ) : Part ℕ))
      = Part.some (if jumpP O (k a n) then 0 else 1) := by
    intro n
    by_cases hj : jumpP O (k a n)
    · simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
        jumpFn_eq_one hj, hj]
    · simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some,
        jumpFn_eq_zero hj, hj]
  apply Part.ext
  intro v
  constructor
  · intro hv
    obtain ⟨htrue, -⟩ := Nat.mem_rfind.mp hv
    rw [hquery v] at htrue
    simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff] at htrue
    by_cases hj : jumpP O (k a v)
    · exact (hkey a v).mp hj
    · rw [if_neg hj] at htrue
      simp at htrue
  · intro hv
    have hj : jumpP O (k a v) := (hkey a v).mpr hv
    refine Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩
    · rw [hquery v]
      simp [Part.map_eq_map, Part.map_some, Part.mem_some_iff, hj]
    · have hjm : ¬ jumpP O (k a m) := by
        intro hjm
        have := Part.mem_unique ((hkey a m).mp hjm) hv
        omega
      rw [hquery m]
      simp [Part.map_eq_map, Part.map_some, Part.mem_some_iff, hjm]

/-! ### Towards invariance of the jump: code translation

If `A` is computed by code `cI` relative to `B`, every `A`-oracle code can be
translated to a `B`-oracle code by splicing in `cI` for the `oracle`
constructor.  This is the mathematical content of "the jump is order
preserving"; the primitive recursiveness of the translation on *encodings* — the
remaining ingredient — is discharged in `JumpInvariance.lean` (`trE_primrec`). -/

/-- Splice the code `cI` in place of every `oracle` call. -/
def trOracle (cI : OracleCode) : OracleCode → OracleCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .oracle => cI
  | .pair a b => .pair (trOracle cI a) (trOracle cI b)
  | .comp a b => .comp (trOracle cI a) (trOracle cI b)
  | .prec a b => .prec (trOracle cI a) (trOracle cI b)
  | .rfind a => .rfind (trOracle cI a)

/-- Translation is semantics preserving. -/
theorem eval_trOracle {A B : ℕ →. ℕ} {cI : OracleCode} (hI : eval B cI = A) :
    ∀ c, eval B (trOracle cI c) = eval A c := by
  intro c
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | oracle => exact hI
  | pair a b iha ihb => funext n; simp only [trOracle, eval, iha, ihb]
  | comp a b iha ihb => funext n; simp only [trOracle, eval, iha, ihb]
  | prec a b iha ihb => funext n; simp only [trOracle, eval, iha, ihb]
  | rfind a iha => funext n; simp only [trOracle, eval, iha]

/-- The jump question about `A` at `e` is a jump question about `B` at an
explicitly given translated code.  (The function `e ↦` that code is
primitive recursive on encodings — formalized in `JumpInvariance.lean`
(`trE_primrec`), giving `A ≤ᵀ B → jumpFn A ≤ᵀ jumpFn B`.) -/
theorem jumpP_trOracle {A B : ℕ →. ℕ} {cI : OracleCode} (hI : eval B cI = A) (e : ℕ) :
    jumpP A e
      ↔ jumpP B (encodeCode (.comp (trOracle cI (ofNatCode e)) (const e))) := by
  unfold jumpP
  rw [ofNatCode_encodeCode]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp h
    refine Part.dom_iff_mem.mpr ⟨r, mem_eval_comp.mpr ⟨e, ?_, ?_⟩⟩
    · rw [eval_const]; exact Part.mem_some_iff.mpr rfl
    · rw [eval_trOracle hI]; exact hr
  · intro h
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b, hb, hrb⟩ := mem_eval_comp.mp hr
    rw [eval_const, Part.mem_some_iff] at hb
    subst hb
    rw [eval_trOracle hI] at hrb
    exact Part.dom_iff_mem.mpr ⟨r, hrb⟩

/-! ### Strictness, and sanity anchors -/

/-- **Jump strictness**: every oracle is strictly below its jump. -/
theorem jumpFn_gt (O : ℕ →. ℕ) : O ≤ᵀ jumpFn O ∧ ¬ jumpFn O ≤ᵀ O :=
  ⟨turingReducible_jumpFn O, jumpFn_not_turingReducible O⟩

/-- No jump is computable (relativized unsolvability of the halting problem). -/
theorem jumpFn_not_partrec (O : ℕ →. ℕ) : ¬ Nat.Partrec (jumpFn O) := fun h =>
  jumpFn_not_turingReducible O ((Partrec.nat_iff.mpr h).recursiveIn)

/-- Sanity anchor: `∅′ ≰ᵀ ∅` — the (unrelativized) halting problem is
genuinely uncomputable in this encoding. -/
theorem halting_problem_not_partrec : ¬ Nat.Partrec (jumpFn fun _ => Part.some 0) :=
  jumpFn_not_partrec _

#print axioms jumpFn_gt
#print axioms jumpFn_not_partrec
