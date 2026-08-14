/-
Toward the **explicit** universal machine as a single `OracleCode`.

`Universal.lean` proves `eval_universal` — the two-argument evaluator is
*recursive in* any total oracle — but as a per-oracle `RecursiveIn` proposition,
so `exists_code` off it yields a code depending on the oracle.  Several
constructions (notably the coding reals of Lachlan's discontinuous case, whose
recovery machine runs with a varying oracle `Y_c`) need a *single* explicit code
`univCode : OracleCode` with `eval (toPFun X) univCode ⟨e,n⟩ = eval (toPFun X)
(ofNatCode e) n` for every total `0/1` oracle `X`.

This file builds the **only genuinely oracle-using ingredient**: `cGraph`, an
explicit `OracleCode` that enumerates the oracle's own graph prefixes
(`eval_cGraph : eval (toPFun X) cGraph k = graphEnc X k`).  Every remaining part
of the machine (`evaln`, the stage test `ts`, extraction) is oracle-independent
and gets an *oracle-generic* code via `exists_code_of_partrec`; assembling those
with `cGraph`, `curry`, and the `rfind`/`comp` constructors — mirroring
`eval_universal`'s proof at the code level — yields `univCode`.  That assembly is
the remaining step (see `ATTACK.md`); `cGraph` and its Part-monad evaluation
idiom (applied-form `eval_left_app`/`eval_right_app` + explicit `Part.bind_some`
terms for `PFun` continuations) are the reusable groundwork done here.
-/
import MartinsConjecture.Universal

open scoped Computability
open OracleCode Cantor

namespace OracleCode

/-! ### The explicit oracle-graph-prefix encoder `cGraph` -/

/-- Append one value to an encoded list (local copy of `Universal.concatE`). -/
def concatE' : ℕ → ℕ :=
  fun p => Encodable.encode
    (((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD []) ++ [(Nat.unpair p).2])

theorem concatE'_prim : Primrec concatE' :=
  Primrec.encode.comp (Primrec.list_concat.comp
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const ([] : List ℕ)))
    (Primrec.snd.comp Primrec.unpair))

theorem concatE'_encode (l : List ℕ) (b : ℕ) :
    concatE' (Nat.pair (Encodable.encode l) b) = Encodable.encode (l ++ [b]) := by
  rw [concatE']
  simp [Nat.unpair_pair, Encodable.encodek]

/-- An oracle-generic code for `concatE'`. -/
noncomputable def cConcat : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp concatE'_prim))).choose

theorem cConcat_spec (O : ℕ →. ℕ) (p : ℕ) : eval O cConcat p = Part.some (concatE' p) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp concatE'_prim))).choose_spec O) p

/-- The `prec` step: from `⟨a, ⟨y, IH⟩⟩` append the oracle's value at `y`. -/
noncomputable def cGraphStep : OracleCode :=
  .comp cConcat (.pair (.comp .right .right) (.comp .oracle (.comp .left .right)))

/-- The `prec` recursion producing `encode (graphOf (bitg X) ·)` from `⟨0, k⟩`. -/
noncomputable def cGraphPrec : OracleCode :=
  .prec (const (Encodable.encode ([] : List ℕ))) cGraphStep

/-- The explicit oracle-graph-prefix encoder: `eval (toPFun X) cGraph k = graphEnc X k`. -/
noncomputable def cGraph : OracleCode := .comp cGraphPrec (.pair (const 0) idCode)

theorem eval_left_fn (O : ℕ →. ℕ) : eval O .left = fun n => Part.some (Nat.unpair n).1 := rfl
theorem eval_right_fn (O : ℕ →. ℕ) : eval O .right = fun n => Part.some (Nat.unpair n).2 := rfl

theorem eval_left_app (O : ℕ →. ℕ) (a b : ℕ) : eval O .left (Nat.pair a b) = Part.some a := by
  simp only [eval_left_fn, Nat.unpair_pair]

theorem eval_right_app (O : ℕ →. ℕ) (a b : ℕ) : eval O .right (Nat.pair a b) = Part.some b := by
  simp only [eval_right_fn, Nat.unpair_pair]

theorem eval_cGraphStep (X : ℕ → Bool) (a y i : ℕ) :
    eval (toPFun X) cGraphStep (Nat.pair a (Nat.pair y i))
      = Part.some (concatE' (Nat.pair i (bitg X y))) := by
  have hA : eval (toPFun X) (.comp .right .right) (Nat.pair a (Nat.pair y i)) = Part.some i := by
    rw [eval_comp, eval_right_app,
      show (Part.some (Nat.pair y i) >>= eval (toPFun X) .right)
        = eval (toPFun X) .right (Nat.pair y i) from Part.bind_some _ _, eval_right_app]
  have hB : eval (toPFun X) (.comp .oracle (.comp .left .right)) (Nat.pair a (Nat.pair y i))
      = Part.some (bitg X y) := by
    have hLR : eval (toPFun X) (.comp .left .right) (Nat.pair a (Nat.pair y i)) = Part.some y := by
      rw [eval_comp, eval_right_app,
        show (Part.some (Nat.pair y i) >>= eval (toPFun X) .left)
          = eval (toPFun X) .left (Nat.pair y i) from Part.bind_some _ _, eval_left_app]
    rw [eval_comp, hLR,
      show (Part.some y >>= eval (toPFun X) .oracle) = eval (toPFun X) .oracle y from
        Part.bind_some _ _, eval_oracle, toPFun_eq_bitg]
  rw [cGraphStep, eval_comp, eval_pair_eq, hA, hB]
  simp only [Part.map_some, Part.bind_some]
  rw [show (Part.some (Nat.pair i (bitg X y)) >>= eval (toPFun X) cConcat)
      = eval (toPFun X) cConcat (Nat.pair i (bitg X y)) from Part.bind_some _ _, cConcat_spec]

theorem eval_cGraph (X : ℕ → Bool) (k : ℕ) :
    eval (toPFun X) cGraph k = graphEnc X k := by
  have hpair0 : eval (toPFun X) (.pair (const 0) idCode) k = Part.some (Nat.pair 0 k) := by
    simp only [eval_pair_eq, eval_const, eval_idCode, Part.map_some, Part.bind_eq_bind,
      Part.bind_some]
  rw [cGraph, eval_comp,
    show eval (toPFun X) (.pair (const 0) idCode) k >>= eval (toPFun X) cGraphPrec
      = eval (toPFun X) cGraphPrec (Nat.pair 0 k) from by rw [hpair0]; exact Part.bind_some _ _]
  -- unfold prec and induct on k
  show (Nat.unpair (Nat.pair 0 k)).2.rec
      (eval (toPFun X) (const (Encodable.encode ([] : List ℕ))) (Nat.unpair (Nat.pair 0 k)).1)
      (fun y IH => IH >>= fun i =>
        eval (toPFun X) cGraphStep (Nat.pair (Nat.unpair (Nat.pair 0 k)).1 (Nat.pair y i)))
      = graphEnc X k
  rw [Nat.unpair_pair]
  clear hpair0
  induction k with
  | zero => rw [eval_const]; rfl
  | succ k ih =>
    show (Nat.rec (motive := fun _ => Part ℕ) _ _ k) >>= _ = _
    rw [ih, show graphEnc X k = Part.some (Encodable.encode (graphOf (bitg X) k)) from rfl,
      show (Part.some (Encodable.encode (graphOf (bitg X) k)) >>= fun i =>
          eval (toPFun X) cGraphStep (Nat.pair 0 (Nat.pair k i)))
        = eval (toPFun X) cGraphStep (Nat.pair 0 (Nat.pair k
            (Encodable.encode (graphOf (bitg X) k)))) from Part.bind_some _ _,
      eval_cGraphStep, concatE'_encode,
      show graphEnc X (k + 1)
        = Part.some (Encodable.encode (graphOf (bitg X) (k + 1))) from rfl]
    congr 2
    rw [graphOf, graphOf, List.range_succ, List.map_append]
    rfl

#print axioms eval_cGraph

/-! ### The oracle-free ingredients and the assembled universal code -/

/-- Decoded `evaln` as a primitive recursive function (local copy). -/
def uEvalnD : ℕ → Option ℕ := fun v =>
  evaln (Nat.unpair (Nat.unpair v).1).2
    ((Encodable.decode (α := List ℕ) (Nat.unpair v).2).getD [])
    (ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
    (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2

theorem uEvalnD_prim : Primrec uEvalnD := by
  have hg : Primrec fun v : ℕ =>
      ((((Nat.unpair (Nat.unpair v).1).2,
        (Encodable.decode (α := List ℕ) (Nat.unpair v).2).getD []),
        ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1),
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2) := by
    refine Primrec.pair (Primrec.pair (Primrec.pair ?_ ?_) ?_) ?_
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    · exact Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const ([] : List ℕ))
    · exact (Primrec.ofNat OracleCode).comp
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    · exact Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  exact evaln_prim.comp hg

theorem uEvalnD_graph (X : ℕ → Bool) (p k : ℕ) :
    uEvalnD (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k)))
      = evaln k (graphOf (bitg X) k) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2 := by
  rw [uEvalnD]; simp [Nat.unpair_pair, Encodable.encodek]

/-- Stage test: `0` iff stage `k` already answers. -/
def uTs : ℕ → ℕ := fun v => cond (uEvalnD v).isSome 0 1

theorem uTs_prim : Primrec uTs :=
  Primrec.cond (Primrec.option_isSome.comp uEvalnD_prim) (Primrec.const 0) (Primrec.const 1)

/-- Value extraction. -/
def uExtv : ℕ → ℕ := fun v => (uEvalnD v).getD 0

theorem uExtv_prim : Primrec uExtv := Primrec.option_getD.comp uEvalnD_prim (Primrec.const 0)

/-- Oracle-generic code for the stage test. -/
noncomputable def cTs : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp uTs_prim))).choose

theorem cTs_spec (O : ℕ →. ℕ) (v : ℕ) : eval O cTs v = Part.some (uTs v) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp uTs_prim))).choose_spec O) v

/-- Oracle-generic code for extraction. -/
noncomputable def cExtv : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp uExtv_prim))).choose

theorem cExtv_spec (O : ℕ →. ℕ) (v : ℕ) : eval O cExtv v = Part.some (uExtv v) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp uExtv_prim))).choose_spec O) v

/-- Assemble `⟨p, k⟩ ↦ ⟨⟨p,k⟩, graphEnc X k⟩` — the argument the stage test consumes. -/
noncomputable def asmCode : OracleCode := .pair idCode (.comp cGraph .right)

theorem eval_asmCode (X : ℕ → Bool) (p k : ℕ) :
    eval (toPFun X) asmCode (Nat.pair p k)
      = Part.some (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k))) := by
  have hg : eval (toPFun X) (.comp cGraph .right) (Nat.pair p k)
      = Part.some (Encodable.encode (graphOf (bitg X) k)) := by
    rw [eval_comp, eval_right_app,
      show (Part.some k >>= eval (toPFun X) cGraph) = eval (toPFun X) cGraph k from
        Part.bind_some _ _, eval_cGraph, graphEnc]
  rw [asmCode, eval_pair_eq, eval_idCode, hg]
  simp only [Part.map_some, Part.bind_some]

/-- The stage search: least `k` at which `evaln` answers. -/
noncomputable def cSearch : OracleCode := .rfind (.comp cTs asmCode)

/-- **The explicit universal machine.** -/
noncomputable def univCode : OracleCode := .comp cExtv (.comp asmCode (.pair idCode cSearch))

/-- The inner stage-test value. -/
theorem eval_test (X : ℕ → Bool) (p k : ℕ) :
    eval (toPFun X) (.comp cTs asmCode) (Nat.pair p k)
      = Part.some (uTs (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k)))) := by
  rw [eval_comp, eval_asmCode,
    show (Part.some (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k)))
        >>= eval (toPFun X) cTs)
      = eval (toPFun X) cTs (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k)))
      from Part.bind_some _ _, cTs_spec]

/-- Membership in the stage search: `v` is the least stage that answers. -/
theorem mem_cSearch (X : ℕ → Bool) (p v : ℕ) :
    v ∈ eval (toPFun X) cSearch p ↔
      uTs (Nat.pair (Nat.pair p v) (Encodable.encode (graphOf (bitg X) v))) = 0
      ∧ ∀ m < v, uTs (Nat.pair (Nat.pair p m) (Encodable.encode (graphOf (bitg X) m))) ≠ 0 := by
  rw [cSearch, mem_eval_rfind]
  constructor
  · rintro ⟨h1, h2⟩
    rw [eval_test, Part.mem_some_iff] at h1
    refine ⟨h1.symm, fun m hm => ?_⟩
    obtain ⟨x, hx, hxne⟩ := h2 m hm
    rw [eval_test, Part.mem_some_iff] at hx
    rw [← hx]; exact hxne
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [eval_test]; exact Part.mem_some_iff.mpr h1.symm, fun m hm => ?_⟩
    exact ⟨_, by rw [eval_test]; exact Part.mem_some _, h2 m hm⟩

/-- `uTs = 0` exactly means `evaln` answers at that stage. -/
theorem uTs_eq_zero_iff (X : ℕ → Bool) (p k : ℕ) :
    uTs (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k))) = 0
      ↔ (evaln k (graphOf (bitg X) k) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2).isSome := by
  rw [uTs, uEvalnD_graph]
  cases (evaln k (graphOf (bitg X) k) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2).isSome <;>
    simp

/-- **Universality of the explicit code**: for every total `0/1` oracle `X`,
`univCode` on `⟨e,n⟩` computes `Φ_e^X(n)`.  A single `OracleCode` valid for all
oracles — the artifact `eval_universal` supplies only per-oracle. -/
theorem eval_univCode (X : ℕ → Bool) (p : ℕ) :
    eval (toPFun X) univCode p
      = eval (toPFun X) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2 := by
  have hO : ∀ i, toPFun X i = Part.some (bitg X i) := toPFun_eq_bitg X
  apply Part.ext
  intro y
  constructor
  · -- forward: unfold `univCode` and read off the answer via `evaln_sound`
    intro hy
    rw [univCode, mem_eval_comp] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    rw [cExtv_spec, Part.mem_some_iff] at hyb
    rw [mem_eval_comp] at hb
    obtain ⟨c, hc, hbc⟩ := hb
    rw [mem_eval_pair] at hc
    obtain ⟨a, ha, d, hd, hcad⟩ := hc
    rw [eval_idCode, Part.mem_some_iff] at ha
    subst a
    subst hcad
    rw [eval_asmCode, Part.mem_some_iff] at hbc
    subst hbc
    rw [mem_cSearch] at hd
    have hsome := (uTs_eq_zero_iff X p d).mp hd.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    rw [hyb, uExtv, uEvalnD_graph, hv, Option.getD_some]
    exact evaln_sound (graphOf_sound hO d) hv
  · -- backward: `evaln` converges somewhere, so the search halts at the least stage
    intro hy
    obtain ⟨k₀, hk₀⟩ := evaln_complete hO hy
    have hk₀some : (evaln k₀ (graphOf (bitg X) k₀)
        (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2).isSome := by rw [hk₀]; rfl
    have hdom : (eval (toPFun X) cSearch p).Dom := by
      rw [cSearch, dom_eval_rfind]
      refine ⟨k₀, ?_, fun m _ => ?_⟩
      · rw [eval_test]; exact Part.mem_some_iff.mpr ((uTs_eq_zero_iff X p k₀).mpr hk₀some).symm
      · rw [eval_test]; trivial
    obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp hdom
    have hdz := (mem_cSearch X p d).mp hd
    have hsome := (uTs_eq_zero_iff X p d).mp hdz.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    have hvy : v = y :=
      Part.mem_unique (evaln_sound (graphOf_sound hO d) hv) hy
    rw [univCode, mem_eval_comp]
    refine ⟨Nat.pair (Nat.pair p d) (Encodable.encode (graphOf (bitg X) d)), ?_, ?_⟩
    · rw [mem_eval_comp]
      refine ⟨Nat.pair p d, ?_, ?_⟩
      · rw [mem_eval_pair]
        exact ⟨p, by rw [eval_idCode]; exact Part.mem_some _, d, hd, rfl⟩
      · rw [eval_asmCode]; exact Part.mem_some _
    · rw [cExtv_spec, uExtv, uEvalnD_graph, hv, Option.getD_some, hvy]
      exact Part.mem_some _

#print axioms eval_univCode

end OracleCode
