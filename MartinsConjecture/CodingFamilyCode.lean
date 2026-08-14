/-
The explicit oracle-generic recovery code for `HasCodingFamily`'s backward s-m-n
component.

`yc_backward` (in `CodingFamily.lean`) shows `X ≤ᵀ Y_c` per `c`, but the fixed-shift
`recFnK` cannot be s-m-n'd uniformly (its `K = |wit|` is `X`-dependent).  For the
`EquivVia` interface we need one *oracle-generic* `OracleCode` that recovers `X`
from any oracle `O` — computing the shift `K` from `O` at runtime via the `wit`
search.  This file builds that code from `cGraph` (the explicit oracle-graph
encoder), oracle-free `evaln`/test codes (`exists_code_of_partrec`), the `rfind`
search constructors, and oracle queries, then packages it by `curryEnc` into the
computable index map `s`, discharging `HasCodingFamily`.
-/
import MartinsConjecture.CodingFamily

set_option maxHeartbeats 1000000

open scoped Computability
open OracleCode Cantor

namespace OracleCode
namespace Coding

attribute [local instance] Classical.propDecidable

/-! ### The halting-stage search as an explicit oracle code -/

/-- Oracle-free test on `w = ⟨⟨c,m⟩, g⟩` (`g` the encoded oracle graph): `0` if
`evaln` halts (with table `g`), else `1` — the `hStage`-search predicate. -/
def notHaltFn (w : ℕ) : ℕ :=
  bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair w).1).1
    (Nat.unpair (Nat.unpair w).1).1) (Nat.unpair (Nat.unpair w).1).2)
    (Nat.unpair w).2)).isSome then 0 else 1

theorem notHaltFn_prim : Primrec notHaltFn := by
  refine Primrec.cond
    (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_)) (Primrec.const 0) (Primrec.const 1)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    (Primrec.snd.comp Primrec.unpair)

/-- Oracle-generic code for `notHaltFn`. -/
noncomputable def cNotHaltTest : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp notHaltFn_prim))).choose

theorem cNotHaltTest_spec (O : ℕ →. ℕ) (w : ℕ) :
    eval O cNotHaltTest w = Part.some (notHaltFn w) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp notHaltFn_prim))).choose_spec O) w

/-- `⟨c,m'⟩ ↦ notHalt bit` over oracle `O`: pack with the graph at `m'`, then test. -/
noncomputable def cNotHalt : OracleCode := .comp cNotHaltTest (.pair idCode (.comp cGraph .right))

theorem eval_cNotHalt (X : ℕ → Bool) (c m' : ℕ) :
    eval (toPFun X) cNotHalt (Nat.pair c m')
      = Part.some (bif haltedB X c m' then 0 else 1) := by
  have hg : eval (toPFun X) (.comp cGraph .right) (Nat.pair c m')
      = Part.some (Encodable.encode (graphOf (bitg X) m')) := by
    rw [eval_comp, eval_right_app,
      show (Part.some m' >>= eval (toPFun X) cGraph) = eval (toPFun X) cGraph m' from
        Part.bind_some _ _, eval_cGraph, graphEnc]
  have hpair : eval (toPFun X) (.pair idCode (.comp cGraph .right)) (Nat.pair c m')
      = Part.some (Nat.pair (Nat.pair c m') (Encodable.encode (graphOf (bitg X) m'))) := by
    rw [eval_pair_eq, eval_idCode, hg]; simp only [Part.map_some, Part.bind_some]
  rw [cNotHalt, eval_comp, hpair,
    show (Part.some (Nat.pair (Nat.pair c m') (Encodable.encode (graphOf (bitg X) m')))
        >>= eval (toPFun X) cNotHaltTest)
      = eval (toPFun X) cNotHaltTest (Nat.pair (Nat.pair c m')
          (Encodable.encode (graphOf (bitg X) m'))) from Part.bind_some _ _,
    cNotHaltTest_spec]
  congr 1
  rw [notHaltFn]
  simp only [Nat.unpair_pair]
  rw [uEvalnD_graph, Nat.unpair_pair]
  rfl

/-- The explicit halting-stage search. -/
noncomputable def cHStage : OracleCode := .rfind cNotHalt

/-- On a converging `c`, `cHStage` returns the halting stage. -/
theorem eval_cHStage (X : ℕ → Bool) (c : ℕ) (h : conv X c) :
    eval (toPFun X) cHStage c = Part.some (hStage X c) := by
  rw [cHStage, eval_rfind]
  simp only [eval_cNotHalt, Part.map_eq_map, Part.map_some]
  exact hStageSearch_eq X c h

#print axioms eval_cHStage

/-! ### The witness search as an explicit oracle code -/

/-- Oracle-free witness-pair test on `w = ⟨⟨t,p⟩, g⟩` (`g` the encoded graph at `t`). -/
def witTestFn (e n₀ : ℕ) (w : ℕ) : ℕ :=
  bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair e n₀)
      (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2)
      (encTable (Nat.unpair w).2 (Nat.unpair (Nat.unpair w).1).2))).isSome then 0 else 1

theorem witTestFn_prim (e n₀ : ℕ) : Primrec (witTestFn e n₀) := by
  refine Primrec.cond (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_))
    (Primrec.const 0) (Primrec.const 1)
  refine Primrec₂.natPair.comp (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.const e) (Primrec.const n₀))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))) ?_
  exact encTable_prim.comp (Primrec.snd.comp Primrec.unpair)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))

noncomputable def cWitTest (e n₀ : ℕ) : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (witTestFn_prim e n₀)))).choose

theorem cWitTest_spec (e n₀ : ℕ) (O : ℕ →. ℕ) (w : ℕ) :
    eval O (cWitTest e n₀) w = Part.some (witTestFn e n₀ w) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (witTestFn_prim e n₀)))).choose_spec O) w

noncomputable def cWit (e n₀ : ℕ) : OracleCode :=
  .comp (cWitTest e n₀) (.pair idCode (.comp cGraph .left))

theorem eval_cWit (e n₀ : ℕ) (X : ℕ → Bool) (t p : ℕ) :
    eval (toPFun X) (cWit e n₀) (Nat.pair t p)
      = Part.some (bif witPair e n₀ X t p then 0 else 1) := by
  have hg : eval (toPFun X) (.comp cGraph .left) (Nat.pair t p)
      = Part.some (Encodable.encode (graphOf (bitg X) t)) := by
    rw [eval_comp, eval_left_app,
      show (Part.some t >>= eval (toPFun X) cGraph) = eval (toPFun X) cGraph t from
        Part.bind_some _ _, eval_cGraph, graphEnc]
  have hpair : eval (toPFun X) (.pair idCode (.comp cGraph .left)) (Nat.pair t p)
      = Part.some (Nat.pair (Nat.pair t p) (Encodable.encode (graphOf (bitg X) t))) := by
    rw [eval_pair_eq, eval_idCode, hg]; simp only [Part.map_some, Part.bind_some]
  rw [cWit, eval_comp, hpair,
    show (Part.some (Nat.pair (Nat.pair t p) (Encodable.encode (graphOf (bitg X) t)))
        >>= eval (toPFun X) (cWitTest e n₀))
      = eval (toPFun X) (cWitTest e n₀) (Nat.pair (Nat.pair t p)
          (Encodable.encode (graphOf (bitg X) t))) from Part.bind_some _ _,
    cWitTest_spec]
  congr 1
  rw [witTestFn]
  simp only [Nat.unpair_pair]
  rw [← witPair_eq_uEvalnD]

/-- The explicit witness search. -/
noncomputable def cWitSearch (e n₀ : ℕ) : OracleCode := .rfind (cWit e n₀)

theorem eval_cWitSearch (e n₀ : ℕ) (X : ℕ → Bool) (t : ℕ)
    (h : ∃ p, witPair e n₀ X t p = true) :
    eval (toPFun X) (cWitSearch e n₀) t = Part.some (witEnc e n₀ X t) := by
  rw [cWitSearch, eval_rfind]
  simp only [eval_cWit, Part.map_eq_map, Part.map_some]
  exact witEncSearch_eq e n₀ X t h

#print axioms eval_cWitSearch

/-! ### The halted-bit code, the un-shift query, and the splice -/

def haltFn (w : ℕ) : ℕ :=
  bif (uEvalnD (Nat.pair (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair w).1).1
    (Nat.unpair (Nat.unpair w).1).1) (Nat.unpair (Nat.unpair w).1).2)
    (Nat.unpair w).2)).isSome then 1 else 0

theorem haltFn_prim : Primrec haltFn := by
  refine Primrec.cond
    (Primrec.option_isSome.comp (uEvalnD_prim.comp ?_)) (Primrec.const 1) (Primrec.const 0)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    (Primrec.snd.comp Primrec.unpair)

noncomputable def cHaltTest : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp haltFn_prim))).choose

theorem cHaltTest_spec (O : ℕ →. ℕ) (w : ℕ) : eval O cHaltTest w = Part.some (haltFn w) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp haltFn_prim))).choose_spec O) w

noncomputable def cHalted : OracleCode := .comp cHaltTest (.pair idCode (.comp cGraph .right))

theorem eval_cHalted (X : ℕ → Bool) (c m : ℕ) :
    eval (toPFun X) cHalted (Nat.pair c m) = Part.some (bif haltedB X c m then 1 else 0) := by
  have hg : eval (toPFun X) (.comp cGraph .right) (Nat.pair c m)
      = Part.some (Encodable.encode (graphOf (bitg X) m)) := by
    rw [eval_comp, eval_right_app,
      show (Part.some m >>= eval (toPFun X) cGraph) = eval (toPFun X) cGraph m from
        Part.bind_some _ _, eval_cGraph, graphEnc]
  have hpair : eval (toPFun X) (.pair idCode (.comp cGraph .right)) (Nat.pair c m)
      = Part.some (Nat.pair (Nat.pair c m) (Encodable.encode (graphOf (bitg X) m))) := by
    rw [eval_pair_eq, eval_idCode, hg]; simp only [Part.map_some, Part.bind_some]
  rw [cHalted, eval_comp, hpair,
    show (Part.some (Nat.pair (Nat.pair c m) (Encodable.encode (graphOf (bitg X) m)))
        >>= eval (toPFun X) cHaltTest)
      = eval (toPFun X) cHaltTest (Nat.pair (Nat.pair c m)
          (Encodable.encode (graphOf (bitg X) m))) from Part.bind_some _ _, cHaltTest_spec]
  congr 1
  rw [haltFn]
  simp only [Nat.unpair_pair]
  rw [uEvalnD_graph, Nat.unpair_pair]
  rfl

/-- The un-shift index `m + |decoded we|` from `Z = ⟨⟨⟨c,m⟩,t⟩, we⟩`. -/
def cIdxFn (Z : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair Z).1).1).2
    + ((Encodable.decode (α := List Bool) (Nat.unpair (Nat.unpair Z).2).1).getD []).length

theorem cIdxFn_prim : Primrec cIdxFn :=
  Primrec.nat_add.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    (Primrec.list_length.comp (Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair)))) (Primrec.const ([] : List Bool))))

noncomputable def cIdxCode : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp cIdxFn_prim))).choose

theorem cIdxCode_spec (O : ℕ →. ℕ) (Z : ℕ) : eval O cIdxCode Z = Part.some (cIdxFn Z) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp cIdxFn_prim))).choose_spec O) Z

/-- The splice (halted branch): search `hStage`, search `witEnc`, then query `O` at `m+|w|`. -/
noncomputable def cSpl (e n₀ : ℕ) : OracleCode :=
  .comp (.comp .oracle cIdxCode)
    (.comp (.pair idCode (.comp (cWitSearch e n₀) .right))
      (.pair idCode (.comp cHStage .left)))

theorem eval_cSpl (e n₀ : ℕ) (X : ℕ → Bool) (c m : ℕ) (h : conv X c)
    (hwp : ∃ p, witPair e n₀ X (hStage X c) p = true) :
    eval (toPFun X) (cSpl e n₀) (Nat.pair c m)
      = Part.some (bitg X (m + (wit e n₀ X (hStage X c)).length)) := by
  have hct : eval (toPFun X) (.comp cHStage .left) (Nat.pair c m) = Part.some (hStage X c) := by
    rw [eval_comp, eval_left_app,
      show (Part.some c >>= eval (toPFun X) cHStage) = eval (toPFun X) cHStage c from
        Part.bind_some _ _, eval_cHStage X c h]
  have hqt : eval (toPFun X) (.pair idCode (.comp cHStage .left)) (Nat.pair c m)
      = Part.some (Nat.pair (Nat.pair c m) (hStage X c)) := by
    rw [eval_pair_eq, eval_idCode, hct]; simp only [Part.map_some, Part.bind_some]
  have hwe : eval (toPFun X) (.comp (cWitSearch e n₀) .right)
      (Nat.pair (Nat.pair c m) (hStage X c)) = Part.some (witEnc e n₀ X (hStage X c)) := by
    rw [eval_comp, eval_right_app,
      show (Part.some (hStage X c) >>= eval (toPFun X) (cWitSearch e n₀))
        = eval (toPFun X) (cWitSearch e n₀) (hStage X c) from Part.bind_some _ _,
      eval_cWitSearch e n₀ X (hStage X c) hwp]
  have hqtwe : eval (toPFun X) (.pair idCode (.comp (cWitSearch e n₀) .right))
      (Nat.pair (Nat.pair c m) (hStage X c))
      = Part.some (Nat.pair (Nat.pair (Nat.pair c m) (hStage X c))
          (witEnc e n₀ X (hStage X c))) := by
    rw [eval_pair_eq, eval_idCode, hwe]; simp only [Part.map_some, Part.bind_some]
  rw [cSpl, eval_comp, eval_comp, hqt,
    show (Part.some (Nat.pair (Nat.pair c m) (hStage X c))
        >>= eval (toPFun X) (.pair idCode (.comp (cWitSearch e n₀) .right)))
      = eval (toPFun X) (.pair idCode (.comp (cWitSearch e n₀) .right))
          (Nat.pair (Nat.pair c m) (hStage X c)) from Part.bind_some _ _, hqtwe,
    show (Part.some (Nat.pair (Nat.pair (Nat.pair c m) (hStage X c))
          (witEnc e n₀ X (hStage X c))) >>= eval (toPFun X) (.comp .oracle cIdxCode))
      = eval (toPFun X) (.comp .oracle cIdxCode) (Nat.pair (Nat.pair (Nat.pair c m) (hStage X c))
          (witEnc e n₀ X (hStage X c))) from Part.bind_some _ _,
    eval_comp, cIdxCode_spec,
    show (Part.some (cIdxFn (Nat.pair (Nat.pair (Nat.pair c m) (hStage X c))
          (witEnc e n₀ X (hStage X c)))) >>= eval (toPFun X) OracleCode.oracle)
      = eval (toPFun X) OracleCode.oracle (cIdxFn (Nat.pair (Nat.pair (Nat.pair c m)
          (hStage X c)) (witEnc e n₀ X (hStage X c)))) from Part.bind_some _ _, eval_oracle]
  rw [show cIdxFn (Nat.pair (Nat.pair (Nat.pair c m) (hStage X c)) (witEnc e n₀ X (hStage X c)))
      = m + (wit e n₀ X (hStage X c)).length from by
    simp only [cIdxFn, Nat.unpair_pair, wit], toPFun_eq_bitg]

#print axioms eval_cSpl

/-! ### The assembled recovery code and `HasCodingFamily` -/

/-- Base branch: query `O` at `m`. -/
noncomputable def cBase : OracleCode := .comp .oracle .right

/-- Halted branch, taking its context from the `prec` input. -/
noncomputable def cSpl' (e n₀ : ℕ) : OracleCode := .comp (cSpl e n₀) .left

/-- **The explicit recovery code**: `prec`-select the splice (halted) or `O(m)`. -/
noncomputable def cRecCode (e n₀ : ℕ) : OracleCode :=
  .comp (.prec cBase (cSpl' e n₀)) (.pair idCode cHalted)

theorem eval_prec_pair (O : ℕ →. ℕ) (cf cg : OracleCode) (a n : ℕ) :
    eval O (.prec cf cg) (Nat.pair a n)
      = Nat.rec (motive := fun _ => Part ℕ) (eval O cf a)
          (fun y IH => IH >>= fun i => eval O cg (Nat.pair a (Nat.pair y i))) n := by
  show Nat.rec (motive := fun _ => Part ℕ) (eval O cf (Nat.unpair (Nat.pair a n)).1)
      (fun y IH => IH >>= fun i =>
        eval O cg (Nat.pair (Nat.unpair (Nat.pair a n)).1 (Nat.pair y i)))
      (Nat.unpair (Nat.pair a n)).2 = _
  rw [Nat.unpair_pair]

theorem eval_cBase (X : ℕ → Bool) (a : ℕ) :
    eval (toPFun X) cBase a = Part.some (bitg X (Nat.unpair a).2) := by
  rw [cBase, eval_comp, show eval (toPFun X) OracleCode.right a = Part.some (Nat.unpair a).2 from rfl,
    show (Part.some (Nat.unpair a).2 >>= eval (toPFun X) OracleCode.oracle)
      = eval (toPFun X) OracleCode.oracle (Nat.unpair a).2 from Part.bind_some _ _,
    eval_oracle, toPFun_eq_bitg]

/-- A witness pair exists for `Y_c` at the halting stage (from `hd` + agreement). -/
theorem hwp_yc (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ) (h : conv X c)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    ∃ p, witPair e n₀ (yc e n₀ X c) (hStage X c) p = true := by
  obtain ⟨s, hs⟩ := wit_spec e n₀ X (hStage X c) (hd _)
  refine ⟨Nat.pair (Encodable.encode (wit e n₀ X (hStage X c))) s, ?_⟩
  rw [witPair_yc e n₀ X c _ h]
  simp only [witPair, Nat.unpair_pair, Encodable.encodek, Option.getD_some]; exact hs

/-- **The recovery code recovers `X` from `Y_c`.** -/
theorem eval_cRecCode (e n₀ : ℕ) (X : ℕ → Bool) (c : ℕ)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) (m : ℕ) :
    eval (toPFun (yc e n₀ X c)) (cRecCode e n₀) (Nat.pair c m) = Part.some (bitg X m) := by
  have key : eval (toPFun (yc e n₀ X c)) (cRecCode e n₀) (Nat.pair c m)
      = Part.some (recFn e n₀ (yc e n₀ X c) c m) := by
    have hpair : eval (toPFun (yc e n₀ X c)) (.pair idCode cHalted) (Nat.pair c m)
        = Part.some (Nat.pair (Nat.pair c m) (bif haltedB (yc e n₀ X c) c m then 1 else 0)) := by
      rw [eval_pair_eq, eval_idCode, eval_cHalted]; simp only [Part.map_some, Part.bind_some]
    rw [cRecCode, eval_comp, hpair,
      show (Part.some (Nat.pair (Nat.pair c m) (bif haltedB (yc e n₀ X c) c m then 1 else 0))
          >>= eval (toPFun (yc e n₀ X c)) (.prec cBase (cSpl' e n₀)))
        = eval (toPFun (yc e n₀ X c)) (.prec cBase (cSpl' e n₀))
            (Nat.pair (Nat.pair c m) (bif haltedB (yc e n₀ X c) c m then 1 else 0))
        from Part.bind_some _ _, eval_prec_pair]
    rw [recFn]
    by_cases hh : haltedB (yc e n₀ X c) c m = true
    · have hconvX : conv X c := by
        by_contra hnc
        rw [funext (yc_eq_of_not_conv e n₀ X c hnc)] at hh
        exact hnc ⟨m, hh⟩
      rw [hh, nat_rec_bif_true, eval_cBase, Nat.unpair_pair,
        show (Part.some (bitg (yc e n₀ X c) m) >>= fun i =>
            eval (toPFun (yc e n₀ X c)) (cSpl' e n₀) (Nat.pair (Nat.pair c m) (Nat.pair 0 i)))
          = eval (toPFun (yc e n₀ X c)) (cSpl' e n₀)
              (Nat.pair (Nat.pair c m) (Nat.pair 0 (bitg (yc e n₀ X c) m))) from Part.bind_some _ _,
        cSpl', eval_comp, eval_left_app,
        show (Part.some (Nat.pair c m) >>= eval (toPFun (yc e n₀ X c)) (cSpl e n₀))
          = eval (toPFun (yc e n₀ X c)) (cSpl e n₀) (Nat.pair c m) from Part.bind_some _ _,
        eval_cSpl e n₀ (yc e n₀ X c) c m (conv_yc e n₀ X c hconvX)
          (by rw [hStage_yc e n₀ X c hconvX]; exact hwp_yc e n₀ X c hconvX hd),
        Bool.cond_true]
    · rw [Bool.not_eq_true] at hh
      rw [hh, nat_rec_bif_false, eval_cBase, Nat.unpair_pair, Bool.cond_false]
  rw [key, recFn_yc]

/-- **The backward s-m-n reduction**: a computable index map `s` with
`Φ_{s c}^{Y_c} = X`. -/
theorem yc_backward_code (e n₀ : ℕ) (X : ℕ → Bool)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    ∃ s : ℕ → ℕ, Computable s ∧
      ∀ c, eval (toPFun (yc e n₀ X c)) (ofNatCode (s c)) = toPFun X := by
  refine ⟨fun c => curryEnc (encodeCode (cRecCode e n₀)) c, ?_, fun c => ?_⟩
  · exact Primrec.to_comp (curryEnc_prim.comp (Primrec.const _) Primrec.id)
  · funext m
    show eval (toPFun (yc e n₀ X c)) (ofNatCode (curryEnc (encodeCode (cRecCode e n₀)) c)) m
      = toPFun X m
    rw [show curryEnc (encodeCode (cRecCode e n₀)) c = encodeCode (curry (cRecCode e n₀) c) from
        (encodeCode_curry (cRecCode e n₀) c).symm, ofNatCode_encodeCode, eval_curry,
      eval_cRecCode e n₀ X c hd, toPFun_eq_bitg]

/-- **`HasCodingFamily` is discharged.** -/
theorem hasCodingFamily (e n₀ : ℕ) (X : ℕ → Bool)
    (hnp : ∀ ℓ, ¬ haltsOn (graphOf (bitg X) ℓ) e n₀)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀) :
    HasCodingFamily e X n₀ := by
  obtain ⟨r, hr, hrspec⟩ := yc_forward e n₀ X hd
  obtain ⟨s, hs, hsspec⟩ := yc_backward_code e n₀ X hd
  refine ⟨r, s, hr, hs, fun c => ⟨yc e n₀ X c, ⟨hrspec c, hsspec c⟩, ?_⟩⟩
  exact marker_property e n₀ X c hnp hd

#print axioms hasCodingFamily

/-! ### Lachlan's discontinuous case, complete (coding family discharged) -/

/-- **Lachlan's discontinuous case, complete** (modulo Bard's Lemma 3.8): a
computably-uniformly-invariant r.e. operator `W` (index `e`) that is
*discontinuous* at `X` — no prefix of `X` halts `W` at the marker `n₀` (`hnp`),
but every prefix has a `0/1` extension that does (`hd`) — satisfies `Wˣ ≡ᵀ X′`.
The coding-real family is now *built*, not assumed: `hasCodingFamily` supplies it
from the discontinuity data, and `discontinuous_equiv_jump` reads off the jump. -/
theorem discontinuous_case_complete (e n₀ : ℕ) (X : ℕ → Bool)
    (hnp : ∀ ℓ, ¬ haltsOn (graphOf (bitg X) ℓ) e n₀)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀)
    (hu : Martin.ComputablyUniformlyTuringInvariant (reReal e)) :
    reReal e X ≡ₜ Cantor.jump X :=
  discontinuous_equiv_jump e X n₀ hu (hasCodingFamily e n₀ X hnp hd)

/-- **No operator solution to Post's problem, complete** (modulo Bard 3.8): for a
computably-uniform r.e. operator that is discontinuous at a high `X` (`0/1`
discontinuity at `n₀`), `Wˣ` is *never* strictly between `X` and `X′` — it is
Turing-equivalent to `X′`.  This is exactly Lachlan's theorem's payoff, with the
coding construction fully formalized. -/
theorem no_operator_post_solution_complete (e n₀ : ℕ) (X : ℕ → Bool)
    (hnp : ∀ ℓ, ¬ haltsOn (graphOf (bitg X) ℓ) e n₀)
    (hd : ∀ t, ∃ w : List Bool, haltsOn (graphOf (bitg X) t ++ w.map bbit) e n₀)
    (hu : Martin.ComputablyUniformlyTuringInvariant (reReal e)) :
    ¬ (X <ₜ reReal e X ∧ reReal e X <ₜ Cantor.jump X) := by
  rintro ⟨hlo, hhi⟩
  exact hhi.2 (discontinuous_case_complete e n₀ X hnp hd hu).2

#print axioms discontinuous_case_complete
#print axioms no_operator_post_solution_complete

end Coding
end OracleCode
