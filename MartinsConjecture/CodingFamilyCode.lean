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

end Coding
end OracleCode
