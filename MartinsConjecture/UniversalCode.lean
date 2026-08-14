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

end OracleCode
