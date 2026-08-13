/-
The jump is limit-computable from the oracle (Δ⁰₂-in-`X`).

`jumpApproxN X m s` runs machine `m` on input `m` with the length-`s` prefix
of `X`'s graph for `s` steps, returning `1` if it halts and `0` otherwise.
This approximation is:

* **`jumpApproxN_recursiveIn`** — jointly `X`-computable in `(m, s)`;
* **`jumpApproxN_mono`** — monotone in the stage `s`;
* **`jumpApproxN_limit`** — convergent to the `m`-th bit of the jump.

Consequently the jump has an `X`-computable stage approximation converging
pointwise to it (`jump_limitApprox`) — one half of the Shoenfield limit
lemma / Post's theorem, and the companion of `recursiveIn_jump_of_limit`.
-/
import MartinsConjecture.RecursionTheorem

open scoped Computability
open OracleCode Cantor

attribute [local instance] Classical.propDecidable

namespace OracleCode

variable {X : ℕ → Bool}

/-- Stage-`s` approximation to the `m`-th bit of `X′`. -/
def jumpApproxN (X : ℕ → Bool) (m s : ℕ) : ℕ :=
  if (evaln s (graphOf (bitg X) s) (ofNatCode m) m).isSome then 1 else 0

/-- The approximation is jointly `X`-computable in `(m, s)`
(input packed as `pair m s`). -/
theorem jumpApproxN_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X}
      (fun w : ℕ => ((jumpApproxN X (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) := by
  -- Post-processing function on `pair Le (pair m s)`:
  -- decode `Le` to the graph list, run `evaln`, test `isSome`.
  set post : ℕ → ℕ := fun z =>
    cond (evaln (Nat.unpair (Nat.unpair z).2).2
        ((Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD [])
        (ofNatCode (Nat.unpair (Nat.unpair z).2).1)
        (Nat.unpair (Nat.unpair z).2).1).isSome 1 0 with hpost
  have hpostP : Nat.Primrec post := by
    rw [hpost]
    refine Primrec.nat_iff.mp ?_
    have hev : Primrec fun z : ℕ =>
        evaln (Nat.unpair (Nat.unpair z).2).2
          ((Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD [])
          (ofNatCode (Nat.unpair (Nat.unpair z).2).1)
          (Nat.unpair (Nat.unpair z).2).1 := by
      have hg : Primrec fun z : ℕ =>
          ((((Nat.unpair (Nat.unpair z).2).2,
            (Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD []),
            ofNatCode (Nat.unpair (Nat.unpair z).2).1),
            (Nat.unpair (Nat.unpair z).2).1) := by
        refine Primrec.pair (Primrec.pair (Primrec.pair ?_ ?_) ?_) ?_
        · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
        · exact Primrec.option_getD.comp
            (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
            (Primrec.const ([] : List ℕ))
        · exact (Primrec.ofNat OracleCode).comp
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
      exact evaln_prim.comp hg
    exact Primrec.cond (Primrec.option_isSome.comp hev)
      (Primrec.const 1) (Primrec.const 0)
  -- Pair the oracle-graph-encoding with `(m, s)`, then post-process.
  have hgraph : Nat.RecursiveIn {toPFun X}
      (fun w : ℕ => (((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X) :=
    Nat.RecursiveIn.comp (graphEnc_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))
  have hid : Nat.RecursiveIn {toPFun X} (fun w : ℕ => ((w : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
      Nat.pair <$> ((((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X) <*>
        ((w : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.pair hgraph hid
  have hcomp : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
      (Nat.pair <$> ((((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X) <*>
        ((w : ℕ) : Part ℕ))
      >>= fun z : ℕ => ((post z : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hpostP.recursiveIn hpair
  refine hcomp.of_eq fun w => ?_
  -- value: the graph encodes to `encode (graphOf (bitg X) s)`, post decodes it.
  simp only [Part.coe_some, Part.bind_eq_bind]
  rw [show (Part.some (Nat.unpair w).2).bind (graphEnc X)
    = graphEnc X (Nat.unpair w).2 from Part.bind_some _ _]
  rw [show graphEnc X (Nat.unpair w).2
    = Part.some (Encodable.encode (graphOf (bitg X) (Nat.unpair w).2)) from rfl]
  simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_some]
  rw [hpost]
  simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some, jumpApproxN]
  by_cases hd : (evaln (Nat.unpair w).2 (graphOf (bitg X) (Nat.unpair w).2)
      (ofNatCode (Nat.unpair w).1) (Nat.unpair w).1).isSome <;>
    simp [hd]

/-- The approximation is monotone in the stage. -/
theorem jumpApproxN_mono (X : ℕ → Bool) (m : ℕ) {s s' : ℕ} (h : s ≤ s') :
    jumpApproxN X m s ≤ jumpApproxN X m s' := by
  rw [jumpApproxN, jumpApproxN]
  by_cases hs : (evaln s (graphOf (bitg X) s) (ofNatCode m) m).isSome
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have : evaln s' (graphOf (bitg X) s') (ofNatCode m) m = some v :=
      evaln_mono h (graphOf_prefix h) hv
    rw [if_pos hs, if_pos (by rw [this]; rfl)]
  · rw [if_neg hs]
    exact Nat.zero_le _

/-- The approximation converges to the `m`-th bit of the jump. -/
theorem jumpApproxN_limit (X : ℕ → Bool) (m : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → jumpApproxN X m s = bitg (jump X) m := by
  have hbit : bitg (jump X) m = if jumpP (toPFun X) m then 1 else 0 := by
    rw [bitg, jump]
    by_cases hj : jumpP (toPFun X) m <;> simp [hj]
  have hjumpApprox_pos : jumpApproxN X m = fun s =>
      if (evaln s (graphOf (bitg X) s) (ofNatCode m) m).isSome then 1 else 0 := rfl
  by_cases hj : jumpP (toPFun X) m
  · -- machine halts; some stage detects it, then monotone
    have hdom : (eval (toPFun X) (ofNatCode m) m).Dom := hj
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := evaln_complete (toPFun_eq_bitg X) hv
    refine ⟨k, fun s hs => ?_⟩
    rw [jumpApproxN, hbit, if_pos hj]
    have : evaln s (graphOf (bitg X) s) (ofNatCode m) m = some v :=
      evaln_mono hs (graphOf_prefix hs) hk
    rw [if_pos (by rw [this]; rfl)]
  · -- machine diverges; approximation is always 0
    refine ⟨0, fun s _ => ?_⟩
    rw [jumpApproxN, hbit, if_neg hj]
    rw [if_neg ?_]
    intro hsome
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    exact hj (Part.dom_iff_mem.mpr ⟨v, evaln_sound (graphOf_sound (toPFun_eq_bitg X) s) hv⟩)

/-- **The jump is limit-computable from the oracle** (Δ⁰₂-in-`X`): there is
an `X`-computable stage approximation `g` converging pointwise to the bits of
`X′`.  Companion to `recursiveIn_jump_of_limit`. -/
theorem jump_limitApprox (X : ℕ → Bool) :
    ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      (∀ m, ∃ s₀, ∀ s, s₀ ≤ s → g m s = bitg (jump X) m) ∧
      (∀ m s s', s ≤ s' → g m s ≤ g m s') :=
  ⟨jumpApproxN X, jumpApproxN_recursiveIn X, jumpApproxN_limit X,
    fun m s s' h => jumpApproxN_mono X m h⟩

#print axioms jumpApproxN_recursiveIn
#print axioms jumpApproxN_limit
#print axioms jump_limitApprox

end OracleCode
