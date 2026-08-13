/-
The full Shoenfield Limit Lemma (relativized).

A total function `f` is computable from `X′` iff it has an `X`-computable
stage approximation converging pointwise:

  `f ≤ᵀ X′  ↔  ∃ g (X-computable) ∀ n ∃ s₀ ∀ s ≥ s₀, g n s = f n`.

The `←` direction is `recursiveIn_jump_of_limit` (`LimitLemma.lean`); the `→`
direction (`recursiveIn_of_jumpApprox`) is proved here by running the
reduction under the `X`-computable stage approximation of `X′`'s graph
(`JumpApprox.lean`), assembled via the reusable table-builder
`exists_tableEnc`.  The characterization is `limit_lemma`.
-/
import MartinsConjecture.JumpApprox

open scoped Computability
open OracleCode Cantor

attribute [local instance] Classical.propDecidable

namespace OracleCode

/-- Append the value `(unpair p).2` to the decoded list `(unpair p).1`. -/
private def concatE : ℕ → ℕ := fun p => Encodable.encode
  (((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD []) ++ [(Nat.unpair p).2])

private theorem concatE_prim : Nat.Primrec concatE :=
  Primrec.nat_iff.mp (Primrec.encode.comp (Primrec.list_concat.comp
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const ([] : List ℕ)))
    (Primrec.snd.comp Primrec.unpair)))

private theorem concatE_spec (l : List ℕ) (v : ℕ) :
    concatE (Nat.pair (Encodable.encode l) v) = Encodable.encode (l ++ [v]) := by
  rw [concatE]; simp [Nat.unpair_pair, Encodable.encodek]

/-- `tacc b s c` builds `encode [b 0 s,…,b (c-1) s]`. -/
private def tacc (b : ℕ → ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => Encodable.encode ([] : List ℕ)
  | c + 1 => concatE (Nat.pair (tacc b s c) (b c s))

private theorem tacc_spec (b : ℕ → ℕ → ℕ) (s : ℕ) :
    ∀ c, tacc b s c = Encodable.encode ((List.range c).map (fun m => b m s))
  | 0 => rfl
  | c + 1 => by
    rw [tacc, tacc_spec b s c, concatE_spec, List.range_succ, List.map_append]; rfl

/-- **Reusable table-builder.**  If `b` is `O`-computable, then
`s ↦ encode [b 0 s, …, b (s-1) s]` is `O`-computable. -/
theorem exists_tableEnc {O : ℕ →. ℕ} {b : ℕ → ℕ → ℕ}
    (hb : Nat.RecursiveIn {O}
      (fun w : ℕ => ((b (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ))) :
    Nat.RecursiveIn {O}
      (fun s : ℕ =>
        ((Encodable.encode ((List.range s).map (fun m => b m s)) : ℕ) : Part ℕ)) := by
  -- step function `q = pair a (pair y i)` ↦ append `b y a` to acc `i`.
  set step : ℕ →. ℕ := fun q =>
    (Nat.pair <$> ((q : ℕ) : Part ℕ) <*>
      ((b (Nat.unpair (Nat.unpair q).2).1 (Nat.unpair q).1 : ℕ) : Part ℕ))
    >>= fun w : ℕ =>
      ((concatE (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2
        (Nat.unpair w).2) : ℕ) : Part ℕ) with hstepdef
  have hbq : Nat.RecursiveIn {O} (fun q : ℕ =>
      ((b (Nat.unpair (Nat.unpair q).2).1 (Nat.unpair q).1 : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp hb (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.fst.comp Primrec.unpair))))).of_eq fun q => by
      simp [Nat.unpair_pair, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hcombP : Nat.Primrec fun w =>
      concatE (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2
        (Nat.unpair w).2) :=
    concatE_prim.comp (Primrec.nat_iff.mp (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
      (Primrec.snd.comp Primrec.unpair)))
  have hstep : Nat.RecursiveIn {O} step :=
    Nat.RecursiveIn.comp hcombP.recursiveIn
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hbq)
  set base : ℕ →. ℕ := fun _ => ((Encodable.encode ([] : List ℕ) : ℕ) : Part ℕ)
    with hbasedef
  have hbase : Nat.RecursiveIn {O} base :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec.const (Encodable.encode ([] : List ℕ))))
  -- Value of the accumulator recursion.
  have key : ∀ a c : ℕ,
      (Nat.rec (motive := fun _ => Part ℕ) (base a)
        (fun y IH => IH >>= fun i => step (Nat.pair a (Nat.pair y i))) c)
      = Part.some (tacc b a c) := by
    intro a c
    induction c with
    | zero => rfl
    | succ c ih =>
      show (Nat.rec (motive := fun _ => Part ℕ) _ _ c) >>= _ = _
      rw [ih]
      simp only [Part.bind_eq_bind, Part.bind_some]
      rw [hstepdef, tacc]
      simp only [Part.coe_some, Nat.unpair_pair, Seq.seq, Part.map_eq_map,
        Part.map_some, Part.bind_eq_bind, Part.bind_some]
  -- Packed version (defeq to the `prec` derivation).
  have hpacked : Nat.RecursiveIn {O}
      (fun p : ℕ => Part.some (tacc b (Nat.unpair p).1 (Nat.unpair p).2)) :=
    (Nat.RecursiveIn.prec hbase hstep).of_eq fun p => key (Nat.unpair p).1 (Nat.unpair p).2
  -- Evaluate at `pair s s`.
  refine (Nat.RecursiveIn.comp hpacked
    ((Primrec.nat_iff.mp (Primrec₂.natPair.comp Primrec.id Primrec.id)).recursiveIn)).of_eq
    fun s => ?_
  simp only [id_eq, Part.coe_some, Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  rw [tacc_spec]

/-! ### The `→` direction and the full characterization -/

/-- Running a reduction `c` (with oracle `X′`) under the stage-`s`
approximation of `X′`'s graph, for `s` steps. -/
private def limApprox (X : ℕ → Bool) (c : OracleCode) (n s : ℕ) : ℕ :=
  (evaln s ((List.range s).map (fun m => jumpApproxN X m s)) c n).getD 0

/-- **The `→` direction of the limit lemma.**  If `f` (total) is computable
from `X′`, it has an `X`-computable stage approximation converging pointwise. -/
theorem recursiveIn_of_jumpApprox {X : ℕ → Bool} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn {toPFun (Cantor.jump X)} (fun n : ℕ => ((f n : ℕ) : Part ℕ))) :
    ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = f n := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn hf
  refine ⟨limApprox X c, ?_, ?_⟩
  · -- X-computability: build the approximated-oracle table, then run `evaln`.
    have htable : Nat.RecursiveIn {toPFun X}
        (fun s : ℕ =>
          ((Encodable.encode ((List.range s).map (fun m => jumpApproxN X m s)) : ℕ)
            : Part ℕ)) :=
      exists_tableEnc (jumpApproxN_recursiveIn X)
    set postF : ℕ → ℕ := fun z =>
      (evaln (Nat.unpair (Nat.unpair z).2).2
        ((Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD [])
        c (Nat.unpair (Nat.unpair z).2).1).getD 0 with hpostF
    have hpostP : Nat.Primrec postF := by
      rw [hpostF]
      refine Primrec.nat_iff.mp ?_
      have hev : Primrec fun z : ℕ =>
          evaln (Nat.unpair (Nat.unpair z).2).2
            ((Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD [])
            c (Nat.unpair (Nat.unpair z).2).1 := by
        have hg : Primrec fun z : ℕ =>
            ((((Nat.unpair (Nat.unpair z).2).2,
              (Encodable.decode (α := List ℕ) (Nat.unpair z).1).getD []),
              c), (Nat.unpair (Nat.unpair z).2).1) := by
          refine Primrec.pair (Primrec.pair (Primrec.pair ?_ ?_) (Primrec.const c)) ?_
          · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
          · exact Primrec.option_getD.comp
              (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
              (Primrec.const ([] : List ℕ))
          · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
        exact evaln_prim.comp hg
      exact Primrec.option_getD.comp hev (Primrec.const 0)
    -- pair the table encoding (at s) with (n, s), then post-process.
    have hpair : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
        Nat.pair <$>
          ((((Nat.unpair w).2 : ℕ) : Part ℕ) >>= fun s =>
            ((Encodable.encode ((List.range s).map (fun m => jumpApproxN X m s)) : ℕ)
              : Part ℕ))
          <*> ((w : ℕ) : Part ℕ)) :=
      Nat.RecursiveIn.pair
        (Nat.RecursiveIn.comp htable
          (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair))))
        ((Primrec.nat_iff.mp Primrec.id).recursiveIn)
    have hF := Nat.RecursiveIn.comp hpostP.recursiveIn hpair
    refine hF.of_eq fun w => ?_
    simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Seq.seq,
      Part.map_eq_map, Part.map_some, Nat.unpair_pair]
    rw [hpostF]
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some, limApprox]
  · -- Convergence.
    intro n
    -- f n = eval (jump X) c n converges, captured by `evaln` at some stage `k`.
    have hmem : f n ∈ eval (toPFun (Cantor.jump X)) c n := by
      rw [hc]; exact Part.mem_some_iff.mpr rfl
    rw [toPFun_jump] at hmem
    -- Replace the jump oracle by its bit-graph total function.
    have hbit : ∀ i, jumpFn (toPFun X) i = Part.some (bitg (jump X) i) := by
      intro i
      rw [← toPFun_jump]; rfl
    obtain ⟨k, hk⟩ := evaln_complete hbit hmem
    -- Each jump bit `m < k` is correctly approximated for large `s`; take the max.
    have hbits : ∀ m, m < k → ∃ s₀, ∀ s, s₀ ≤ s → jumpApproxN X m s = bitg (jump X) m :=
      fun m _ => jumpApproxN_limit X m
    choose sb hsb using hbits
    set S := max k ((Finset.range k).sup (fun m => if h : m < k then sb m h else 0)) with hS
    refine ⟨S, fun s hs => ?_⟩
    rw [limApprox]
    have hsbound : ∀ i, (hi : i < k) → sb i hi ≤ S := by
      intro i hi
      rw [hS]
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans (le_of_eq (dif_pos hi).symm)
        (Finset.le_sup (f := fun m => if h : m < k then sb m h else 0)
          (Finset.mem_range.mpr hi))
    -- The approximated table agrees with `graphOf (bitg (jump X)) k` on the first `k`.
    have hagree : graphOf (bitg (jump X)) k
        <+: (List.range s).map (fun m => jumpApproxN X m s) := by
      rw [show graphOf (bitg (jump X)) k
        = List.take k ((List.range s).map (fun m => jumpApproxN X m s)) from ?_]
      · exact List.take_prefix k _
      · apply List.ext_getElem
        · simp only [graphOf, List.length_map, List.length_range, List.length_take]
          omega
        · intro i h1 h2
          simp only [graphOf, List.length_map, List.length_range] at h1
          simp only [graphOf, List.getElem_take, List.getElem_map, List.getElem_range]
          exact (hsb i h1 s (le_trans (hsbound i h1) hs)).symm
    -- Monotonicity of `evaln` in fuel and table gives the answer at stage `s`.
    have : evaln s ((List.range s).map (fun m => jumpApproxN X m s)) c n = some (f n) :=
      evaln_mono (le_trans (le_max_left _ _) hs) hagree hk
    rw [this, Option.getD_some]

/-- **The Shoenfield Limit Lemma** (relativized): a total function is
computable from `X′` iff it has an `X`-computable stage approximation
converging pointwise. -/
theorem limit_lemma (X : ℕ → Bool) (f : ℕ → ℕ) :
    Nat.RecursiveIn {toPFun (Cantor.jump X)} (fun n : ℕ => ((f n : ℕ) : Part ℕ)) ↔
    ∃ g : ℕ → ℕ → ℕ,
      Nat.RecursiveIn {toPFun X}
        (fun w : ℕ => ((g (Nat.unpair w).1 (Nat.unpair w).2 : ℕ) : Part ℕ)) ∧
      ∀ n, ∃ s₀, ∀ s, s₀ ≤ s → g n s = f n := by
  constructor
  · exact recursiveIn_of_jumpApprox
  · rintro ⟨g, hg, hlim⟩
    exact recursiveIn_jump_of_limit hg hlim

#print axioms exists_tableEnc
#print axioms recursiveIn_of_jumpApprox
#print axioms limit_lemma

end OracleCode
