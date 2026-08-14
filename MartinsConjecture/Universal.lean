/-
The universal machine, part 3: universality and the recursion theorem.

* `graphEnc_recursiveIn` — an oracle can enumerate its own graph prefixes
  (primitive recursion with oracle queries);
* **`eval_universal`** — the enumeration theorem with universality: the
  two-argument function `(e, n) ↦ eval O (ofNatCode e) n` is itself
  recursive in `O` (for total 0/1 oracles `O = toPFun X`): dovetail
  `evaln` over stages using the oracle's own graph;
* **`exists_fixedPoint`** — Kleene's second recursion theorem, relativized:
  for any computable transformation `f` of code numbers there is `e` with
  `eval O (ofNatCode (f e)) = eval O (ofNatCode e)`.  In this numbering the
  classical diagonal is simply `diag x = curryEnc x x`.

This closes the "single missing artifact" identified in ATTACK.md.
-/
import MartinsConjecture.EvalnPrim
import MartinsConjecture.UniformJump
import MartinsConjecture.CantorPoints

open scoped Computability
open OracleCode Cantor

namespace OracleCode

/-- The bit-graph of `X` as a total function. -/
def bitg (X : ℕ → Bool) : ℕ → ℕ := fun i => cond (X i) 1 0

theorem toPFun_eq_bitg (X : ℕ → Bool) (i : ℕ) :
    toPFun X i = Part.some (bitg X i) := rfl

/-- The `0/1` numeral of a Boolean (the oracle bit).  Defined here — early —
so the `0/1`-extension machinery (`ExtHalting`, `ContinuousCase`) can quantify
over Boolean extensions mapped into oracle tables. -/
def bbit (b : Bool) : ℕ := bif b then 1 else 0

theorem bbit_prim : Primrec bbit :=
  Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)

theorem bitg_eq_bbit (Y : ℕ → Bool) (m : ℕ) : bitg Y m = bbit (Y m) := rfl

/-- A `bitg` graph prefix is a `0/1` table: `graphOf (bitg X) k` is the
`bbit`-image of `X`'s first `k` Boolean values.  This exposes graph prefixes as
genuine Cantor-space (Boolean) prefixes for the extension-halting analysis. -/
theorem graphOf_bitg_eq_map (X : ℕ → Bool) (k : ℕ) :
    graphOf (bitg X) k = ((List.range k).map X).map bbit := by
  rw [graphOf, List.map_map]
  rfl

/-- A longer `bitg` graph prefix is the shorter one followed by a `bbit`-mapped
Boolean tail: `graphOf (bitg X) ℓ'` extends `graphOf (bitg X) ℓ` by a genuine
`0/1` (Boolean) block whenever `ℓ ≤ ℓ'`.  This is what lets the extension-halting
analysis stay inside Cantor space. -/
theorem graphOf_bitg_prefix_bool {X : ℕ → Bool} {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    ∃ τ : List Bool, graphOf (bitg X) ℓ' = graphOf (bitg X) ℓ ++ τ.map bbit := by
  induction ℓ' with
  | zero => rw [Nat.le_zero.mp h]; exact ⟨[], by rw [List.map_nil, List.append_nil]⟩
  | succ k ih =>
    by_cases hk : ℓ = k + 1
    · exact ⟨[], by rw [hk, List.map_nil, List.append_nil]⟩
    · obtain ⟨τ, hτ⟩ := ih (by omega)
      refine ⟨τ ++ [X k], ?_⟩
      have hstep : graphOf (bitg X) (k + 1) = graphOf (bitg X) k ++ [bbit (X k)] := by
        rw [graphOf, graphOf, List.range_succ, List.map_append, List.map_singleton, bitg_eq_bbit]
      rw [hstep, hτ, List.map_append, List.map_singleton, List.append_assoc]

/-- Encoded graph prefixes of the oracle. -/
def graphEnc (X : ℕ → Bool) : ℕ → Part ℕ :=
  fun k => Part.some (Encodable.encode (graphOf (bitg X) k))

/-- Appending one value to an encoded list, primitively. -/
private def concatE : ℕ → ℕ :=
  fun p => Encodable.encode
    (((Encodable.decode (α := List ℕ) (Nat.unpair p).1).getD []) ++ [(Nat.unpair p).2])

private theorem concatE_prim : Primrec concatE :=
  Primrec.encode.comp (Primrec.list_concat.comp
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const ([] : List ℕ)))
    (Primrec.snd.comp Primrec.unpair))

private theorem concatE_encode (l : List ℕ) (b : ℕ) :
    concatE (Nat.pair (Encodable.encode l) b) = Encodable.encode (l ++ [b]) := by
  rw [concatE]
  simp [Nat.unpair_pair, Encodable.encodek]

/-- An oracle can enumerate its own graph prefixes. -/
theorem graphEnc_recursiveIn (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X} (graphEnc X) := by
  -- combine map on `w = pair q b` with `q = pair a (pair y i)`:
  -- output `concatE (pair i b)`.
  have hcombP : Nat.Primrec fun w =>
      concatE (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2
        (Nat.unpair w).2) := by
    refine Primrec.nat_iff.mp (concatE_prim.comp ?_)
    exact Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.fst.comp Primrec.unpair)))))
      (Primrec.snd.comp Primrec.unpair)
  have hy : Nat.RecursiveIn {toPFun X}
      (fun q : ℕ => (((Nat.unpair (Nat.unpair q).2).1 : ℕ) : Part ℕ) >>= toPFun X) :=
    Nat.RecursiveIn.comp (.oracle _ rfl)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hP : Nat.RecursiveIn {toPFun X} (fun q : ℕ =>
      Nat.pair <$> ((q : ℕ) : Part ℕ) <*>
        ((((Nat.unpair (Nat.unpair q).2).1 : ℕ) : Part ℕ) >>= toPFun X)) :=
    Nat.RecursiveIn.pair hid hy
  have hstep : Nat.RecursiveIn {toPFun X} (fun q : ℕ =>
      (Nat.pair <$> ((q : ℕ) : Part ℕ) <*>
        ((((Nat.unpair (Nat.unpair q).2).1 : ℕ) : Part ℕ) >>= toPFun X))
      >>= fun w : ℕ =>
        ((concatE (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2
          (Nat.unpair w).2) : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hcombP.recursiveIn hP
  have hzero : Nat.RecursiveIn {toPFun X}
      (fun _ : ℕ => ((Encodable.encode ([] : List ℕ) : ℕ) : Part ℕ)) :=
    (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec.const (Encodable.encode ([] : List ℕ)))))
  have hprec := Nat.RecursiveIn.prec hzero hstep
  have hpair0 : Nat.RecursiveIn {toPFun X}
      (fun k : ℕ => ((Nat.pair 0 k : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)).recursiveIn
  have hF := Nat.RecursiveIn.comp hprec hpair0
  refine hF.of_eq fun k => ?_
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  -- induction on the recursion counter
  induction k with
  | zero => rfl
  | succ k ih =>
    show (Nat.rec (motive := fun _ => Part ℕ) _ _ k).bind _ = _
    rw [ih]
    rw [show graphEnc X k
      = Part.some (Encodable.encode (graphOf (bitg X) k)) from rfl, Part.bind_some]
    rw [show (Part.some k >>= toPFun X) = toPFun X k from Part.bind_some _ _]
    rw [show toPFun X k = Part.some (bitg X k) from rfl]
    simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind,
      Part.bind_some, Nat.unpair_pair]
    rw [concatE_encode]
    rw [show graphEnc X (k + 1)
      = Part.some (Encodable.encode (graphOf (bitg X) (k + 1))) from rfl]
    congr 2
    rw [graphOf, graphOf, List.range_succ, List.map_append]
    rfl

/-- Decoded `evaln`, as a primitive recursive function of raw numbers. -/
private def evalnD : ℕ → Option ℕ := fun v =>
  evaln (Nat.unpair (Nat.unpair v).1).2
    ((Encodable.decode (α := List ℕ) (Nat.unpair v).2).getD [])
    (ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
    (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2

private theorem evalnD_prim : Primrec evalnD := by
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

private theorem evalnD_eq (p k Le : ℕ) :
    evalnD (Nat.pair (Nat.pair p k) Le)
      = evaln k ((Encodable.decode (α := List ℕ) Le).getD [])
          (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2 := by
  rw [evalnD]
  simp [Nat.unpair_pair]

private theorem evalnD_graph (X : ℕ → Bool) (p k : ℕ) :
    evalnD (Nat.pair (Nat.pair p k) (Encodable.encode (graphOf (bitg X) k)))
      = evaln k (graphOf (bitg X) k) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2 := by
  rw [evalnD_eq]
  simp [Encodable.encodek]

/-- The stage test: `0` iff stage `k` already answers. -/
private def ts : ℕ → ℕ := fun v => cond (evalnD v).isSome 0 1

private theorem ts_prim : Primrec ts :=
  Primrec.cond (Primrec.option_isSome.comp evalnD_prim)
    (Primrec.const 0) (Primrec.const 1)

/-- **Universality**: relative to any total 0/1 oracle, the two-argument
evaluation function `(e, n) ↦ eval O (ofNatCode e) n` is recursive in the
oracle. -/
theorem eval_universal (X : ℕ → Bool) :
    Nat.RecursiveIn {toPFun X}
      (fun p : ℕ =>
        eval (toPFun X) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2) := by
  have hid : Nat.RecursiveIn {toPFun X} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hA : Nat.RecursiveIn {toPFun X}
      (fun w : ℕ => (((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X) :=
    Nat.RecursiveIn.comp (graphEnc_recursiveIn X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair)))
  have hB : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
      Nat.pair <$> ((w : ℕ) : Part ℕ) <*>
        ((((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X)) :=
    Nat.RecursiveIn.pair hid hA
  have hC : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
      (Nat.pair <$> ((w : ℕ) : Part ℕ) <*>
        ((((Nat.unpair w).2 : ℕ) : Part ℕ) >>= graphEnc X))
      >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp ts_prim)) hB
  have hR := Nat.RecursiveIn.rfind hC
  have hH : Nat.RecursiveIn {toPFun X} (fun p : ℕ =>
      (Nat.rfind fun k => (fun m => m = 0) <$>
        ((Nat.pair <$> ((Nat.pair p k : ℕ) : Part ℕ) <*>
          ((((Nat.unpair (Nat.pair p k)).2 : ℕ) : Part ℕ) >>= graphEnc X))
        >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ)))
      >>= fun km : ℕ =>
        Nat.pair <$> ((Nat.pair p km : ℕ) : Part ℕ) <*>
          ((((Nat.unpair (Nat.pair p km)).2 : ℕ) : Part ℕ) >>= graphEnc X)) := by
    -- pair the input with the found stage, then attach the graph at that stage
    have hpk : Nat.RecursiveIn {toPFun X} (fun v : ℕ =>
        Nat.pair <$> ((v : ℕ) : Part ℕ) <*>
          ((((Nat.unpair v).2 : ℕ) : Part ℕ) >>= graphEnc X)) :=
      Nat.RecursiveIn.pair hid hA
    have hpair : Nat.RecursiveIn {toPFun X} (fun p : ℕ =>
        Nat.pair <$> ((p : ℕ) : Part ℕ) <*>
          (Nat.rfind fun k => (fun m => m = 0) <$>
            ((Nat.pair <$> ((Nat.pair p k : ℕ) : Part ℕ) <*>
              ((((Nat.unpair (Nat.pair p k)).2 : ℕ) : Part ℕ) >>= graphEnc X))
            >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ)))) :=
      Nat.RecursiveIn.pair hid hR
    exact Nat.RecursiveIn.comp hpk hpair |>.of_eq fun p => by
      apply Part.ext
      intro y
      simp only [Part.coe_some, Part.bind_eq_bind, Seq.seq, Part.map_eq_map,
        Part.map_some, Part.bind_some, Part.mem_bind_iff, Part.mem_map_iff]
      constructor
      · rintro ⟨w, ⟨km, hkm, rfl⟩, hy⟩
        exact ⟨km, hkm, hy⟩
      · rintro ⟨km, hkm, hy⟩
        exact ⟨Nat.pair p km, ⟨km, hkm, rfl⟩, hy⟩
  set extv : ℕ → ℕ := fun v => (evalnD v).getD 0 with hextv
  have hextP : Primrec extv := by
    rw [hextv]
    exact Primrec.option_getD.comp evalnD_prim (Primrec.const 0)
  have hFinal := Nat.RecursiveIn.comp
    (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp hextP)) hH
  refine hFinal.of_eq fun p => ?_
  -- Value analysis.
  have hO : ∀ i, toPFun X i = Part.some (bitg X i) := toPFun_eq_bitg X
  have hLsound : ∀ k, ∀ i, (hi : i < (graphOf (bitg X) k).length) →
      toPFun X i = Part.some (graphOf (bitg X) k)[i] :=
    fun k => graphOf_sound hO k
  -- the inner test values
  have htest : ∀ k : ℕ,
      ((Nat.pair <$> ((Nat.pair p k : ℕ) : Part ℕ) <*>
        ((((Nat.unpair (Nat.pair p k)).2 : ℕ) : Part ℕ) >>= graphEnc X))
      >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ))
      = Part.some (ts (Nat.pair (Nat.pair p k)
          (Encodable.encode (graphOf (bitg X) k)))) := by
    intro k
    simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Seq.seq,
      Part.map_eq_map, Part.map_some, Nat.unpair_pair]
    rw [show graphEnc X k = Part.some (Encodable.encode (graphOf (bitg X) k)) from rfl]
    simp only [Part.bind_some, Part.map_some]
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain ⟨w, hw, hyv⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨km, hkm, hw2⟩ := Part.mem_bind_iff.mp hw
    -- decompose the pair-with-graph
    simp only [Part.coe_some, Part.bind_eq_bind, Seq.seq, Part.map_eq_map,
      Part.map_some, Part.bind_some, Nat.unpair_pair] at hw2
    rw [show graphEnc X km
      = Part.some (Encodable.encode (graphOf (bitg X) km)) from rfl] at hw2
    simp only [Part.bind_some, Part.map_some, Part.mem_some_iff] at hw2
    subst hw2
    obtain ⟨hts, -⟩ := Nat.mem_rfind.mp hkm
    rw [htest km] at hts
    simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff] at hts
    -- the test succeeded at km, so evaln answered
    have hsome : (evalnD (Nat.pair (Nat.pair p km)
        (Encodable.encode (graphOf (bitg X) km)))).isSome = true := by
      by_contra hns
      rw [ts] at hts
      simp only [Bool.not_eq_true] at hns
      rw [hns] at hts
      simp at hts
    obtain ⟨vm, hvm⟩ := Option.isSome_iff_exists.mp hsome
    -- extract and transport by soundness
    rw [Part.coe_some, Part.mem_some_iff] at hyv
    subst hyv
    rw [hextv]
    simp only [hvm, Option.getD_some]
    rw [evalnD_graph] at hvm
    exact evaln_sound (hLsound km) hvm
  · intro hy
    obtain ⟨k₀, hk₀⟩ := evaln_complete hO hy
    -- the search halts: some stage answers
    have htotal : ∀ k, ((Nat.pair <$> ((Nat.pair p k : ℕ) : Part ℕ) <*>
        ((((Nat.unpair (Nat.pair p k)).2 : ℕ) : Part ℕ) >>= graphEnc X))
        >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ)).Dom := by
      intro k
      rw [htest k]
      trivial
    have hdomR : (Nat.rfind fun k => (fun m => m = 0) <$>
        ((Nat.pair <$> ((Nat.pair p k : ℕ) : Part ℕ) <*>
          ((((Nat.unpair (Nat.pair p k)).2 : ℕ) : Part ℕ) >>= graphEnc X))
        >>= fun v : ℕ => ((ts v : ℕ) : Part ℕ))).Dom := by
      refine Nat.rfind_dom.mpr ⟨k₀, ?_, fun {m} _ => htotal m⟩
      rw [htest k₀]
      simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff]
      rw [ts, evalnD_graph, hk₀]
      rfl
    obtain ⟨km, hkm⟩ := Part.dom_iff_mem.mp hdomR
    -- the found stage answers with the right value
    obtain ⟨hts, -⟩ := Nat.mem_rfind.mp hkm
    rw [htest km] at hts
    simp only [Part.map_eq_map, Part.map_some, Part.mem_some_iff] at hts
    have hsome : (evalnD (Nat.pair (Nat.pair p km)
        (Encodable.encode (graphOf (bitg X) km)))).isSome = true := by
      by_contra hns
      rw [ts] at hts
      simp only [Bool.not_eq_true] at hns
      rw [hns] at hts
      simp at hts
    obtain ⟨vm, hvm⟩ := Option.isSome_iff_exists.mp hsome
    have hvy : vm = y := by
      have := evaln_sound (hLsound km) (by rw [← evalnD_graph (X := X)]; exact hvm)
      exact Part.mem_unique this hy
    refine Part.mem_bind_iff.mpr ⟨Nat.pair (Nat.pair p km)
      (Encodable.encode (graphOf (bitg X) km)), ?_, ?_⟩
    · refine Part.mem_bind_iff.mpr ⟨km, hkm, ?_⟩
      simp only [Part.coe_some, Part.bind_eq_bind, Seq.seq, Part.map_eq_map,
        Part.map_some, Part.bind_some, Nat.unpair_pair]
      rw [show graphEnc X km
        = Part.some (Encodable.encode (graphOf (bitg X) km)) from rfl]
      simp only [Part.bind_some, Part.map_some]
      exact Part.mem_some_iff.mpr rfl
    · rw [hextv]
      simp only [hvm, Option.getD_some]
      exact Part.mem_some_iff.mpr hvy.symm

/-- **Kleene's second recursion theorem, relativized**: any computable
transformation of code numbers has a fixed point relative to any (total 0/1)
oracle.  In this numbering the diagonal is `diag x = curryEnc x x`. -/
theorem exists_fixedPoint (X : ℕ → Bool) {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ e : ℕ, eval (toPFun X) (ofNatCode (f e)) = eval (toPFun X) (ofNatCode e) := by
  have hD : Nat.RecursiveIn {toPFun X} (fun w : ℕ =>
      (((Nat.pair (f (curryEnc (Nat.unpair w).1 (Nat.unpair w).1))
          (Nat.unpair w).2 : ℕ) : Part ℕ)) >>=
        fun p : ℕ =>
          eval (toPFun X) (ofNatCode (Nat.unpair p).1) (Nat.unpair p).2) :=
    Nat.RecursiveIn.comp (eval_universal X)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (Primrec₂.natPair.comp
          ((Primrec.nat_iff.mpr hf).comp
            (curryEnc_prim.comp (Primrec.fst.comp Primrec.unpair)
              (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair))))
  obtain ⟨cD, hcD⟩ := exists_code_of_recursiveIn hD
  refine ⟨curryEnc (encodeCode cD) (encodeCode cD), ?_⟩
  funext y
  have h1 : ofNatCode (curryEnc (encodeCode cD) (encodeCode cD))
      = curry cD (encodeCode cD) := by
    rw [show curryEnc (encodeCode cD) (encodeCode cD)
      = encodeCode (curry cD (encodeCode cD)) from rfl, ofNatCode_encodeCode]
  rw [h1, eval_curry, hcD]
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]

#print axioms eval_universal
#print axioms exists_fixedPoint

end OracleCode
