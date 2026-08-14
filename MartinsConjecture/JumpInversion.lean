/-
The Friedberg jump-inversion theorem: every degree `≥ᵀ 0′` is a jump.

`∀ C, 0′ ≤ᵀ C → ∃ A, A′ ≡ᵀ C`.

Construction (finite extension, relative to `C`): build `A = ⋃ σ_e` where at
stage `e` we consult the extension-halting oracle (`0′`-decidable, hence
`C`-decidable) "does `Φ_e` halt on `e` under some extension of `σ_e`?"; if so we
append the least such extension (forcing `e ∈ A′`), otherwise nothing; then we
append one bit of `C`.  Then `A ≤ᵀ C`, `A′ ≤ᵀ C` (the jump is read off the
`C`-computable decisions), and `C ≤ᵀ A′` (decode by reconstructing the
construction from `A′`, using `A ≤ᵀ A′`).
-/
import MartinsConjecture.ContinuousCase

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- A `0/1` extension decoded from a `List Bool` code. -/
def boolExt (v : ℕ) : List ℕ :=
  ((Encodable.decode (α := List Bool) v).getD []).map (fun b => if b then 1 else 0)

theorem boolExt_le (v : ℕ) : ∀ x ∈ boolExt v, x ≤ 1 := by
  intro x hx
  rw [boolExt, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  cases b <;> simp

/-- The existence of a `0/1` halting extension witness for `σ`, machine `e`,
input `e`, phrased over encoded pairs `w = ⟪encode(τ : List Bool), s⟫`. -/
def jExists (σ : List ℕ) (e : ℕ) : Prop :=
  ∃ w, (evaln (Nat.unpair w).2
    (σ ++ boolExt (Nat.unpair w).1)
    (ofNatCode e) e).isSome = true

/-- The least `0/1` halting-extension for `σ` at stage `e` (empty if none). -/
noncomputable def jtau (σ : List ℕ) (e : ℕ) : List ℕ :=
  if h : jExists σ e then boolExt (Nat.unpair (Nat.find h)).1 else []

theorem jtau_le (σ : List ℕ) (e : ℕ) : ∀ x ∈ jtau σ e, x ≤ 1 := by
  rw [jtau]
  split
  · exact boolExt_le _
  · simp

/-- The stage-`e` string of the construction (relative to `C`). -/
noncomputable def jstr (C : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | e + 1 =>
    (if jExists (jstr C e) e then jstr C e ++ jtau (jstr C e) e else jstr C e)
      ++ [if C e then 1 else 0]

/-- The real produced by the construction: the `n`-th bit is read from stage
`n+1` (which is long enough). -/
noncomputable def jReal (C : ℕ → Bool) : ℕ → Bool :=
  fun n => (jstr C (n + 1)).getD n 0 = 1

/-! ### Length and prefix facts -/

/-- Each stage appends at least one bit. -/
theorem jstr_succ_prefix (C : ℕ → Bool) (e : ℕ) : jstr C e <+: jstr C (e + 1) := by
  rw [jstr]
  by_cases h : jExists (jstr C e) e
  · simp only [if_pos h]
    exact (List.prefix_append _ _).trans (List.prefix_append _ _)
  · simp only [if_neg h]
    exact List.prefix_append _ _

theorem jstr_mono (C : ℕ → Bool) {e e' : ℕ} (h : e ≤ e') : jstr C e <+: jstr C e' := by
  induction e' with
  | zero => rw [Nat.le_zero.mp h]
  | succ e' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h1 | h1
    · exact (ih (Nat.lt_succ_iff.mp h1)).trans (jstr_succ_prefix C e')
    · rw [h1]

theorem jstr_len_ge (C : ℕ → Bool) : ∀ e, e ≤ (jstr C e).length
  | 0 => Nat.zero_le _
  | e + 1 => by
    have h := jstr_len_ge C e
    have : (jstr C e).length < (jstr C (e + 1)).length := by
      rw [jstr]
      by_cases hh : jExists (jstr C e) e <;> simp [hh]
    omega

/-- All bits of the construction are `0/1`. -/
theorem jstr_bits_le (C : ℕ → Bool) : ∀ e, ∀ x ∈ jstr C e, x ≤ 1
  | 0 => by simp [jstr]
  | e + 1 => by
    rw [jstr]
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hh : jExists (jstr C e) e
      · rw [if_pos hh, List.mem_append] at hx
        rcases hx with hx | hx
        · exact jstr_bits_le C e x hx
        · exact jtau_le _ _ x hx
      · rw [if_neg hh] at hx
        exact jstr_bits_le C e x hx
    · rw [List.mem_singleton] at hx
      subst hx; split <;> simp

theorem prefix_getD {l l' : List ℕ} (h : l <+: l') {n : ℕ} (hn : n < l.length) :
    l'.getD n 0 = l.getD n 0 := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

/-- The construction's bit at `n` matches the real `jReal C`. -/
theorem jstr_getD_eq_bitg (C : ℕ → Bool) (e n : ℕ) (hn : n < (jstr C e).length) :
    (jstr C e).getD n 0 = bitg (jReal C) n := by
  have hble : (jstr C (n + 1)).getD n 0 ≤ 1 := by
    have hn1 : n < (jstr C (n + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self n) (jstr_len_ge C (n + 1))
    refine jstr_bits_le C (n + 1) _ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn1, Option.getD_some]
    exact List.getElem_mem _
  have hbitg : bitg (jReal C) n = (jstr C (n + 1)).getD n 0 := by
    rw [bitg, jReal]
    by_cases h1 : (jstr C (n + 1)).getD n 0 = 1
    · rw [h1]; rfl
    · have h0 : (jstr C (n + 1)).getD n 0 = 0 := by omega
      rw [h0]; rfl
  rw [hbitg]
  rcases le_total e (n + 1) with hle | hle
  · exact (prefix_getD (jstr_mono C hle) hn).symm
  · have hn1 : n < (jstr C (n + 1)).length :=
      lt_of_lt_of_le (Nat.lt_succ_self n) (jstr_len_ge C (n + 1))
    exact prefix_getD (jstr_mono C hle) hn1

/-- **Key**: the stage-`e` string is exactly the length-`|σ_e|` prefix table of
the real's bit-graph.  Hence `evaln`-soundness/completeness against `jstr C e`
transfer to genuine computations relative to `jReal C`. -/
theorem jstr_eq_graphOf (C : ℕ → Bool) (e : ℕ) :
    jstr C e = graphOf (bitg (jReal C)) (jstr C e).length := by
  apply List.ext_getElem (by simp [graphOf])
  intro i h1 h2
  rw [show (jstr C e)[i] = (jstr C e).getD i 0 from by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some],
    jstr_getD_eq_bitg C e i h1]
  simp only [graphOf, List.getElem_map, List.getElem_range]

theorem graphOf_split {g : ℕ → ℕ} {L ℓ : ℕ} (h : L ≤ ℓ) :
    graphOf g ℓ = graphOf g L ++ (List.range (ℓ - L)).map (fun j => g (L + j)) := by
  rw [graphOf, graphOf]
  conv_lhs => rw [show ℓ = L + (ℓ - L) from by omega]
  rw [List.range_add, List.map_append, List.map_map]
  simp [graphOf, Function.comp, Nat.add_comm]

/-- A bit of any prefix of a stage string equals the corresponding bit of the
real. -/
theorem prefix_getElem_bit (C : ℕ → Bool) {S : List ℕ} {m : ℕ} (hS : S <+: jstr C m)
    {i : ℕ} (hi : i < S.length) : S[i] = bitg (jReal C) i := by
  have hlen : i < (jstr C m).length := lt_of_lt_of_le hi hS.length_le
  have h1 : (jstr C m).getD i 0 = S.getD i 0 := prefix_getD hS hi
  have h3 : S.getD i 0 = S[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [← h3, ← h1, jstr_getD_eq_bitg C m i hlen]

/-- **The jump characterization** (claim 2's heart): `e ∈ (jReal C)′` iff `Φ_e`
halts on `e` under some extension of the stage-`e` string. -/
theorem dom_iff_jExists (C : ℕ → Bool) (e : ℕ) :
    (eval (toPFun (jReal C)) (ofNatCode e) e).Dom ↔ jExists (jstr C e) e := by
  constructor
  · intro hdom
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨ℓ, hℓ⟩ := evaln_complete (O := toPFun (jReal C)) (g := bitg (jReal C))
      (fun i => rfl) hv
    rcases le_total ℓ (jstr C e).length with hle | hle
    · refine ⟨Nat.pair (Encodable.encode ([] : List Bool)) ℓ, ?_⟩
      have hb : boolExt (Encodable.encode ([] : List Bool)) = [] := by
        simp [boolExt, Encodable.encodek]
      have hpre : graphOf (bitg (jReal C)) ℓ <+: jstr C e := by
        conv_rhs => rw [jstr_eq_graphOf C e]
        exact graphOf_prefix hle
      have hmono := evaln_mono (le_refl ℓ) hpre hℓ
      simp only [Nat.unpair_pair, hb, List.append_nil, hmono, Option.isSome_some]
    · set L := (jstr C e).length with hLdef
      refine ⟨Nat.pair (Encodable.encode
        ((List.range (ℓ - L)).map (fun j => jReal C (L + j)))) ℓ, ?_⟩
      simp only [Nat.unpair_pair]
      have hbe : boolExt (Encodable.encode
          ((List.range (ℓ - L)).map (fun j => jReal C (L + j))))
          = (List.range (ℓ - L)).map (fun j => bitg (jReal C) (L + j)) := by
        rw [boolExt, Encodable.encodek, Option.getD_some, List.map_map]
        apply List.map_congr_left
        intro j _
        simp only [Function.comp_apply, bitg]
        cases jReal C (L + j) <;> rfl
      have hjs : jstr C e = graphOf (bitg (jReal C)) L := by rw [hLdef]; exact jstr_eq_graphOf C e
      have hsplit : jstr C e ++
          (List.range (ℓ - L)).map (fun j => bitg (jReal C) (L + j)) = graphOf (bitg (jReal C)) ℓ := by
        rw [hjs, ← graphOf_split hle]
      simp only [hbe, hsplit, hℓ, Option.isSome_some]
  · intro h
    have hfind := Nat.find_spec h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hfind
    have hjtau : jstr C e ++ jtau (jstr C e) e
        = jstr C e ++ boolExt (Nat.unpair (Nat.find h)).1 := by rw [jtau, dif_pos h]
    have hvalid : ∀ i, (hi : i < (jstr C e ++ jtau (jstr C e) e).length) →
        toPFun (jReal C) i = Part.some ((jstr C e ++ jtau (jstr C e) e)[i]) := by
      intro i hi
      have hpre : jstr C e ++ jtau (jstr C e) e <+: jstr C (e + 1) := by
        rw [jstr, if_pos h]; exact List.prefix_append _ _
      rw [toPFun_eq_some_bitg, prefix_getElem_bit C hpre hi]
    refine Part.dom_iff_mem.mpr ⟨v, evaln_sound (k := (Nat.unpair (Nat.find h)).2) hvalid ?_⟩
    rw [hjtau]; exact hv

/-! ### `jExists` is `0′`-decidable -/

theorem boolExt_prim : Primrec boolExt := by
  have hd : Primrec (fun v : ℕ => (Encodable.decode (α := List Bool) v).getD []) :=
    Primrec.option_getD.comp (Primrec.decode (α := List Bool)) (Primrec.const ([] : List Bool))
  have hg : Primrec₂ (fun (_ : ℕ) (b : Bool) => if b then (1 : ℕ) else 0) :=
    Primrec₂.of_eq (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)).to₂
      (fun _ b => by cases b <;> rfl)
  exact (Primrec.list_map hd hg).of_eq fun v => rfl

/-- `q = ⟪encode σ, e⟫`; `jTest q w = 0` iff witness `w` makes `Φ_e` halt on `e`
under a `0/1` extension of `σ`. -/
def jTest (q w : ℕ) : ℕ :=
  if (evaln (Nat.unpair w).2
      (((Encodable.decode (α := List ℕ) (Nat.unpair q).1).getD []) ++ boolExt (Nat.unpair w).1)
      (ofNatCode (Nat.unpair q).2) (Nat.unpair q).2).isSome then 0 else 1

theorem jTest_prim : Nat.Primrec (fun v => jTest (Nat.unpair v).1 (Nat.unpair v).2) := by
  refine Primrec.nat_iff.mp ?_
  have hfuel : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair v).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hσ : Primrec fun v : ℕ =>
      (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const ([] : List ℕ))
  have hext : Primrec fun v : ℕ => boolExt (Nat.unpair (Nat.unpair v).2).1 :=
    boolExt_prim.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have he : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair v).1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hcode : Primrec fun v : ℕ => ofNatCode (Nat.unpair (Nat.unpair v).1).2 :=
    (Primrec.ofNat OracleCode).comp he
  have hev : Primrec fun v : ℕ =>
      evaln (Nat.unpair (Nat.unpair v).2).2
        (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [])
          ++ boolExt (Nat.unpair (Nat.unpair v).2).1)
        (ofNatCode (Nat.unpair (Nat.unpair v).1).2)
        (Nat.unpair (Nat.unpair v).1).2 :=
    evaln_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hfuel
      (Primrec.list_append.comp hσ hext)) hcode) he)
  have hci : ∀ b : Bool, (cond b (0 : ℕ) 1) = if b then (0 : ℕ) else 1 :=
    fun b => by cases b <;> rfl
  exact (Primrec.cond (Primrec.option_isSome.comp hev)
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => by
    simp only [jTest, Nat.unpair_pair]
    exact hci _

noncomputable def jPred (q : ℕ) : ℕ →. Bool :=
  fun w => (fun m => decide (m = 0)) <$> (Part.some (jTest q w) : Part ℕ)

noncomputable def jFun (q : ℕ) : Part ℕ := Nat.rfind (jPred q)

theorem jFun_partrec : Nat.Partrec jFun := by
  have h1 : Nat.Partrec (fun v : ℕ => (Part.some (jTest (Nat.unpair v).1 (Nat.unpair v).2) : Part ℕ)) :=
    Nat.Partrec.of_primrec jTest_prim
  refine (Nat.Partrec.rfind h1).of_eq fun q => ?_
  simp only [Nat.unpair_pair]
  rfl

theorem jFun_dom (q : ℕ) : (jFun q).Dom ↔ ∃ w, jTest q w = 0 := by
  rw [jFun, Nat.rfind_dom]
  constructor
  · rintro ⟨w, hw, -⟩
    rw [jPred, Part.map_eq_map, Part.mem_map_iff] at hw
    obtain ⟨x, hx, hx0⟩ := hw
    rw [Part.mem_some_iff.mp hx] at hx0
    exact ⟨w, of_decide_eq_true hx0⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, fun {m} _ => by rw [jPred, Part.map_eq_map, Part.map_some]; trivial⟩
    rw [jPred, Part.map_eq_map, Part.mem_map_iff]
    exact ⟨jTest q w, Part.mem_some _, by simp [hw]⟩

/-- `∃ w, jTest ⟪encode σ, e⟫ w = 0` iff `jExists σ e`. -/
theorem exists_jTest_iff (σ : List ℕ) (e : ℕ) :
    (∃ w, jTest (Nat.pair (Encodable.encode σ) e) w = 0) ↔ jExists σ e := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    by_contra hns
    rw [jTest, Nat.unpair_pair, Encodable.encodek, Option.getD_some, if_neg hns] at hw
    exact one_ne_zero hw
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [jTest, Nat.unpair_pair, Encodable.encodek, Option.getD_some, if_pos hw]

/-- **The `jExists` decision is `0′`-decidable.** -/
theorem jExists_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun q : ℕ => ((if (∃ w, jTest q w = 0) then 1 else 0 : ℕ) : Part ℕ)) := by
  have hrec : Nat.RecursiveIn {emptyO} jFun := jFun_partrec.recursiveIn
  refine (domain_recursiveIn_jump hrec).of_eq fun q => ?_
  rw [jFun_dom q]

theorem jTest_encode_zero_iff (σ : List ℕ) (e w : ℕ) :
    jTest (Nat.pair (Encodable.encode σ) e) w = 0 ↔
    (evaln (Nat.unpair w).2 (σ ++ boolExt (Nat.unpair w).1) (ofNatCode e) e).isSome = true := by
  rw [jTest, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  constructor
  · intro h; by_contra hns; rw [if_neg hns] at h; exact one_ne_zero h
  · intro h; rw [if_pos h]

theorem true_mem_jPred (q w : ℕ) : true ∈ jPred q w ↔ jTest q w = 0 := by
  rw [jPred, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩; rw [Part.mem_some_iff.mp hx] at hx0; exact of_decide_eq_true hx0
  · intro h; exact ⟨jTest q w, Part.mem_some _, by simp [h]⟩

/-- The search returns the least witness — matching `jtau`. -/
theorem jFun_eq_find (σ : List ℕ) (e : ℕ) (h : jExists σ e) :
    jFun (Nat.pair (Encodable.encode σ) e) = Part.some (Nat.find h) := by
  apply Part.eq_some_iff.mpr
  rw [jFun, Nat.mem_rfind]
  refine ⟨?_, fun {m} hm => ?_⟩
  · rw [true_mem_jPred, jTest_encode_zero_iff]
    exact Nat.find_spec h
  · rw [jPred, Part.map_eq_map, Part.mem_map_iff]
    refine ⟨jTest (Nat.pair (Encodable.encode σ) e) m, Part.mem_some _, ?_⟩
    have hfalse : jTest (Nat.pair (Encodable.encode σ) e) m ≠ 0 :=
      fun hc => Nat.find_min h hm ((jTest_encode_zero_iff σ e m).mp hc)
    exact decide_eq_false hfalse

/-! ### The construction is recursive in `C` (claim 1) -/

/-- `(decode c : List ℕ).getD []`. -/
def jDecode (c : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) c).getD []

theorem jDecode_encode (l : List ℕ) : jDecode (Encodable.encode l) = l := by
  rw [jDecode, Encodable.encodek, Option.getD_some]

theorem jDecode_prim : Primrec jDecode :=
  Primrec.option_getD.comp (Primrec.decode (α := List ℕ)) (Primrec.const ([] : List ℕ))

/-- The encoded stage step, run inside a `prec` fold: on `⟪a, ⟪y, c⟫⟫` with
`c = encode (jstr C y)`, produces `encode (jstr C (y+1))`.  Uses the `0′`
decision (`jExists`), the search `jFun` for the least extension, and the oracle
`C` for the coding bit. -/
noncomputable def jStepEnc (C : ℕ → Bool) (arg : ℕ) : Part ℕ :=
  ((if (∃ w, jTest (Nat.pair (Nat.unpair (Nat.unpair arg).2).2 (Nat.unpair (Nat.unpair arg).2).1) w = 0)
      then 1 else 0 : ℕ) : Part ℕ) >>= fun d =>
    (toPFun C (Nat.unpair (Nat.unpair arg).2).1) >>= fun cb =>
      Nat.rec
        (Part.some (Encodable.encode (jDecode (Nat.unpair (Nat.unpair arg).2).2 ++ [cb])))
        (fun _ _ => (jFun (Nat.pair (Nat.unpair (Nat.unpair arg).2).2 (Nat.unpair (Nat.unpair arg).2).1)).map
          (fun w => Encodable.encode
            (jDecode (Nat.unpair (Nat.unpair arg).2).2 ++ boolExt (Nat.unpair w).1 ++ [cb])))
        d

/-- Correctness of the encoded step: at `⟪a, ⟪y, encode (jstr C y)⟫⟫` it produces
`encode (jstr C (y+1))`. -/
theorem jStepEnc_spec (C : ℕ → Bool) (a y : ℕ) :
    jStepEnc C (Nat.pair a (Nat.pair y (Encodable.encode (jstr C y))))
      = Part.some (Encodable.encode (jstr C (y + 1))) := by
  rw [jStepEnc]
  simp only [Nat.unpair_pair, jDecode_encode]
  have hcb : toPFun C y = Part.some (if C y then 1 else 0) := by
    rw [toPFun]; congr 1; cases C y <;> rfl
  by_cases hj : jExists (jstr C y) y
  · have hd : (∃ w, jTest (Nat.pair (Encodable.encode (jstr C y)) y) w = 0) := by
      rw [exists_jTest_iff]; exact hj
    rw [if_pos hd, Part.coe_some, Part.bind_eq_bind, Part.bind_some, hcb,
      Part.bind_eq_bind, Part.bind_some]
    show (jFun (Nat.pair (Encodable.encode (jstr C y)) y)).map _ = _
    rw [jFun_eq_find (jstr C y) y hj, Part.map_some]
    congr 1
    rw [jstr, if_pos hj, jtau, dif_pos hj]
  · have hd : ¬ (∃ w, jTest (Nat.pair (Encodable.encode (jstr C y)) y) w = 0) := by
      rw [exists_jTest_iff]; exact hj
    rw [if_neg hd, Part.coe_some, Part.bind_eq_bind, Part.bind_some, hcb,
      Part.bind_eq_bind, Part.bind_some]
    show Part.some _ = Part.some _
    congr 1
    rw [jstr, if_neg hj]

/-- The query `⟪c, y⟫` extracted from a prec argument `⟪a, ⟪y, c⟫⟫`. -/
def jQ (arg : ℕ) : ℕ :=
  Nat.pair (Nat.unpair (Nat.unpair arg).2).2 (Nat.unpair (Nat.unpair arg).2).1

theorem jQ_prim : Primrec jQ := by
  unfold jQ
  exact Primrec₂.natPair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

/-- The stage-`y` code `c` extracted from `arg = ⟪a, ⟪y, c⟫⟫`. -/
def jC (arg : ℕ) : ℕ := (Nat.unpair (Nat.unpair arg).2).2

theorem jC_prim : Primrec jC :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

/-- The stage index `y`. -/
def jY (arg : ℕ) : ℕ := (Nat.unpair (Nat.unpair arg).2).1

theorem jY_prim : Primrec jY :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

/-- Base assembly on `p = ⟪arg, cb⟫`: `encode (jstr-code ++ [cb])`. -/
def jBaseFn (p : ℕ) : ℕ :=
  Encodable.encode (jDecode (jC (Nat.unpair p).1) ++ [(Nat.unpair p).2])

theorem jBaseFn_prim : Primrec jBaseFn := by
  unfold jBaseFn
  exact Primrec.encode.comp (Primrec.list_append.comp
    (jDecode_prim.comp (jC_prim.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const [])))

/-- Force assembly on `pw = ⟪⟪arg, cb⟫, w⟫`:
`encode (jstr-code ++ boolExt(w) ++ [cb])`. -/
def jAssembleFn (pw : ℕ) : ℕ :=
  Encodable.encode
    (jDecode (jC (Nat.unpair (Nat.unpair pw).1).1)
      ++ boolExt (Nat.unpair (Nat.unpair pw).2).1
      ++ [(Nat.unpair (Nat.unpair pw).1).2])

theorem jAssembleFn_prim : Primrec jAssembleFn := by
  unfold jAssembleFn
  exact Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.list_append.comp
      (jDecode_prim.comp (jC_prim.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
      (boolExt_prim.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
    (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.const [])))

/-- The forcing step (no coding bit), on `p = ⟪arg, cb⟫`, recursive in `0′`. -/
noncomputable def innerEnc (p : ℕ) : Part ℕ :=
  ((if (∃ w, jTest (jQ (Nat.unpair p).1) w = 0) then 1 else 0 : ℕ) : Part ℕ) >>= fun d =>
    Nat.rec (Part.some (jBaseFn p))
      (fun _ _ => (jFun (jQ (Nat.unpair p).1)).map
        (fun w => jAssembleFn (Nat.pair p w)))
      d

theorem innerEnc_recursiveIn : Nat.RecursiveIn {jumpFn emptyO} innerEnc := by
  have hdec : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((if (∃ w, jTest (jQ (Nat.unpair p).1) w = 0) then 1 else 0 : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp jExists_recursiveIn_jump
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (jQ_prim.comp (Primrec.fst.comp Primrec.unpair))))).of_eq
      fun p => by rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hbase : Nat.RecursiveIn {jumpFn emptyO} (fun p : ℕ => ((jBaseFn p : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp jBaseFn_prim)
  have hsrchp : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => jFun (jQ (Nat.unpair (Nat.unpair p).1).1)) :=
    (Nat.RecursiveIn.comp jFun_partrec.recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (jQ_prim.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))))).of_eq
      fun p => by rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hstep : Nat.RecursiveIn {jumpFn emptyO} (fun p : ℕ =>
      (Nat.pair <$> ((p : ℕ) : Part ℕ) <*> jFun (jQ (Nat.unpair (Nat.unpair p).1).1))
        >>= fun pw : ℕ =>
          ((jAssembleFn (Nat.pair (Nat.unpair (Nat.unpair pw).1).1 (Nat.unpair pw).2) : ℕ)
            : Part ℕ)) :=
    Nat.RecursiveIn.comp
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (jAssembleFn_prim.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair)))))
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hsrchp)
  have hprec := Nat.RecursiveIn.prec hbase hstep
  have hpairing : Nat.RecursiveIn {jumpFn emptyO} (fun p : ℕ =>
      Nat.pair <$> ((p : ℕ) : Part ℕ) <*>
        ((if (∃ w, jTest (jQ (Nat.unpair p).1) w = 0) then 1 else 0 : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hdec
  refine (Nat.RecursiveIn.comp hprec hpairing).of_eq fun p => ?_
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Seq.seq,
    Part.map_eq_map, Part.map_some, Nat.unpair_pair]
  rw [innerEnc]
  by_cases hd : ∃ w, jTest (jQ (Nat.unpair p).1) w = 0
  · rw [if_pos hd]
    simp [Part.bind_some, Part.bind_eq_bind, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def, Nat.unpair_pair]
  · rw [if_neg hd]
    simp [Part.bind_some, Part.bind_eq_bind, Nat.unpair_pair]

/-- The encoded step is recursive in `C ⊕ 0′`. -/
theorem jStepEnc_recursiveIn (C : ℕ → Bool) :
    Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO} (jStepEnc C) := by
  have hinner : Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO} innerEnc :=
    innerEnc_recursiveIn.subst (fun g hg => Nat.RecursiveIn.oracle g (Set.mem_insert_of_mem _ hg))
  have hC : Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO}
      (fun arg : ℕ => Cantor.toPFun C (jY arg)) :=
    (Nat.RecursiveIn.comp (Nat.RecursiveIn.oracle (Cantor.toPFun C)
      (Set.mem_insert (Cantor.toPFun C) {jumpFn emptyO}))
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp jY_prim))).of_eq
      fun arg => Part.bind_some _ _
  have hpair : Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO}
      (fun arg : ℕ => Nat.pair <$> ((arg : ℕ) : Part ℕ) <*> Cantor.toPFun C (jY arg)) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hC
  refine (Nat.RecursiveIn.comp hinner hpair).of_eq fun arg => ?_
  have hcb : Cantor.toPFun C ((Nat.unpair (Nat.unpair arg).2).1)
      = Part.some (if C ((Nat.unpair (Nat.unpair arg).2).1) then 1 else 0) := by
    rw [Cantor.toPFun]; congr 1; cases C ((Nat.unpair (Nat.unpair arg).2).1) <;> rfl
  simp only [Seq.seq, Part.coe_some, Part.map_eq_map, Part.bind_eq_bind, Part.map_some,
    Part.bind_some, innerEnc, jStepEnc, jQ, jC, jY, jBaseFn, jAssembleFn, Nat.unpair_pair, hcb]

/-- The encoded construction, as a `prec` fold. -/
noncomputable def jstrEnc (C : ℕ → Bool) (p : ℕ) : Part ℕ :=
  Nat.rec (((Encodable.encode ([] : List ℕ) : ℕ) : Part ℕ))
    (fun y IH => IH >>= fun i => jStepEnc C (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))
    (Nat.unpair p).2

theorem jstrEnc_recursiveIn (C : ℕ → Bool) :
    Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO} (jstrEnc C) := by
  have hbase : Nat.RecursiveIn {Cantor.toPFun C, jumpFn emptyO}
      (fun _ : ℕ => ((Encodable.encode ([] : List ℕ) : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.const _))
  exact (Nat.RecursiveIn.prec hbase (jStepEnc_recursiveIn C)).of_eq fun p => rfl

theorem jstrEnc_spec (C : ℕ → Bool) (n : ℕ) :
    jstrEnc C (Nat.pair 0 n) = Part.some (Encodable.encode (jstr C n)) := by
  induction n with
  | zero => rw [jstrEnc]; simp only [Nat.unpair_pair]; rfl
  | succ n ih =>
    have hunf : jstrEnc C (Nat.pair 0 (n + 1))
        = jstrEnc C (Nat.pair 0 n) >>= fun i => jStepEnc C (Nat.pair 0 (Nat.pair n i)) := by
      rw [jstrEnc, jstrEnc]; simp only [Nat.unpair_pair]
    rw [hunf, ih, Part.bind_eq_bind, Part.bind_some, jStepEnc_spec]

/-- `0′ = jump ∅` as `jumpFn emptyO`, at the point level. -/
theorem jumpFn_emptyO_eq : jumpFn emptyO = Cantor.toPFun (Cantor.jump (fun _ : ℕ => false)) := by
  rw [Cantor.toPFun_jump, Cantor.toPFun_const_false]; rfl

theorem jExtract_prim : Primrec (fun p : ℕ =>
    ((Encodable.decode (α := List ℕ) (Nat.unpair p).2).getD []).getD (Nat.unpair p).1 0) :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const ([] : List ℕ)))
      (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun _ => List.getD_eq_getElem?_getD.symm

/-- **Claim 1: `A ≤ᵀ C`.**  The construction is recursive in `C` (which computes
`0′`). -/
theorem jReal_le (C : ℕ → Bool) (hC : Cantor.jump (fun _ : ℕ => false) ≤ₜ C) :
    jReal C ≤ₜ C := by
  have hjstrC : Nat.RecursiveIn {Cantor.toPFun C} (jstrEnc C) :=
    (jstrEnc_recursiveIn C).subst (by
      intro g hg
      rcases hg with h | h
      · subst h; exact Nat.RecursiveIn.oracle _ rfl
      · rw [Set.mem_singleton_iff.mp h, jumpFn_emptyO_eq]
        exact RecursiveIn.iff_nat.mp hC)
  rw [Cantor.le_iff_bitg]
  have hbuild : Nat.RecursiveIn {Cantor.toPFun C} (fun n : ℕ => jstrEnc C (Nat.pair 0 (n + 1))) :=
    (Nat.RecursiveIn.comp hjstrC (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp (Primrec.const 0)
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))))).of_eq
      fun n => by simp only [id_eq, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hext : Nat.RecursiveIn {Cantor.toPFun C}
      (fun p : ℕ => ((((Encodable.decode (α := List ℕ) (Nat.unpair p).2).getD []).getD
        (Nat.unpair p).1 0 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp jExtract_prim)
  have hpair : Nat.RecursiveIn {Cantor.toPFun C}
      (fun n : ℕ => Nat.pair <$> ((n : ℕ) : Part ℕ) <*> jstrEnc C (Nat.pair 0 (n + 1))) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hbuild
  refine (Nat.RecursiveIn.comp hext hpair).of_eq fun n => ?_
  rw [jstrEnc_spec]
  simp only [Part.coe_some, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_some,
    Part.bind_some, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  have hlen : n < (jstr C (n + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (jstr_len_ge C (n + 1))
  rw [← jstr_getD_eq_bitg C (n + 1) n hlen]

/-- **Claim 2: `A′ ≤ᵀ C`.**  The jump of the construction is read off the
`C`-computable stage decisions. -/
theorem jump_jReal_le (C : ℕ → Bool) (hC : Cantor.jump (fun _ : ℕ => false) ≤ₜ C) :
    Cantor.jump (jReal C) ≤ₜ C := by
  have hjstrC : Nat.RecursiveIn {Cantor.toPFun C} (jstrEnc C) :=
    (jstrEnc_recursiveIn C).subst (by
      intro g hg
      rcases hg with h | h
      · subst h; exact Nat.RecursiveIn.oracle _ rfl
      · rw [Set.mem_singleton_iff.mp h, jumpFn_emptyO_eq]; exact RecursiveIn.iff_nat.mp hC)
  have hjumpC : Nat.RecursiveIn {Cantor.toPFun C}
      (fun q : ℕ => ((if (∃ w, jTest q w = 0) then 1 else 0 : ℕ) : Part ℕ)) :=
    jExists_recursiveIn_jump.subst (by
      intro g hg
      rw [Set.mem_singleton_iff.mp hg, jumpFn_emptyO_eq]; exact RecursiveIn.iff_nat.mp hC)
  rw [Cantor.le_iff_bitg]
  have hs0 : Nat.RecursiveIn {Cantor.toPFun C} (fun e : ℕ => jstrEnc C (Nat.pair 0 e)) :=
    (Nat.RecursiveIn.comp hjstrC (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)))).of_eq
      fun e => by simp only [id_eq, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hquery : Nat.RecursiveIn {Cantor.toPFun C}
      (fun e : ℕ => Nat.pair <$> jstrEnc C (Nat.pair 0 e) <*> ((e : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.pair hs0 ((Primrec.nat_iff.mp Primrec.id).recursiveIn)
  refine (Nat.RecursiveIn.comp hjumpC hquery).of_eq fun e => ?_
  rw [jstrEnc_spec]
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_some, Part.bind_some,
    Part.coe_some, exists_jTest_iff]
  have hbit : (if jExists (jstr C e) e then (1 : ℕ) else 0) = bitg (jump (jReal C)) e := by
    rw [bitg]
    by_cases hj : jExists (jstr C e) e
    · rw [if_pos hj]
      have : jump (jReal C) e = true := by
        rw [jump]; exact decide_eq_true ((dom_iff_jExists C e).mpr hj)
      rw [this]; rfl
    · rw [if_neg hj]
      have : jump (jReal C) e = false := by
        rw [jump]; exact decide_eq_false (fun hd => hj ((dom_iff_jExists C e).mp hd))
      rw [this]; rfl
  rw [hbit]

/-! ### Claim 3: `C ≤ᵀ A′` (decoding) -/

/-- The coding bit `C e` sits at the last position of stage `e+1`. -/
theorem C_eq_jReal (C : ℕ → Bool) (e : ℕ) :
    C e = jReal C ((jstr C (e + 1)).length - 1) := by
  have hstr : jstr C (e + 1)
      = (if jExists (jstr C e) e then jstr C e ++ jtau (jstr C e) e else jstr C e)
        ++ [if C e then 1 else 0] := by rw [jstr]
  set σ' := if jExists (jstr C e) e then jstr C e ++ jtau (jstr C e) e else jstr C e with hσ'
  have hlen : (jstr C (e + 1)).length = σ'.length + 1 := by rw [hstr]; simp
  have hge : e + 1 ≤ (jstr C (e + 1)).length := jstr_len_ge C (e + 1)
  set m := (jstr C (e + 1)).length - 1 with hm
  have hmeq : m = σ'.length := by omega
  have hmlt : m < (jstr C (e + 1)).length := by omega
  have hlast : (jstr C (e + 1)).getD m 0 = (if C e then 1 else 0) := by
    rw [hstr, List.getD_eq_getElem?_getD, hmeq, List.getElem?_append_right (le_refl _),
      Nat.sub_self]
    simp
  rw [jReal]
  have hget : (jstr C (m + 1)).getD m 0 = (jstr C (e + 1)).getD m 0 :=
    prefix_getD (jstr_mono C (by omega)) hmlt
  rw [hget, hlast]
  cases C e <;> simp

/-- The encoded length step (reconstruction), on `⟪a, ⟪y, ln⟫⟫` with
`ln = |jstr C y|`: computes `|jstr C (y+1)|`.  Uses `graphEnc (jReal C)` (to
rebuild the stage string, `≤ᵀ A′`), the oracle `A′` (the forcing decision), and
the search `jFun` (for the forcing length). -/
noncomputable def lenStepEnc (C : ℕ → Bool) (arg : ℕ) : Part ℕ :=
  graphEnc (jReal C) (Nat.unpair (Nat.unpair arg).2).2 >>= fun σenc =>
    Cantor.toPFun (Cantor.jump (jReal C)) (Nat.unpair (Nat.unpair arg).2).1 >>= fun aBit =>
      Nat.rec (Part.some ((Nat.unpair (Nat.unpair arg).2).2 + 1))
        (fun _ _ => (jFun (Nat.pair σenc (Nat.unpair (Nat.unpair arg).2).1)).map
          (fun w => (Nat.unpair (Nat.unpair arg).2).2 + (boolExt (Nat.unpair w).1).length + 1))
        aBit

theorem lenStepEnc_spec (C : ℕ → Bool) (a y : ℕ) :
    lenStepEnc C (Nat.pair a (Nat.pair y (jstr C y).length))
      = Part.some (jstr C (y + 1)).length := by
  rw [lenStepEnc]
  simp only [Nat.unpair_pair]
  -- σenc = encode (jstr C y)
  have hσ : graphEnc (jReal C) (jstr C y).length = Part.some (Encodable.encode (jstr C y)) := by
    rw [graphEnc, ← jstr_eq_graphOf]
  rw [hσ, Part.bind_eq_bind, Part.bind_some]
  -- aBit = jExists decision
  have haBit : Cantor.toPFun (Cantor.jump (jReal C)) y
      = Part.some (if jExists (jstr C y) y then 1 else 0) := by
    rw [Cantor.toPFun, jump]
    simp only [jumpP]
    by_cases hj : jExists (jstr C y) y
    · rw [if_pos hj]; simp [(dom_iff_jExists C y).mpr hj]
    · rw [if_neg hj]
      have hnd : ¬ (eval (Cantor.toPFun (jReal C)) (ofNatCode y) y).Dom :=
        fun hd => hj ((dom_iff_jExists C y).mp hd)
      simp [hnd]
  rw [haBit, Part.bind_eq_bind, Part.bind_some]
  by_cases hj : jExists (jstr C y) y
  · rw [if_pos hj]
    show (jFun (Nat.pair (Encodable.encode (jstr C y)) y)).map _ = _
    rw [jFun_eq_find (jstr C y) y hj, Part.map_some]
    have hjstr : (jstr C (y + 1)).length
        = (jstr C y).length + (boolExt (Nat.unpair (Nat.find hj)).1).length + 1 := by
      rw [jstr, if_pos hj, jtau, dif_pos hj]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]
    rw [hjstr]
  · rw [if_neg hj]
    show Part.some ((jstr C y).length + 1) = _
    have hjstr : (jstr C (y + 1)).length = (jstr C y).length + 1 := by
      rw [jstr, if_neg hj]
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hjstr]

/-- Query `⟪σenc, y⟫` from `a = ⟪arg, σenc⟫`, `arg = ⟪·, ⟪y, ln⟫⟫`. -/
def lenQFn (a : ℕ) : ℕ :=
  Nat.pair (Nat.unpair a).2 (Nat.unpair (Nat.unpair (Nat.unpair a).1).2).1

theorem lenQFn_prim : Primrec lenQFn :=
  Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))

/-- Base length `ln + 1` from `a = ⟪arg, σenc⟫`. -/
def lenBaseFn (a : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair a).1).2).2 + 1

theorem lenBaseFn_prim : Primrec lenBaseFn :=
  Primrec.nat_add.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    (Primrec.const 1)

/-- Force length `ln + |boolExt w| + 1` from `aw = ⟪a, w⟫`. -/
def lenAssembleFn (aw : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair aw).1).1).2).2
    + (boolExt (Nat.unpair (Nat.unpair aw).2).1).length + 1

theorem lenAssembleFn_prim : Primrec lenAssembleFn :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))))
      (Primrec.list_length.comp (boolExt_prim.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.const 1)

theorem lenStepEnc_recursiveIn (C : ℕ → Bool) :
    Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))} (lenStepEnc C) := by
  -- graphEnc (jReal C) lifted to `A′` (since `jReal C ≤ᵀ A′`)
  have hgA : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))} (graphEnc (jReal C)) :=
    (graphEnc_recursiveIn (jReal C)).subst (by
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact RecursiveIn.iff_nat.mp (le_jump (jReal C)))
  have hbase : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))}
      (fun a : ℕ => ((lenBaseFn a : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp lenBaseFn_prim)
  have hsrchp : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))}
      (fun p : ℕ => jFun (lenQFn (Nat.unpair p).1)) :=
    (Nat.RecursiveIn.comp jFun_partrec.recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (lenQFn_prim.comp (Primrec.fst.comp Primrec.unpair))))).of_eq
      fun p => by rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hstep : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))} (fun p : ℕ =>
      (Nat.pair <$> ((p : ℕ) : Part ℕ) <*> jFun (lenQFn (Nat.unpair p).1))
        >>= fun pw : ℕ =>
          ((lenAssembleFn (Nat.pair (Nat.unpair (Nat.unpair pw).1).1 (Nat.unpair pw).2) : ℕ)
            : Part ℕ)) :=
    Nat.RecursiveIn.comp
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (lenAssembleFn_prim.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair)))))
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hsrchp)
  have hprec := Nat.RecursiveIn.prec hbase hstep
  -- pairing: `⟪⟪arg, σenc⟫, aBit⟫`
  have hgm : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))}
      (fun arg : ℕ => graphEnc (jReal C) (Nat.unpair (Nat.unpair arg).2).2) :=
    (Nat.RecursiveIn.comp hgA (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))).of_eq
      fun arg => by rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have haBit : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))}
      (fun arg : ℕ => Cantor.toPFun (Cantor.jump (jReal C)) (Nat.unpair (Nat.unpair arg).2).1) :=
    (Nat.RecursiveIn.comp
      (Nat.RecursiveIn.oracle (Cantor.toPFun (Cantor.jump (jReal C))) (Set.mem_singleton_iff.mpr rfl))
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))).of_eq
      fun arg => Part.bind_some _ _
  have hpairing : Nat.RecursiveIn {Cantor.toPFun (Cantor.jump (jReal C))} (fun arg : ℕ =>
      Nat.pair <$> (Nat.pair <$> ((arg : ℕ) : Part ℕ)
        <*> graphEnc (jReal C) (Nat.unpair (Nat.unpair arg).2).2)
        <*> Cantor.toPFun (Cantor.jump (jReal C)) (Nat.unpair (Nat.unpair arg).2).1) :=
    Nat.RecursiveIn.pair
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hgm) haBit
  refine (Nat.RecursiveIn.comp hprec hpairing).of_eq fun arg => ?_
  rw [lenStepEnc,
    show graphEnc (jReal C) (Nat.unpair (Nat.unpair arg).2).2
      = Part.some (Encodable.encode (graphOf (bitg (jReal C)) (Nat.unpair (Nat.unpair arg).2).2))
      from rfl,
    show Cantor.toPFun (Cantor.jump (jReal C)) (Nat.unpair (Nat.unpair arg).2).1
      = Part.some (cond (Cantor.jump (jReal C) (Nat.unpair (Nat.unpair arg).2).1) 1 0) from rfl]
  simp only [Part.coe_some, Part.map_eq_map, Part.bind_eq_bind, Seq.seq, Part.map_some,
    Part.bind_some]
  cases Cantor.jump (jReal C) (Nat.unpair (Nat.unpair arg).2).1
  · simp [lenBaseFn, Nat.unpair_pair]
  · simp [Part.bind_some, Part.bind_eq_bind, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def, Nat.unpair_pair, lenQFn, lenAssembleFn]

end OracleCode

#print axioms OracleCode.jstr_mono
#print axioms OracleCode.dom_iff_jExists
#print axioms OracleCode.jReal_le
#print axioms OracleCode.jump_jReal_le
#print axioms OracleCode.C_eq_jReal
#print axioms OracleCode.lenStepEnc_recursiveIn
