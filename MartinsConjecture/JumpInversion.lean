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

end OracleCode

#print axioms OracleCode.jstr_mono
#print axioms OracleCode.dom_iff_jExists
