/-
The effective Kleene–Post theorem: incomparable Turing degrees below `0′`.

`∃ A B : ℕ → Bool, A ≤ᵀ 0′ ∧ B ≤ᵀ 0′ ∧ ¬(A ≤ᵀ B) ∧ ¬(B ≤ᵀ A)`.

The finite-extension construction, with each stage's Σ₁ decision answered by
`0′` (`ExtHalting`).  Strings are `List ℕ` of 0/1 values (matching `evaln`'s
oracle table).  At an even stage `2e` we defeat `Φₑᴮ = A`; at odd `2e+1`,
`Φₑᴬ = B`.  Incomparability uses the `evaln` bridge
(`evaln_sound`/`complete`/`mono`); the `0′`-bound uses that the whole
construction is recursive in `jump ∅`.

Phase 1 (this section): the construction and the defeat/incomparability
lemmas (mathematical, `Classical` where convenient).
-/
import MartinsConjecture.ExtHalting

open scoped Computability
open OracleCode Cantor

namespace KleenePostJump

attribute [local instance] Classical.propDecidable

/-- A bit differing from `v` (as a value): `diagBit v ≠ v` always. -/
def diagBit (v : ℕ) : ℕ := if v = 0 then 1 else 0

theorem diagBit_ne (v : ℕ) : diagBit v ≠ v := by
  rw [diagBit]; split <;> omega

theorem diagBit_le_one (v : ℕ) : diagBit v ≤ 1 := by
  rw [diagBit]; by_cases h : v = 0 <;> simp [h]

/-- The extension coded by `w` — a 0/1 string (we search over `List Bool`). -/
def extOf (w : ℕ) : List ℕ :=
  ((Encodable.decode (α := List Bool) (Nat.unpair w).1).getD []).map
    (fun b => if b then 1 else 0)

theorem extOf_le (w : ℕ) : ∀ x ∈ extOf w, x ≤ 1 := by
  intro x hx
  rw [extOf, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  by_cases h : b <;> simp [h]

/-- The step counter coded by `w`. -/
def fuelOf (w : ℕ) : ℕ := (Nat.unpair w).2

/-- `w` witnesses that machine `e` halts on input `len` under `pas`'s
extension `extOf w`. -/
def haltsAt (pas : List ℕ) (e len w : ℕ) : Prop :=
  (evaln (fuelOf w) (pas ++ extOf w) (ofNatCode e) len).isSome = true

/-- One requirement step: extend `(act, pas)` to defeat `Φₑ^pas = act`.
Returns `(act ++ actExt, pas ++ pasExt)`. -/
noncomputable def reqStep (act pas : List ℕ) (e : ℕ) : List ℕ × List ℕ :=
  if h : ∃ w, haltsAt pas e act.length w then
    let w := Nat.find h
    let v := (evaln (fuelOf w) (pas ++ extOf w) (ofNatCode e) act.length).getD 0
    (act ++ [diagBit v], pas ++ extOf w)
  else
    (act ++ [0], pas ++ [0])

/-- The active side is always extended by exactly one bit. -/
theorem reqStep_fst_len (act pas : List ℕ) (e : ℕ) :
    (reqStep act pas e).1.length = act.length + 1 := by
  rw [reqStep]; split <;> simp

theorem reqStep_fst_prefix (act pas : List ℕ) (e : ℕ) :
    act <+: (reqStep act pas e).1 := by
  rw [reqStep]; split <;> exact List.prefix_append _ _

theorem reqStep_snd_prefix (act pas : List ℕ) (e : ℕ) :
    pas <+: (reqStep act pas e).2 := by
  rw [reqStep]; split <;> exact List.prefix_append _ _

/-- The stage-`r` condition `(σ, τ)`. -/
noncomputable def cond : ℕ → List ℕ × List ℕ
  | 0 => ([], [])
  | r + 1 =>
    if r % 2 = 0 then
      reqStep (cond r).1 (cond r).2 (r / 2)
    else
      let p := reqStep (cond r).2 (cond r).1 (r / 2)
      (p.2, p.1)

theorem cond_fst_prefix (r : ℕ) : (cond r).1 <+: (cond (r + 1)).1 := by
  rw [cond]
  by_cases h : r % 2 = 0
  · rw [if_pos h]; exact reqStep_fst_prefix _ _ _
  · rw [if_neg h]; exact reqStep_snd_prefix _ _ _

theorem cond_snd_prefix (r : ℕ) : (cond r).2 <+: (cond (r + 1)).2 := by
  rw [cond]
  by_cases h : r % 2 = 0
  · rw [if_pos h]; exact reqStep_snd_prefix _ _ _
  · rw [if_neg h]; exact reqStep_fst_prefix _ _ _

theorem cond_fst_mono {r r' : ℕ} (h : r ≤ r') : (cond r).1 <+: (cond r').1 := by
  induction r' with
  | zero => rw [Nat.le_zero.mp h]
  | succ r' ih =>
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (cond_fst_prefix r')

theorem cond_snd_mono {r r' : ℕ} (h : r ≤ r') : (cond r).2 <+: (cond r').2 := by
  induction r' with
  | zero => rw [Nat.le_zero.mp h]
  | succ r' ih =>
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (cond_snd_prefix r')

/-- A prefix superstring agrees at positions inside the shorter string. -/
theorem prefix_getD {l l' : List ℕ} (h : l <+: l') {n : ℕ} (hn : n < l.length) :
    l'.getD n 0 = l.getD n 0 := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

theorem reqStep_fst_le {act pas : List ℕ} {e : ℕ}
    (hact : ∀ x ∈ act, x ≤ 1) : ∀ x ∈ (reqStep act pas e).1, x ≤ 1 := by
  rw [reqStep]; split
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hact x h
    · rw [List.mem_singleton] at h; rw [h]; exact diagBit_le_one _
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hact x h
    · rw [List.mem_singleton] at h; omega

theorem reqStep_snd_le {act pas : List ℕ} {e : ℕ}
    (hpas : ∀ x ∈ pas, x ≤ 1) : ∀ x ∈ (reqStep act pas e).2, x ≤ 1 := by
  rw [reqStep]; split
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hpas x h
    · exact extOf_le _ x h
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hpas x h
    · rw [List.mem_singleton] at h; omega

/-- All values in the strings are 0/1. -/
theorem cond_le : ∀ r, (∀ x ∈ (cond r).1, x ≤ 1) ∧ (∀ x ∈ (cond r).2, x ≤ 1)
  | 0 => ⟨by simp [cond], by simp [cond]⟩
  | r + 1 => by
    obtain ⟨ih1, ih2⟩ := cond_le r
    rw [cond]
    by_cases h : r % 2 = 0
    · rw [if_pos h]; exact ⟨reqStep_fst_le ih1, reqStep_snd_le ih2⟩
    · rw [if_neg h]; exact ⟨reqStep_snd_le ih1, reqStep_fst_le ih2⟩

theorem strings_fst_le (r n : ℕ) (_hn : n < (cond r).1.length) :
    (cond r).1.getD n 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (cond r).1[n]? with _ | x
  · simp
  · simp only [Option.getD_some]
    exact (cond_le r).1 x (List.mem_of_getElem? h)

theorem strings_snd_le (r n : ℕ) (_hn : n < (cond r).2.length) :
    (cond r).2.getD n 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (cond r).2[n]? with _ | x
  · simp
  · simp only [Option.getD_some]
    exact (cond_le r).2 x (List.mem_of_getElem? h)

/-- Both strings have length at least `m` after `2m` stages. -/
theorem cond_len_bound : ∀ m, m ≤ (cond (2 * m)).1.length ∧ m ≤ (cond (2 * m)).2.length
  | 0 => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := cond_len_bound m
    have he : cond (2 * m + 1) = reqStep (cond (2 * m)).1 (cond (2 * m)).2 m := by
      conv_lhs => rw [cond]
      rw [if_pos (show (2 * m) % 2 = 0 by omega), show (2 * m) / 2 = m by omega]
    have ho : cond (2 * m + 2)
        = ((reqStep (cond (2 * m + 1)).2 (cond (2 * m + 1)).1 m).2,
           (reqStep (cond (2 * m + 1)).2 (cond (2 * m + 1)).1 m).1) := by
      conv_lhs => rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl, cond]
      rw [if_neg (show ¬ (2 * m + 1) % 2 = 0 by omega),
        show (2 * m + 1) / 2 = m by omega]
    have h1 : (cond (2 * m + 1)).1.length = (cond (2 * m)).1.length + 1 := by
      rw [he]; exact reqStep_fst_len _ _ _
    have h2 : (cond (2 * m)).2.length ≤ (cond (2 * m + 1)).2.length := by
      rw [he]; exact (reqStep_snd_prefix _ _ _).length_le
    have h3 : (cond (2 * m + 1)).1.length ≤ (cond (2 * m + 2)).1.length := by
      rw [ho]; exact (reqStep_snd_prefix _ _ _).length_le
    have h4 : (cond (2 * m + 2)).2.length = (cond (2 * m + 1)).2.length + 1 := by
      rw [ho]; exact reqStep_fst_len _ _ _
    have hmm : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hmm]
    exact ⟨by omega, by omega⟩

theorem cond_fst_len_gt (n : ℕ) : n < (cond (2 * (n + 1))).1.length :=
  lt_of_lt_of_le (Nat.lt_succ_self n) (cond_len_bound (n + 1)).1

theorem cond_snd_len_gt (n : ℕ) : n < (cond (2 * (n + 1))).2.length :=
  lt_of_lt_of_le (Nat.lt_succ_self n) (cond_len_bound (n + 1)).2

/-- The left real `A` of the construction. -/
noncomputable def A (n : ℕ) : Bool := (cond (2 * (n + 1))).1.getD n 0 = 1

/-- The right real `B` of the construction. -/
noncomputable def B (n : ℕ) : Bool := (cond (2 * (n + 1))).2.getD n 0 = 1

/-- `A`'s value at `n` is read off from any long-enough stage. -/
theorem bitg_A (r n : ℕ) (hn : n < (cond r).1.length) :
    bitg A n = (cond r).1.getD n 0 := by
  have key : (cond r).1.getD n 0 = (cond (2 * (n + 1))).1.getD n 0 := by
    rcases le_total r (2 * (n + 1)) with hle | hle
    · rw [prefix_getD (cond_fst_mono hle) hn]
    · rw [prefix_getD (cond_fst_mono hle) (cond_fst_len_gt n)]
  have hle1 : (cond r).1.getD n 0 ≤ 1 := strings_fst_le r n hn
  have hAn : A n = decide ((cond r).1.getD n 0 = 1) := by rw [A, key]
  rw [bitg, hAn]
  by_cases h1 : (cond r).1.getD n 0 = 1
  · rw [h1]; rfl
  · have h0 : (cond r).1.getD n 0 = 0 := by omega
    rw [h0]; rfl

/-- `B`'s value at `n` is read off from any long-enough stage. -/
theorem bitg_B (r n : ℕ) (hn : n < (cond r).2.length) :
    bitg B n = (cond r).2.getD n 0 := by
  have key : (cond r).2.getD n 0 = (cond (2 * (n + 1))).2.getD n 0 := by
    rcases le_total r (2 * (n + 1)) with hle | hle
    · rw [prefix_getD (cond_snd_mono hle) hn]
    · rw [prefix_getD (cond_snd_mono hle) (cond_snd_len_gt n)]
  have hle1 : (cond r).2.getD n 0 ≤ 1 := strings_snd_le r n hn
  have hBn : B n = decide ((cond r).2.getD n 0 = 1) := by rw [B, key]
  rw [bitg, hBn]
  by_cases h1 : (cond r).2.getD n 0 = 1
  · rw [h1]; rfl
  · have h0 : (cond r).2.getD n 0 = 0 := by omega
    rw [h0]; rfl

/-! ### Helper list/graph facts -/

theorem list_getD_range (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h2)]; rfl

theorem graphOf_take (g : ℕ → ℕ) {m K : ℕ} (h : m ≤ K) :
    (graphOf g K).take m = graphOf g m := by
  rw [graphOf, graphOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bitg_le_one (X : ℕ → Bool) (i : ℕ) : bitg X i ≤ 1 := by
  rw [bitg]; cases X i <;> simp

/-- `τ` (the stage-`r` right string) is exactly `B`'s first `|τ|` bits. -/
theorem cond_snd_eq_graph (r : ℕ) :
    (cond r).2 = graphOf (bitg B) (cond r).2.length := by
  conv_lhs => rw [← list_getD_range (cond r).2]
  rw [graphOf]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [bitg_B r i hi]

/-- `σ` (the stage-`r` left string) is exactly `A`'s first `|σ|` bits. -/
theorem cond_fst_eq_graph (r : ℕ) :
    (cond r).1 = graphOf (bitg A) (cond r).1.length := by
  conv_lhs => rw [← list_getD_range (cond r).1]
  rw [graphOf]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [bitg_A r i hi]

/-! ### The defeat lemmas -/

theorem defeat_even (e : ℕ) : eval (toPFun B) (ofNatCode e) ≠ toPFun A := by
  intro heq
  have hstep : cond (2 * e + 1) = reqStep (cond (2 * e)).1 (cond (2 * e)).2 e := by
    conv_lhs => rw [cond]
    rw [if_pos (show (2 * e) % 2 = 0 by omega), show (2 * e) / 2 = e by omega]
  set σ := (cond (2 * e)).1 with hσ
  set τ := (cond (2 * e)).2 with hτ
  -- `B` correctly tabulated by any stage's `τ`-side.
  have hBtab : ∀ (s : ℕ), ∀ i, (hi : i < (cond s).2.length) →
      toPFun B i = Part.some ((cond s).2)[i] := by
    intro s i hi
    rw [toPFun_eq_bitg, bitg_B s i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  by_cases hh : ∃ w, haltsAt τ e σ.length w
  · -- YES: force convergence and diagonalize.
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hh)
    have hlv : (evaln (fuelOf (Nat.find hh)) (τ ++ extOf (Nat.find hh))
        (ofNatCode e) σ.length).getD 0 = v := by rw [hv]; rfl
    have hcond1 : cond (2 * e + 1)
        = (σ ++ [diagBit v], τ ++ extOf (Nat.find hh)) := by
      rw [hstep, reqStep, dif_pos hh]; simp only [hlv]
    have hL : τ ++ extOf (Nat.find hh) = (cond (2 * e + 1)).2 :=
      (congrArg Prod.snd hcond1).symm
    -- A's bit at `σ.length` is `diagBit v`
    have hAlen : bitg A σ.length = diagBit v := by
      have hlt : σ.length < (cond (2 * e + 1)).1.length := by
        rw [hcond1]; simp
      rw [bitg_A (2 * e + 1) σ.length hlt, hcond1]
      simp only []
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp
    -- Φₑᴮ(σ.length) = v via soundness
    have hBval : v ∈ eval (toPFun B) (ofNatCode e) σ.length := by
      have hev : evaln (fuelOf (Nat.find hh)) (cond (2 * e + 1)).2
          (ofNatCode e) σ.length = some v := hL ▸ hv
      exact evaln_sound (fun i hi => hBtab (2 * e + 1) i hi) hev
    rw [heq] at hBval
    rw [toPFun_eq_bitg, hAlen, Part.mem_some_iff] at hBval
    exact diagBit_ne v hBval.symm
  · -- NO: divergence defeats the requirement.
    have hAdom : (toPFun A σ.length).Dom := trivial
    rw [← heq] at hAdom
    obtain ⟨vv, hvv⟩ := Part.dom_iff_mem.mp hAdom
    obtain ⟨k, hk⟩ := evaln_complete (toPFun_eq_bitg B) hvv
    set K := max k τ.length with hK
    have hmono : evaln K (graphOf (bitg B) K) (ofNatCode e) σ.length = some vv :=
      evaln_mono (le_max_left _ _) (graphOf_prefix (le_max_left _ _)) hk
    set ext' := (graphOf (bitg B) K).drop τ.length with hext'
    have hsplit : graphOf (bitg B) K = τ ++ ext' := by
      conv_lhs => rw [← List.take_append_drop τ.length (graphOf (bitg B) K)]
      rw [hext', graphOf_take (bitg B) (le_max_right _ _),
        ← cond_snd_eq_graph (2 * e), ← hτ]
    have hext'_le : ∀ x ∈ ext', x ≤ 1 := by
      intro x hx
      have := List.mem_of_mem_drop (hext' ▸ hx)
      rw [graphOf, List.mem_map] at this
      obtain ⟨i, -, rfl⟩ := this
      exact bitg_le_one B i
    set extBool : List Bool := ext'.map (fun x => x = 1) with hextBool
    have hroundtrip : extOf (Nat.pair (Encodable.encode extBool) K) = ext' := by
      rw [extOf, Nat.unpair_pair, Encodable.encodek, Option.getD_some, hextBool,
        List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id ext')
      intro x hx
      have hx1 := hext'_le x hx
      simp only [Function.comp]
      by_cases h : x = 1
      · simp [h]
      · have : x = 0 := by omega
        simp [this]
    apply hh
    refine ⟨Nat.pair (Encodable.encode extBool) K, ?_⟩
    rw [haltsAt, fuelOf, Nat.unpair_pair, hroundtrip, ← hsplit, hmono]
    rfl


/-- Defeat lemma (odd requirements): `Φₑᴬ ≠ B`. -/
theorem defeat_odd (e : ℕ) : eval (toPFun A) (ofNatCode e) ≠ toPFun B := by
  intro heq
  have hstep : cond (2 * e + 2)
      = ((reqStep (cond (2 * e + 1)).2 (cond (2 * e + 1)).1 e).2,
         (reqStep (cond (2 * e + 1)).2 (cond (2 * e + 1)).1 e).1) := by
    conv_lhs => rw [show 2 * e + 2 = (2 * e + 1) + 1 from rfl, cond]
    rw [if_neg (show ¬ (2 * e + 1) % 2 = 0 by omega), show (2 * e + 1) / 2 = e by omega]
  set act := (cond (2 * e + 1)).2 with hact
  set pas := (cond (2 * e + 1)).1 with hpas
  have hAtab : ∀ (s : ℕ), ∀ i, (hi : i < (cond s).1.length) →
      toPFun A i = Part.some ((cond s).1)[i] := by
    intro s i hi
    rw [toPFun_eq_bitg, bitg_A s i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  by_cases hh : ∃ w, haltsAt pas e act.length w
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hh)
    have hlv : (evaln (fuelOf (Nat.find hh)) (pas ++ extOf (Nat.find hh))
        (ofNatCode e) act.length).getD 0 = v := by rw [hv]; rfl
    have hcond1 : cond (2 * e + 2)
        = (pas ++ extOf (Nat.find hh), act ++ [diagBit v]) := by
      rw [hstep, reqStep, dif_pos hh]; simp only [hlv]
    have hL : pas ++ extOf (Nat.find hh) = (cond (2 * e + 2)).1 :=
      (congrArg Prod.fst hcond1).symm
    have hBlen : bitg B act.length = diagBit v := by
      have hlt : act.length < (cond (2 * e + 2)).2.length := by
        rw [hcond1]; simp
      rw [bitg_B (2 * e + 2) act.length hlt, hcond1]
      simp only []
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp
    have hAval : v ∈ eval (toPFun A) (ofNatCode e) act.length := by
      have hev : evaln (fuelOf (Nat.find hh)) (cond (2 * e + 2)).1
          (ofNatCode e) act.length = some v := hL ▸ hv
      exact evaln_sound (fun i hi => hAtab (2 * e + 2) i hi) hev
    rw [heq] at hAval
    rw [toPFun_eq_bitg, hBlen, Part.mem_some_iff] at hAval
    exact diagBit_ne v hAval.symm
  · have hBdom : (toPFun B act.length).Dom := trivial
    rw [← heq] at hBdom
    obtain ⟨vv, hvv⟩ := Part.dom_iff_mem.mp hBdom
    obtain ⟨k, hk⟩ := evaln_complete (toPFun_eq_bitg A) hvv
    set K := max k pas.length with hK
    have hmono : evaln K (graphOf (bitg A) K) (ofNatCode e) act.length = some vv :=
      evaln_mono (le_max_left _ _) (graphOf_prefix (le_max_left _ _)) hk
    set ext' := (graphOf (bitg A) K).drop pas.length with hext'
    have hsplit : graphOf (bitg A) K = pas ++ ext' := by
      conv_lhs => rw [← List.take_append_drop pas.length (graphOf (bitg A) K)]
      rw [hext', graphOf_take (bitg A) (le_max_right _ _),
        ← cond_fst_eq_graph (2 * e + 1), ← hpas]
    have hext'_le : ∀ x ∈ ext', x ≤ 1 := by
      intro x hx
      have := List.mem_of_mem_drop (hext' ▸ hx)
      rw [graphOf, List.mem_map] at this
      obtain ⟨i, -, rfl⟩ := this
      exact bitg_le_one A i
    set extBool : List Bool := ext'.map (fun x => x = 1) with hextBool
    have hroundtrip : extOf (Nat.pair (Encodable.encode extBool) K) = ext' := by
      rw [extOf, Nat.unpair_pair, Encodable.encodek, Option.getD_some, hextBool,
        List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id ext')
      intro x hx
      have hx1 := hext'_le x hx
      simp only [Function.comp]
      by_cases h : x = 1
      · simp [h]
      · have : x = 0 := by omega
        simp [this]
    apply hh
    refine ⟨Nat.pair (Encodable.encode extBool) K, ?_⟩
    rw [haltsAt, fuelOf, Nat.unpair_pair, hroundtrip, ← hsplit, hmono]
    rfl

/-! ### Incomparability -/

theorem not_A_le_B : ¬ (A ≤ₜ B) := by
  intro h
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  exact defeat_even (encodeCode c) (by rw [ofNatCode_encodeCode]; exact hc)

theorem not_B_le_A : ¬ (B ≤ₜ A) := by
  intro h
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp h)
  exact defeat_odd (encodeCode c) (by rw [ofNatCode_encodeCode]; exact hc)

/-! ### Phase 2: the construction is recursive in `0′` -/

/-- The empty oracle; its jump is `0′`. -/
def emptyO : ℕ →. ℕ := fun _ => Part.some 0

/-- `extOf` is primitive recursive. -/
theorem extOf_prim : Primrec extOf := by
  have hd : Primrec (fun w : ℕ =>
      (Encodable.decode (α := List Bool) (Nat.unpair w).1).getD []) :=
    Primrec.option_getD.comp
      ((Primrec.decode (α := List Bool)).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const ([] : List Bool))
  have hg : Primrec₂ (fun (_ : ℕ) (b : Bool) => if b then (1 : ℕ) else 0) :=
    Primrec₂.of_eq (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)).to₂
      (fun _ b => by cases b <;> rfl)
  exact (Primrec.list_map hd hg).of_eq fun w => rfl

/-- The step-test on `q = ⟪encode pas, ⟪e, len⟫⟫`: `0` iff `w` witnesses a
halt. -/
def srchTest (q w : ℕ) : ℕ :=
  bif (evaln (fuelOf w)
      (((Encodable.decode (α := List ℕ) (Nat.unpair q).1).getD []) ++ extOf w)
      (ofNatCode (Nat.unpair (Nat.unpair q).2).1)
      (Nat.unpair (Nat.unpair q).2).2).isSome then 0 else 1

theorem srchTest_prim :
    Nat.Primrec (fun v => srchTest (Nat.unpair v).1 (Nat.unpair v).2) := by
  refine Primrec.nat_iff.mp ?_
  have hev : Primrec fun v : ℕ =>
      evaln (fuelOf (Nat.unpair v).2)
        (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [])
          ++ extOf (Nat.unpair v).2)
        (ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 := by
    have hfuel : Primrec fun v : ℕ => fuelOf (Nat.unpair v).2 :=
      (Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)
    have hpas : Primrec fun v : ℕ =>
        (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair v).1).1).getD [] :=
      Primrec.option_getD.comp
        (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.fst.comp Primrec.unpair)))) (Primrec.const ([] : List ℕ))
    have hext : Primrec fun v : ℕ => extOf (Nat.unpair v).2 :=
      extOf_prim.comp (Primrec.snd.comp Primrec.unpair)
    have hcode : Primrec fun v : ℕ =>
        ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 :=
      (Primrec.ofNat OracleCode).comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
    have hlen : Primrec fun v : ℕ =>
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    exact evaln_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hfuel
      (Primrec.list_append.comp hpas hext)) hcode) hlen)
  exact (Primrec.cond (Primrec.option_isSome.comp hev)
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => by
    simp only [srchTest, fuelOf]

/-- The rfind predicate for the search. -/
def srchPred (q : ℕ) : ℕ →. Bool :=
  fun w => (fun m => decide (m = 0)) <$> (Part.some (srchTest q w) : Part ℕ)

/-- The least-witness search: halts on `q` iff a witness exists. -/
noncomputable def srch (q : ℕ) : Part ℕ := Nat.rfind (srchPred q)

theorem srch_partrec : Nat.Partrec srch := by
  have h1 : Nat.Partrec (fun v : ℕ =>
      (Part.some (srchTest (Nat.unpair v).1 (Nat.unpair v).2) : Part ℕ)) :=
    Nat.Partrec.of_primrec srchTest_prim
  refine (Nat.Partrec.rfind h1).of_eq fun q => ?_
  simp only [Nat.unpair_pair]
  rfl

theorem srchPred_dom (q w : ℕ) : (srchPred q w).Dom := by
  rw [srchPred, Part.map_eq_map, Part.map_some]; trivial

theorem true_mem_srchPred (q w : ℕ) : true ∈ srchPred q w ↔ srchTest q w = 0 := by
  rw [srchPred, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    rw [Part.mem_some_iff.mp hx] at hx0
    exact of_decide_eq_true hx0
  · intro h
    exact ⟨srchTest q w, Part.mem_some _, by simp [h]⟩

theorem srch_dom (q : ℕ) : (srch q).Dom ↔ ∃ w, srchTest q w = 0 := by
  rw [srch, Nat.rfind_dom]
  constructor
  · rintro ⟨w, hw, -⟩
    exact ⟨w, (true_mem_srchPred q w).mp hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (true_mem_srchPred q w).mpr hw, fun {m} _ => srchPred_dom q m⟩

theorem srchTest_zero_iff (q w : ℕ) :
    srchTest q w = 0 ↔ (evaln (fuelOf w)
      (((Encodable.decode (α := List ℕ) (Nat.unpair q).1).getD []) ++ extOf w)
      (ofNatCode (Nat.unpair (Nat.unpair q).2).1)
      (Nat.unpair (Nat.unpair q).2).2).isSome = true := by
  rw [srchTest]
  cases (evaln (fuelOf w) _ _ _).isSome <;> simp

/-- The query encoding a `haltsAt pas e len` question. -/
def query (pasEnc e len : ℕ) : ℕ := Nat.pair pasEnc (Nat.pair e len)

/-- `srch (query …)` halts iff the construction's step-search succeeds. -/
theorem srch_query_dom (pas : List ℕ) (e len : ℕ) :
    (srch (query (Encodable.encode pas) e len)).Dom ↔ ∃ w, haltsAt pas e len w := by
  rw [srch_dom]
  have hqeq : ∀ w, srchTest (query (Encodable.encode pas) e len) w = 0 ↔
      haltsAt pas e len w := by
    intro w
    rw [srchTest_zero_iff]
    simp only [haltsAt, query, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (hqeq w).mp hw⟩, fun ⟨w, hw⟩ => ⟨w, (hqeq w).mpr hw⟩⟩

/-- **The construction's step is `0′`-decidable.** -/
theorem decision_recursiveIn_jump :
    Nat.RecursiveIn {jumpFn emptyO}
      (fun q : ℕ => ((if (srch q).Dom then 1 else 0 : ℕ) : Part ℕ)) :=
  domain_recursiveIn_jump srch_partrec.recursiveIn

/-- The search returns exactly the least witness `Nat.find` chooses. -/
theorem srch_query_eq (pas : List ℕ) (e len : ℕ)
    (h : ∃ w, haltsAt pas e len w) :
    srch (query (Encodable.encode pas) e len) = Part.some (Nat.find h) := by
  have hqeq : ∀ w, srchTest (query (Encodable.encode pas) e len) w = 0 ↔
      haltsAt pas e len w := by
    intro w
    rw [srchTest_zero_iff]
    simp only [haltsAt, query, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  rw [Part.eq_some_iff, srch]
  refine Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩
  · rw [true_mem_srchPred]
    exact (hqeq _).mpr (Nat.find_spec h)
  · rw [srchPred, Part.map_eq_map, Part.mem_map_iff]
    refine ⟨srchTest _ m, Part.mem_some _, ?_⟩
    have hnh : ¬ haltsAt pas e len m := Nat.find_min h hm
    exact decide_eq_false ((hqeq m).not.mpr hnh)

end KleenePostJump