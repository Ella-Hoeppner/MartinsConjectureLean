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
import MartinsConjecture.CantorLimit

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

/-- The value of a witnessed computation. -/
def valAt (pas : List ℕ) (e len w : ℕ) : ℕ :=
  (evaln (fuelOf w) (pas ++ extOf w) (ofNatCode e) len).getD 0

/-- Encoded pair of lists. -/
def encPair (a b : List ℕ) : ℕ := Nat.pair (Encodable.encode a) (Encodable.encode b)

/-- Decoded list from an encoding. -/
def decL (c : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) c).getD []

theorem decL_encode (l : List ℕ) : decL (Encodable.encode l) = l := by
  rw [decL, Encodable.encodek, Option.getD_some]

/-- The encoded step: `arg = ⟪encode act, ⟪encode pas, e⟫⟫` ↦ the encoded
`reqStep act pas e`.  On the `yes` branch it runs `srch`; the oracle branch
is selected by the `0′`-decision via the `prec`-conditional
`Nat.rec base (fun _ _ => yes) b`. -/
noncomputable def reqStepEnc (arg : ℕ) : Part ℕ :=
  ((if (srch (query (Nat.unpair (Nat.unpair arg).2).1 (Nat.unpair (Nat.unpair arg).2).2
      (decL (Nat.unpair arg).1).length)).Dom then 1 else 0 : ℕ) : Part ℕ) >>= fun b =>
    Nat.rec (Part.some (encPair (decL (Nat.unpair arg).1 ++ [0])
        (decL (Nat.unpair (Nat.unpair arg).2).1 ++ [0])))
      (fun _ _ => (srch (query (Nat.unpair (Nat.unpair arg).2).1
          (Nat.unpair (Nat.unpair arg).2).2 (decL (Nat.unpair arg).1).length)).map
        (fun w => encPair
          (decL (Nat.unpair arg).1
            ++ [diagBit (valAt (decL (Nat.unpair (Nat.unpair arg).2).1)
              (Nat.unpair (Nat.unpair arg).2).2 (decL (Nat.unpair arg).1).length w)])
          (decL (Nat.unpair (Nat.unpair arg).2).1 ++ extOf w)))
      b

/-- Correctness of the encoded step. -/
theorem reqStepEnc_spec (act pas : List ℕ) (e : ℕ) :
    reqStepEnc (Nat.pair (Encodable.encode act) (Nat.pair (Encodable.encode pas) e))
      = Part.some (encPair (reqStep act pas e).1 (reqStep act pas e).2) := by
  rw [reqStepEnc]
  simp only [Nat.unpair_pair, decL_encode]
  by_cases hh : ∃ w, haltsAt pas e act.length w
  · have hdom : (srch (query (Encodable.encode pas) e act.length)).Dom :=
      (srch_query_dom pas e act.length).mpr hh
    rw [if_pos hdom, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
    rw [srch_query_eq pas e act.length hh]
    rw [Part.map_some]
    rw [reqStep, dif_pos hh]
    rfl
  · have hdom : ¬ (srch (query (Encodable.encode pas) e act.length)).Dom :=
      fun hd => hh ((srch_query_dom pas e act.length).mp hd)
    rw [if_neg hdom, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
    show Part.some (encPair (act ++ [0]) (pas ++ [0])) = _
    rw [reqStep, dif_neg hh]


/-! ### `reqStepEnc` is recursive in `0′` -/

theorem decL_prim : Primrec decL :=
  Primrec.option_getD.comp (Primrec.decode (α := List ℕ)) (Primrec.const ([] : List ℕ))

/-- The query as a primrec function of `arg`. -/
theorem qFn_prim : Primrec (fun arg : ℕ =>
    query (Nat.unpair (Nat.unpair arg).2).1 (Nat.unpair (Nat.unpair arg).2).2
      (decL (Nat.unpair arg).1).length) := by
  unfold query
  exact Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.list_length.comp (decL_prim.comp (Primrec.fst.comp Primrec.unpair))))

theorem baseFn_prim : Primrec (fun arg : ℕ =>
    encPair (decL (Nat.unpair arg).1 ++ [0])
      (decL (Nat.unpair (Nat.unpair arg).2).1 ++ [0])) := by
  unfold encPair
  exact Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.list_append.comp
      (decL_prim.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [0])))
    (Primrec.encode.comp (Primrec.list_append.comp
      (decL_prim.comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair)))) (Primrec.const [0])))

theorem diagBit_prim : Primrec diagBit := by
  unfold diagBit
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 1) (Primrec.const 0)

/-- The `yes`-assembly on `p = ⟪arg, w⟫`. -/
def assembleFn (p : ℕ) : ℕ :=
  let arg := (Nat.unpair p).1
  let w := (Nat.unpair p).2
  encPair
    (decL (Nat.unpair arg).1
      ++ [diagBit (valAt (decL (Nat.unpair (Nat.unpair arg).2).1)
        (Nat.unpair (Nat.unpair arg).2).2 (decL (Nat.unpair arg).1).length w)])
    (decL (Nat.unpair (Nat.unpair arg).2).1 ++ extOf w)

/-- The `yes`-assembly is primitive recursive. -/
theorem assembleFn_prim : Primrec assembleFn := by
  unfold assembleFn
  have harg : Primrec fun p : ℕ => (Nat.unpair p).1 := Primrec.fst.comp Primrec.unpair
  have hw : Primrec fun p : ℕ => (Nat.unpair p).2 := Primrec.snd.comp Primrec.unpair
  have hact : Primrec fun p : ℕ => decL (Nat.unpair (Nat.unpair p).1).1 :=
    decL_prim.comp (Primrec.fst.comp (Primrec.unpair.comp harg))
  have hpas : Primrec fun p : ℕ => decL (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).1 :=
    decL_prim.comp (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp harg))))
  have he : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp harg)))
  have hev : Primrec fun p : ℕ =>
      valAt (decL (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).2
        (decL (Nat.unpair (Nat.unpair p).1).1).length (Nat.unpair p).2 := by
    unfold valAt fuelOf
    have hfuel : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair p).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp hw)
    have htable : Primrec fun p : ℕ =>
        decL (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).1 ++ extOf (Nat.unpair p).2 :=
      Primrec.list_append.comp hpas (extOf_prim.comp hw)
    have hcode : Primrec fun p : ℕ =>
        ofNatCode (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).2 :=
      (Primrec.ofNat OracleCode).comp he
    have hlen : Primrec fun p : ℕ => (decL (Nat.unpair (Nat.unpair p).1).1).length :=
      Primrec.list_length.comp hact
    exact Primrec.option_getD.comp
      (evaln_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hfuel htable) hcode) hlen))
      (Primrec.const 0)
  unfold encPair
  exact Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.list_append.comp hact
      (Primrec.list_cons.comp (diagBit_prim.comp hev) (Primrec.const []))))
    (Primrec.encode.comp (Primrec.list_append.comp hpas (extOf_prim.comp hw)))

/-- `reqStepEnc` is recursive in `0′`. -/
theorem reqStepEnc_recursiveIn : Nat.RecursiveIn {jumpFn emptyO} reqStepEnc := by
  -- abbreviations
  set qF : ℕ → ℕ := fun arg => query (Nat.unpair (Nat.unpair arg).2).1
    (Nat.unpair (Nat.unpair arg).2).2 (decL (Nat.unpair arg).1).length with hqF
  -- decision oracle at `qF arg`
  have hdec : Nat.RecursiveIn {jumpFn emptyO}
      (fun arg : ℕ => ((if (srch (qF arg)).Dom then 1 else 0 : ℕ) : Part ℕ)) :=
    (Nat.RecursiveIn.comp decision_recursiveIn_jump
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp qFn_prim))).of_eq fun arg => by
      rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  -- base branch
  have hbase : Nat.RecursiveIn {jumpFn emptyO}
      (fun arg : ℕ => ((encPair (decL (Nat.unpair arg).1 ++ [0])
        (decL (Nat.unpair (Nat.unpair arg).2).1 ++ [0]) : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp baseFn_prim)
  -- srch at `qF ((unpair p).1)`
  have hsrchp : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => srch (qF (Nat.unpair p).1)) :=
    (Nat.RecursiveIn.comp srch_partrec.recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (qFn_prim.comp (Primrec.fst.comp Primrec.unpair))))).of_eq fun p => by
      rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  -- pair `p` with the search result, then assemble
  have hstep : Nat.RecursiveIn {jumpFn emptyO} (fun p : ℕ =>
      (Nat.pair <$> ((p : ℕ) : Part ℕ) <*> srch (qF (Nat.unpair p).1))
        >>= fun pw : ℕ =>
          ((assembleFn (Nat.pair (Nat.unpair (Nat.unpair pw).1).1 (Nat.unpair pw).2) : ℕ)
            : Part ℕ)) :=
    Nat.RecursiveIn.comp
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (assembleFn_prim.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair)))))
      (Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hsrchp)
  -- the prec fold
  have hprec := Nat.RecursiveIn.prec hbase hstep
  -- pair `arg` with the decision, feed to the prec
  have hpairing : Nat.RecursiveIn {jumpFn emptyO} (fun arg : ℕ =>
      Nat.pair <$> ((arg : ℕ) : Part ℕ) <*>
        ((if (srch (qF arg)).Dom then 1 else 0 : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hdec
  have hfinal := Nat.RecursiveIn.comp hprec hpairing
  refine hfinal.of_eq fun arg => ?_
  -- reduce the pairing/comp and case on the decision
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Seq.seq,
    Part.map_eq_map, Part.map_some, Nat.unpair_pair]
  rw [reqStepEnc, hqF]
  by_cases hd : (srch (query (Nat.unpair (Nat.unpair arg).2).1
      (Nat.unpair (Nat.unpair arg).2).2 (decL (Nat.unpair arg).1).length)).Dom
  · rw [if_pos hd]
    simp [Part.bind_some, Part.bind_eq_bind, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def, Nat.unpair_pair, assembleFn]
  · rw [if_neg hd]
    simp [Part.bind_some, Part.bind_eq_bind, Nat.unpair_pair, assembleFn]

/-! ### The encoded construction is recursive in `0′`

We now show the entire finite-extension construction `cond` is recursive in
`jump ∅`, by encoding each stage's pair `(σ, τ)` as a single natural number
`encPair σ τ` and running the stage recursion with `reqStepEnc` (which is
recursive in `0′`) as the step. -/

/-- The encoded empty pair `([], [])`. -/
def baseEnc : ℕ := encPair [] []

/-- The argument fed to `reqStepEnc` at a stage: on `q = ⟪a, ⟪y, c⟫⟫` (where
`y` is the stage and `c = encPair σ τ` the current pair), builds
`⟪encode σ, ⟪encode τ, y/2⟫⟫` on even `y`, and the swapped version on odd `y`. -/
def condArg (q : ℕ) : ℕ :=
  let y := (Nat.unpair (Nat.unpair q).2).1
  let c := (Nat.unpair (Nat.unpair q).2).2
  if y % 2 = 0 then
    Nat.pair (Nat.unpair c).1 (Nat.pair (Nat.unpair c).2 (y / 2))
  else
    Nat.pair (Nat.unpair c).2 (Nat.pair (Nat.unpair c).1 (y / 2))

theorem condArg_prim : Primrec condArg := by
  unfold condArg
  have hy : Primrec fun q : ℕ => (Nat.unpair (Nat.unpair q).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hc : Primrec fun q : ℕ => (Nat.unpair (Nat.unpair q).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hc1 : Primrec fun q : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair q).2).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp hc)
  have hc2 : Primrec fun q : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair q).2).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp hc)
  have hhalf : Primrec fun q : ℕ => (Nat.unpair (Nat.unpair q).2).1 / 2 :=
    Primrec.nat_div.comp hy (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hy (Primrec.const 2)) (Primrec.const 0))
    (Primrec₂.natPair.comp hc1 (Primrec₂.natPair.comp hc2 hhalf))
    (Primrec₂.natPair.comp hc2 (Primrec₂.natPair.comp hc1 hhalf))

/-- Post-processing of `reqStepEnc`'s output at a stage: identity on even `y`,
swap the two encoded halves on odd `y`. -/
def condPost (q enc : ℕ) : ℕ :=
  if (Nat.unpair (Nat.unpair q).2).1 % 2 = 0 then enc
  else Nat.pair (Nat.unpair enc).2 (Nat.unpair enc).1

theorem condPostN_prim : Primrec (fun p : ℕ => condPost (Nat.unpair p).1 (Nat.unpair p).2) := by
  unfold condPost
  have hq : Primrec fun p : ℕ => (Nat.unpair p).1 := Primrec.fst.comp Primrec.unpair
  have henc : Primrec fun p : ℕ => (Nat.unpair p).2 := Primrec.snd.comp Primrec.unpair
  have hy : Primrec fun p : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hq)))
  have hswap : Primrec fun p : ℕ =>
      Nat.pair (Nat.unpair (Nat.unpair p).2).2 (Nat.unpair (Nat.unpair p).2).1 :=
    Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp henc))
      (Primrec.fst.comp (Primrec.unpair.comp henc))
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hy (Primrec.const 2)) (Primrec.const 0))
    henc hswap

/-- The encoded stage step: on `q = ⟪a, ⟪y, c⟫⟫`, run `reqStepEnc` and
post-process. -/
noncomputable def condStepEnc (q : ℕ) : Part ℕ :=
  (reqStepEnc (condArg q)).map (condPost q)

theorem condStepEnc_recursiveIn : Nat.RecursiveIn {jumpFn emptyO} condStepEnc := by
  have hreq : Nat.RecursiveIn {jumpFn emptyO} (fun q : ℕ => reqStepEnc (condArg q)) :=
    (Nat.RecursiveIn.comp reqStepEnc_recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp condArg_prim))).of_eq fun q => by
      rw [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hpair : Nat.RecursiveIn {jumpFn emptyO}
      (fun q : ℕ => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> reqStepEnc (condArg q)) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hreq
  have hpost : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => ((condPost (Nat.unpair p).1 (Nat.unpair p).2 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp condPostN_prim)
  refine (Nat.RecursiveIn.comp hpost hpair).of_eq fun q => ?_
  rw [condStepEnc]
  simp [Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_some, Part.bind_some,
    Part.bind_some_eq_map, Part.map_map, Function.comp_def, Nat.unpair_pair]

/-- The stage-`r` encoded pair, built by prec on `p = ⟪a, r⟫` (the `a` is a
dummy first coordinate demanded by the `prec` shape). -/
noncomputable def condRec (p : ℕ) : Part ℕ :=
  let a := (Nat.unpair p).1
  let n := (Nat.unpair p).2
  Nat.rec (((baseEnc : ℕ) : Part ℕ))
    (fun y IH => IH >>= fun i => condStepEnc (Nat.pair a (Nat.pair y i))) n

theorem condRec_recursiveIn : Nat.RecursiveIn {jumpFn emptyO} condRec := by
  have hbase : Nat.RecursiveIn {jumpFn emptyO} (fun _ : ℕ => ((baseEnc : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp (Primrec.const baseEnc))
  exact (Nat.RecursiveIn.prec hbase condStepEnc_recursiveIn).of_eq fun p => rfl

/-- The encoded stage pair, indexed by stage alone. -/
noncomputable def condN (r : ℕ) : Part ℕ := condRec (Nat.pair 0 r)

theorem condN_recursiveIn : Nat.RecursiveIn {jumpFn emptyO} condN := by
  have hpc : Nat.RecursiveIn {jumpFn emptyO} (fun r : ℕ => ((Nat.pair 0 r : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  refine (Nat.RecursiveIn.comp condRec_recursiveIn hpc).of_eq fun r => ?_
  rw [condN, Part.coe_some, Part.bind_eq_bind, Part.bind_some]

/-- `cond (r+1)` on an even stage. -/
theorem cond_succ_even (r : ℕ) (h : r % 2 = 0) :
    cond (r + 1) = reqStep (cond r).1 (cond r).2 (r / 2) := by
  simp only [cond, if_pos h]

/-- `cond (r+1)` on an odd stage. -/
theorem cond_succ_odd (r : ℕ) (h : r % 2 ≠ 0) :
    cond (r + 1) =
      ((reqStep (cond r).2 (cond r).1 (r / 2)).2, (reqStep (cond r).2 (cond r).1 (r / 2)).1) := by
  simp only [cond, if_neg h]

/-- Correctness of the encoded stage step at a real pair. -/
theorem condStepEnc_spec (a r : ℕ) :
    condStepEnc (Nat.pair a (Nat.pair r (encPair (cond r).1 (cond r).2)))
      = Part.some (encPair (cond (r + 1)).1 (cond (r + 1)).2) := by
  have hC1 : (Nat.unpair (encPair (cond r).1 (cond r).2)).1 = Encodable.encode (cond r).1 := by
    rw [encPair, Nat.unpair_pair]
  have hC2 : (Nat.unpair (encPair (cond r).1 (cond r).2)).2 = Encodable.encode (cond r).2 := by
    rw [encPair, Nat.unpair_pair]
  rw [condStepEnc, condArg]
  simp only [Nat.unpair_pair, hC1, hC2]
  by_cases hpar : r % 2 = 0
  · rw [if_pos hpar, reqStepEnc_spec, Part.map_some]
    simp only [condPost, Nat.unpair_pair, if_pos hpar]
    rw [cond_succ_even r hpar]
  · rw [if_neg hpar, reqStepEnc_spec, Part.map_some]
    simp only [condPost, Nat.unpair_pair, if_neg hpar]
    rw [cond_succ_odd r hpar, encPair, encPair, Nat.unpair_pair]

/-- **Correctness of the encoded construction**: `condN r` is total and equals
the encoded stage-`r` pair. -/
theorem condN_spec (r : ℕ) : condN r = Part.some (encPair (cond r).1 (cond r).2) := by
  rw [condN]
  induction r with
  | zero => rw [condRec]; simp only [Nat.unpair_pair]; rfl
  | succ r ih =>
    have hunf : condRec (Nat.pair 0 (r + 1))
        = condRec (Nat.pair 0 r) >>= fun i => condStepEnc (Nat.pair 0 (Nat.pair r i)) := by
      rw [condRec, condRec]; simp only [Nat.unpair_pair]
    rw [hunf, ih, Part.bind_eq_bind, Part.bind_some, condStepEnc_spec]

/-! ### The reals `A`, `B` are computable from `0′` -/

/-- Bit-extraction primrec helper: on `p = ⟪n, v⟫` with `v = encPair σ τ`,
reads `σ.getD n 0` (left) . -/
theorem bitExtractFst_prim :
    Primrec (fun p : ℕ => (decL (Nat.unpair (Nat.unpair p).2).1).getD (Nat.unpair p).1 0) :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (decL_prim.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun _ => List.getD_eq_getElem?_getD.symm

theorem bitExtractSnd_prim :
    Primrec (fun p : ℕ => (decL (Nat.unpair (Nat.unpair p).2).2).getD (Nat.unpair p).1 0) :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (decL_prim.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun _ => List.getD_eq_getElem?_getD.symm

theorem bitgA_recursiveIn :
    Nat.RecursiveIn {jumpFn emptyO} (fun n : ℕ => ((bitg A n : ℕ) : Part ℕ)) := by
  have hcond : Nat.RecursiveIn {jumpFn emptyO} (fun n : ℕ => condN (2 * (n + 1))) :=
    (Nat.RecursiveIn.comp condN_recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))))).of_eq fun n => by
      simp only [id_eq, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hpair : Nat.RecursiveIn {jumpFn emptyO}
      (fun n : ℕ => Nat.pair <$> ((n : ℕ) : Part ℕ) <*> condN (2 * (n + 1))) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hcond
  have hext : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => (((decL (Nat.unpair (Nat.unpair p).2).1).getD (Nat.unpair p).1 0 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp bitExtractFst_prim)
  refine (Nat.RecursiveIn.comp hext hpair).of_eq fun n => ?_
  rw [condN_spec]
  simp only [Part.coe_some, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_some,
    Part.bind_some, Nat.unpair_pair]
  rw [show (Nat.unpair (encPair (cond (2 * (n + 1))).1 (cond (2 * (n + 1))).2)).1
        = Encodable.encode (cond (2 * (n + 1))).1 from by rw [encPair, Nat.unpair_pair],
    decL_encode, ← bitg_A (2 * (n + 1)) n (cond_fst_len_gt n)]

theorem bitgB_recursiveIn :
    Nat.RecursiveIn {jumpFn emptyO} (fun n : ℕ => ((bitg B n : ℕ) : Part ℕ)) := by
  have hcond : Nat.RecursiveIn {jumpFn emptyO} (fun n : ℕ => condN (2 * (n + 1))) :=
    (Nat.RecursiveIn.comp condN_recursiveIn
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))))).of_eq fun n => by
      simp only [id_eq, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hpair : Nat.RecursiveIn {jumpFn emptyO}
      (fun n : ℕ => Nat.pair <$> ((n : ℕ) : Part ℕ) <*> condN (2 * (n + 1))) :=
    Nat.RecursiveIn.pair ((Primrec.nat_iff.mp Primrec.id).recursiveIn) hcond
  have hext : Nat.RecursiveIn {jumpFn emptyO}
      (fun p : ℕ => (((decL (Nat.unpair (Nat.unpair p).2).2).getD (Nat.unpair p).1 0 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.mp bitExtractSnd_prim)
  refine (Nat.RecursiveIn.comp hext hpair).of_eq fun n => ?_
  rw [condN_spec]
  simp only [Part.coe_some, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.map_some,
    Part.bind_some, Nat.unpair_pair]
  rw [show (Nat.unpair (encPair (cond (2 * (n + 1))).1 (cond (2 * (n + 1))).2)).2
        = Encodable.encode (cond (2 * (n + 1))).2 from by rw [encPair, Nat.unpair_pair],
    decL_encode, ← bitg_B (2 * (n + 1)) n (cond_snd_len_gt n)]

/-! ### The `0′`-bound, via the point representation -/

/-- The empty point of Cantor space. -/
def emptyPt : ℕ → Bool := fun _ => false

theorem toPFun_emptyPt : Cantor.toPFun emptyPt = emptyO := by
  funext n; rfl

/-- `A ≤ᵀ 0′`. -/
theorem A_le_jump : A ≤ₜ Cantor.jump emptyPt := by
  rw [Cantor.le_jump_iff_bitg, Cantor.toPFun_jump, toPFun_emptyPt]
  exact bitgA_recursiveIn

/-- `B ≤ᵀ 0′`. -/
theorem B_le_jump : B ≤ₜ Cantor.jump emptyPt := by
  rw [Cantor.le_jump_iff_bitg, Cantor.toPFun_jump, toPFun_emptyPt]
  exact bitgB_recursiveIn

/-- **The effective Kleene–Post theorem.**  There is a pair of reals, each
Turing-below `0′` (the jump of the empty set), that are Turing-incomparable. -/
theorem effective_kleene_post :
    ∃ A B : ℕ → Bool, A ≤ₜ Cantor.jump emptyPt ∧ B ≤ₜ Cantor.jump emptyPt ∧
      ¬ (A ≤ₜ B) ∧ ¬ (B ≤ₜ A) :=
  ⟨A, B, A_le_jump, B_le_jump, not_A_le_B, not_B_le_A⟩

#print axioms effective_kleene_post


end KleenePostJump