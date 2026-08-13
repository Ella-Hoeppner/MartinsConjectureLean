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

end KleenePostJump
