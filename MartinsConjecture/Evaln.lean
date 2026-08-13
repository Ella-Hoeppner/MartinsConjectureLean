/-
Step-indexed evaluation of oracle codes (the universal machine, part 1).

`evaln k L c n` runs code `c` on input `n` for at most `k` steps, answering
oracle queries from the finite table `L` (queries outside `L` fail).  This is
the finitary approximation of `eval`:

* `evaln_sound` — a step-bounded computation is correct: if `L` tabulates the
  oracle `toPFun X`, every `evaln` answer is an `eval` answer;
* `evaln_complete` — every converging computation is captured at some stage:
  `v ∈ eval (toPFun X) c n → ∃ k, evaln k (graphList X k) c n = some v`;
* `evaln_mono` — answers persist as fuel and oracle table grow.

Design notes: the `n ≤ k` guard makes stage `k` finitely supported (inputs
`< k`), so stage tables are finite lists — the key to the primitive
recursiveness of `evaln` (part 2).  The `rfind` case is a bounded search
(`searchList`) over an explicit value list, avoiding the `rfind'`-offset
device of Mathlib's unrelativized development.
-/
import MartinsConjecture.OracleCode

open scoped Computability
open OracleCode

namespace OracleCode

/-- Bounded μ-operator on a list of partial results: the index of the first
`some 0`, provided all earlier entries are `some (_ + 1)`; `none` if an
earlier entry is undefined or the list is exhausted. -/
def searchList : List (Option ℕ) → Option ℕ
  | [] => none
  | none :: _ => none
  | some 0 :: _ => some 0
  | some (_ + 1) :: rest => (searchList rest).map (· + 1)

theorem searchList_eq_some : ∀ {l : List (Option ℕ)} {m : ℕ},
    searchList l = some m ↔
      l[m]? = some (some 0) ∧ ∀ j < m, ∃ v, l[j]? = some (some (v + 1)) := by
  intro l
  induction l with
  | nil =>
    intro m
    simp [searchList]
  | cons hd rest ih =>
    intro m
    match hd with
    | none =>
      simp only [searchList]
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro ⟨hm, hj⟩
        rcases m with _ | m
        · simp at hm
        · obtain ⟨v, hv⟩ := hj 0 (Nat.succ_pos m)
          simp at hv
    | some 0 =>
      simp only [searchList]
      constructor
      · intro h
        rw [Option.some_inj] at h
        subst h
        exact ⟨by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · rintro ⟨hm, hj⟩
        rcases m with _ | m
        · rfl
        · obtain ⟨v, hv⟩ := hj 0 (Nat.succ_pos m)
          simp at hv
    | some (w + 1) =>
      simp only [searchList]
      constructor
      · intro h
        obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨h1, h2⟩ := ih.mp hm'
        refine ⟨by simpa using h1, fun j hj => ?_⟩
        rcases j with _ | j
        · exact ⟨w, by simp⟩
        · obtain ⟨v, hv⟩ := h2 j (by omega)
          exact ⟨v, by simpa using hv⟩
      · rintro ⟨hm, hj⟩
        rcases m with _ | m
        · simp at hm
        · rw [Option.map_eq_some_iff]
          refine ⟨m, ih.mpr ⟨by simpa using hm, fun j hj' => ?_⟩, rfl⟩
          obtain ⟨v, hv⟩ := hj (j + 1) (by omega)
          exact ⟨v, by simpa using hv⟩

/-- Step-indexed evaluation with a finite oracle table. -/
def evaln : ℕ → List ℕ → OracleCode → ℕ → Option ℕ
  | 0, _, _, _ => none
  | k + 1, L, c, n =>
    if n ≤ k then
      match c with
      | .zero => some 0
      | .succ => some (n + 1)
      | .left => some (Nat.unpair n).1
      | .right => some (Nat.unpair n).2
      | .oracle => L[n]?
      | .pair cf cg => do
          let a ← evaln (k + 1) L cf n
          let b ← evaln (k + 1) L cg n
          some (Nat.pair a b)
      | .comp cf cg => do
          let x ← evaln (k + 1) L cg n
          evaln (k + 1) L cf x
      | .prec cf cg =>
          match (Nat.unpair n).2 with
          | 0 => evaln (k + 1) L cf (Nat.unpair n).1
          | m + 1 => do
              let ih ← evaln k L (.prec cf cg) (Nat.pair (Nat.unpair n).1 m)
              evaln (k + 1) L cg (Nat.pair (Nat.unpair n).1 (Nat.pair m ih))
      | .rfind cf =>
          searchList ((List.range (k + 1)).map fun m => evaln (k + 1) L cf (Nat.pair n m))
    else none
  termination_by k _ c _ => (k, sizeOf c)

@[simp] theorem evaln_zero_fuel (L : List ℕ) (c : OracleCode) (n : ℕ) :
    evaln 0 L c n = none := by simp [evaln]

theorem evaln_bound {k : ℕ} {L : List ℕ} {c : OracleCode} {n v : ℕ}
    (h : evaln k L c n = some v) : n < k := by
  rcases k with _ | k
  · simp at h
  · by_contra hn
    cases c <;> rw [evaln, if_neg (by omega)] at h <;> exact absurd h (by simp)

/-- `eval` on a `prec` code, in recursor form (definitional). -/
theorem precEval (O : ℕ →. ℕ) (cf cg : OracleCode) (n : ℕ) :
    eval O (.prec cf cg)  n
      = Nat.rec (motive := fun _ => Part ℕ) (eval O cf (Nat.unpair n).1)
          (fun y IH => IH >>= fun i =>
            eval O cg (Nat.pair (Nat.unpair n).1 (Nat.pair y i)))
          (Nat.unpair n).2 := rfl

/-- Monotonicity: `evaln` answers persist as the fuel and the oracle table
grow. -/
theorem evaln_mono : ∀ {k k' : ℕ}, k ≤ k' → ∀ {L L' : List ℕ}, L <+: L' →
    ∀ {c : OracleCode} {n v : ℕ}, evaln k L c n = some v →
      evaln k' L' c n = some v := by
  intro k
  induction k with
  | zero =>
    intro k' _ L L' _ c n v h
    simp at h
  | succ k ihk =>
    intro k' hkk' L L' hLL' c n v
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    have hk : k ≤ k'' := by omega
    induction c generalizing n v with
    | zero =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      exact h
    | succ =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      exact h
    | left =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      exact h
    | right =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      exact h
    | oracle =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      obtain ⟨t, rfl⟩ := hLL'
      have hlen : n < L.length := (List.getElem?_eq_some_iff.mp h).choose
      rw [List.getElem?_append_left hlen]
      exact h
    | pair cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, b, hb, hv⟩ := h
      exact ⟨a, ihf ha, b, ihg hb, hv⟩
    | comp cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, hx, hv⟩ := h
      exact ⟨x, ihg hx, ihf hv⟩
    | prec cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rcases hm : (Nat.unpair n).2 with _ | m
      · rw [evaln, if_pos (by omega), hm] at h
        rw [evaln, if_pos (by omega), hm]
        exact ihf h
      · rw [evaln, if_pos (by omega), hm] at h
        rw [evaln, if_pos (by omega), hm]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨i, hi, hv⟩ := h
        exact ⟨i, ihk hk hLL' hi, ihg hv⟩
    | rfind cf ihf =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h ⊢
      rw [searchList_eq_some] at h ⊢
      obtain ⟨h0, hmin⟩ := h
      have hvk : v < k + 1 := by
        by_contra hv
        rw [List.getElem?_map,
          List.getElem?_eq_none_iff.mpr (by simpa using by omega)] at h0
        exact absurd h0 (by simp)
      rw [List.getElem?_map, List.getElem?_range hvk] at h0
      simp only [Option.map_some, Option.some_inj] at h0
      constructor
      · rw [List.getElem?_map, List.getElem?_range (show v < k'' + 1 by omega)]
        simp only [Option.map_some, Option.some_inj]
        exact ihf h0
      · intro j hj
        obtain ⟨w, hw⟩ := hmin j hj
        rw [List.getElem?_map,
          List.getElem?_range (show j < k + 1 by omega)] at hw
        simp only [Option.map_some, Option.some_inj] at hw
        refine ⟨w, ?_⟩
        rw [List.getElem?_map, List.getElem?_range (show j < k'' + 1 by omega)]
        simp only [Option.map_some, Option.some_inj]
        exact ihf hw

/-! ### Soundness -/

/-- Step-bounded answers are true answers, whenever `L` tabulates the
oracle. -/
theorem evaln_sound {O : ℕ →. ℕ} : ∀ {k : ℕ} {L : List ℕ},
    (∀ i, (hi : i < L.length) → O i = Part.some L[i]) →
    ∀ {c : OracleCode} {n v : ℕ}, evaln k L c n = some v → v ∈ eval O c n := by
  intro k
  induction k with
  | zero =>
    intro L _ c n v h
    simp at h
  | succ k ihk =>
    intro L hL c n v
    induction c generalizing n v with
    | zero =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega), Option.some_inj] at h
      subst h
      exact Part.mem_some_iff.mpr rfl
    | succ =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega), Option.some_inj] at h
      subst h
      exact Part.mem_some_iff.mpr rfl
    | left =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega), Option.some_inj] at h
      subst h
      exact Part.mem_some_iff.mpr rfl
    | right =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega), Option.some_inj] at h
      subst h
      exact Part.mem_some_iff.mpr rfl
    | oracle =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h
      obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp h
      rw [show eval O .oracle n = O n from rfl, hL n hlen]
      exact Part.mem_some_iff.mpr hval.symm
    | pair cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some_inj] at h
      obtain ⟨a, ha, b, hb, hv⟩ := h
      exact mem_eval_pair.mpr ⟨a, ihf ha, b, ihg hb, hv⟩
    | comp cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hv⟩ := h
      exact mem_eval_comp.mpr ⟨x, ihg hx, ihf hv⟩
    | prec cf cg ihf ihg =>
      intro h
      have hn := evaln_bound h
      rcases hm : (Nat.unpair n).2 with _ | m
      · rw [evaln, if_pos (by omega), hm] at h
        rw [precEval, hm]
        exact ihf h
      · rw [evaln, if_pos (by omega), hm] at h
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨i, hi, hv⟩ := h
        have hi' := ihk hL hi
        rw [precEval] at hi'
        simp only [Nat.unpair_pair] at hi'
        rw [precEval, hm]
        exact Part.mem_bind_iff.mpr ⟨i, hi', ihg hv⟩
    | rfind cf ihf =>
      intro h
      have hn := evaln_bound h
      rw [evaln, if_pos (by omega)] at h
      rw [searchList_eq_some] at h
      obtain ⟨h0, hmin⟩ := h
      have hvk : v < k + 1 := by
        by_contra hv
        rw [List.getElem?_map,
          List.getElem?_eq_none_iff.mpr (by simpa using by omega)] at h0
        exact absurd h0 (by simp)
      rw [List.getElem?_map, List.getElem?_range hvk] at h0
      simp only [Option.map_some, Option.some_inj] at h0
      refine mem_eval_rfind.mpr ⟨ihf h0, fun m hm => ?_⟩
      obtain ⟨w, hw⟩ := hmin m hm
      rw [List.getElem?_map, List.getElem?_range (show m < k + 1 by omega)] at hw
      simp only [Option.map_some, Option.some_inj] at hw
      exact ⟨w + 1, ihf hw, Nat.succ_ne_zero w⟩

/-! ### Completeness -/

/-- The graph of a total oracle, tabulated to length `k`. -/
def graphOf (g : ℕ → ℕ) (k : ℕ) : List ℕ := (List.range k).map g

@[simp] theorem graphOf_length (g : ℕ → ℕ) (k : ℕ) :
    (graphOf g k).length = k := by simp [graphOf]

theorem graphOf_prefix {g : ℕ → ℕ} : ∀ {k k' : ℕ}, k ≤ k' →
    graphOf g k <+: graphOf g k' := by
  intro k k' h
  induction k' with
  | zero =>
    rw [Nat.le_zero.mp h]
  | succ k' ih =>
    by_cases hk : k = k' + 1
    · rw [hk]
    · refine (ih (by omega)).trans ?_
      exact ⟨[g k'], by simp [graphOf, List.range_succ]⟩

theorem graphOf_sound {O : ℕ →. ℕ} {g : ℕ → ℕ}
    (hO : ∀ i, O i = Part.some (g i)) (k : ℕ) :
    ∀ i, (hi : i < (graphOf g k).length) → O i = Part.some (graphOf g k)[i] := by
  intro i hi
  rw [hO i]
  congr 1
  simp [graphOf]

/-- Completeness: every converging computation is captured at some stage,
with the oracle tabulated to the same stage. -/
theorem evaln_complete {O : ℕ →. ℕ} {g : ℕ → ℕ}
    (hO : ∀ i, O i = Part.some (g i)) :
    ∀ {c : OracleCode} {n v : ℕ}, v ∈ eval O c n →
      ∃ k, evaln k (graphOf g k) c n = some v := by
  intro c
  induction c with
  | zero =>
    intro n v h
    have hv : v = 0 := Part.mem_some_iff.mp h
    subst hv
    exact ⟨n + 1, by rw [evaln, if_pos (by omega)]⟩
  | succ =>
    intro n v h
    have hv : v = n + 1 := Part.mem_some_iff.mp h
    subst hv
    exact ⟨n + 1, by rw [evaln, if_pos (by omega)]⟩
  | left =>
    intro n v h
    have hv : v = (Nat.unpair n).1 := Part.mem_some_iff.mp h
    subst hv
    exact ⟨n + 1, by rw [evaln, if_pos (by omega)]⟩
  | right =>
    intro n v h
    have hv : v = (Nat.unpair n).2 := Part.mem_some_iff.mp h
    subst hv
    exact ⟨n + 1, by rw [evaln, if_pos (by omega)]⟩
  | oracle =>
    intro n v h
    rw [show eval O .oracle n = O n from rfl, hO n] at h
    have hv : v = g n := Part.mem_some_iff.mp h
    subst hv
    refine ⟨n + 1, ?_⟩
    rw [evaln, if_pos (by omega)]
    rw [show graphOf g (n + 1) = (List.range (n + 1)).map g from rfl,
      List.getElem?_map, List.getElem?_range (Nat.lt_succ_self n)]
    simp
  | pair cf cg ihf ihg =>
    intro n v h
    obtain ⟨a, ha, b, hb, hv⟩ := mem_eval_pair.mp h
    obtain ⟨k1, hk1⟩ := ihf ha
    obtain ⟨k2, hk2⟩ := ihg hb
    refine ⟨max k1 k2 + n + 1, ?_⟩
    rw [evaln, if_pos (by omega)]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some_inj]
    exact ⟨a, evaln_mono (by omega) (graphOf_prefix (by omega)) hk1,
      b, evaln_mono (by omega) (graphOf_prefix (by omega)) hk2, hv⟩
  | comp cf cg ihf ihg =>
    intro n v h
    obtain ⟨x, hx, hv⟩ := mem_eval_comp.mp h
    obtain ⟨k1, hk1⟩ := ihg hx
    obtain ⟨k2, hk2⟩ := ihf hv
    refine ⟨max k1 k2 + n + 1, ?_⟩
    rw [evaln, if_pos (by omega)]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
    exact ⟨x, evaln_mono (by omega) (graphOf_prefix (by omega)) hk1,
      evaln_mono (by omega) (graphOf_prefix (by omega)) hk2⟩
  | prec cf cg ihf ihg =>
    intro n v h
    rw [precEval] at h
    suffices H : ∀ (a m v : ℕ),
        v ∈ Nat.rec (motive := fun _ => Part ℕ) (eval O cf a)
          (fun y IH => IH >>= fun i =>
            eval O cg (Nat.pair a (Nat.pair y i))) m →
        ∃ k, evaln k (graphOf g k) (.prec cf cg) (Nat.pair a m) = some v by
      obtain ⟨k, hk⟩ := H (Nat.unpair n).1 (Nat.unpair n).2 v h
      rw [Nat.pair_unpair] at hk
      exact ⟨k, hk⟩
    intro a m
    induction m with
    | zero =>
      intro v h
      obtain ⟨k1, hk1⟩ := ihf h
      refine ⟨max k1 (Nat.pair a 0) + 1, ?_⟩
      rw [evaln, if_pos (by omega)]
      simp only [Nat.unpair_pair]
      exact evaln_mono (by omega) (graphOf_prefix (by omega)) hk1
    | succ m ihm =>
      intro v h
      obtain ⟨i, hi, hv⟩ := Part.mem_bind_iff.mp h
      obtain ⟨k1, hk1⟩ := ihm i hi
      obtain ⟨k2, hk2⟩ := ihg hv
      refine ⟨max (max k1 k2) (Nat.pair a (m + 1)) + 1, ?_⟩
      rw [evaln, if_pos (by omega)]
      simp only [Nat.unpair_pair]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨i, ?_, ?_⟩
      · exact evaln_mono (by omega) (graphOf_prefix (by omega)) hk1
      · exact evaln_mono (by omega) (graphOf_prefix (by omega)) hk2
  | rfind cf ihf =>
    intro n v h
    obtain ⟨h0, hmin⟩ := mem_eval_rfind.mp h
    obtain ⟨k0, hk0⟩ := ihf h0
    have key : ∀ m, ∃ km, m < v →
        ∃ w, evaln km (graphOf g km) cf (Nat.pair n m) = some (w + 1) := by
      intro m
      by_cases hm : m < v
      · obtain ⟨z, hz, hnz⟩ := hmin m hm
        obtain ⟨km, hkm⟩ := ihf hz
        obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
        exact ⟨km, fun _ => ⟨w, hkm⟩⟩
      · exact ⟨0, fun hc => absurd hc hm⟩
    choose km hkm using key
    refine ⟨max (max k0 ((Finset.range v).sup km)) (max n v) + 1, ?_⟩
    rw [evaln, if_pos (by omega)]
    rw [searchList_eq_some]
    constructor
    · rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.some_inj]
      exact evaln_mono (by omega) (graphOf_prefix (by omega)) hk0
    · intro j hj
      obtain ⟨w, hw⟩ := hkm j hj
      refine ⟨w, ?_⟩
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.some_inj]
      have hkj : km j ≤ max (max k0 ((Finset.range v).sup km)) (max n v) + 1 := by
        have := Finset.le_sup (f := km) (Finset.mem_range.mpr hj)
        omega
      exact evaln_mono hkj (graphOf_prefix hkj) hw

end OracleCode
