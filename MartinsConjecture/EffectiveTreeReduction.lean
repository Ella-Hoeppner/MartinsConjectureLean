/-
**The effective reduction for Lutz–Siskind's Lemma 2.1.**

`EffectiveTree.lean` proved the *algorithm* (`search_computes`): for a computable
injective functional `g` (code `e`) on the branches of a tree `T`, there is, for
each `n`, a level `m ≥ n` at which every consistent length-`m` node reveals `x↾n`.

Here that search is turned into an actual **Turing reduction** `x ≤ᵀ g x ⊕ T`, by
implementing it as an oracle computation: enumerate the length-`m` nodes, decide
tree-membership and consistency from the oracle, `rfind` the good level, read off
`x↾n`.

This file builds the primitive-recursive scaffolding first (node enumeration).
-/
import MartinsConjecture.EffectiveTree

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- All binary strings of length `m` (`map ++ map` form — primitive recursive). -/
def allBoolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allBoolLists m).map (false :: ·) ++ (allBoolLists m).map (true :: ·)

theorem allBoolLists_length : ∀ (m : ℕ), ∀ l ∈ allBoolLists m, l.length = m := by
  intro m
  induction m with
  | zero => intro l hl; simp only [allBoolLists, List.mem_singleton] at hl; simp [hl]
  | succ m ih =>
      intro l hl
      simp only [allBoolLists, List.mem_append, List.mem_map] at hl
      rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩ <;> simp [ih l' hl']

theorem allBoolLists_complete : ∀ (l : List Bool), l ∈ allBoolLists l.length := by
  intro l
  induction l with
  | nil => simp [allBoolLists]
  | cons b l ih =>
      simp only [List.length_cons, allBoolLists, List.mem_append, List.mem_map]
      cases b
      · exact Or.inl ⟨l, ih, rfl⟩
      · exact Or.inr ⟨l, ih, rfl⟩

theorem allBoolLists_prim : Primrec allBoolLists := by
  have h : Primrec (fun m : ℕ => Nat.rec (motive := fun _ => List (List Bool)) [[]]
      (fun _ prev => prev.map (false :: ·) ++ prev.map (true :: ·)) m) :=
    Primrec.nat_rec' Primrec.id (Primrec.const [[]])
      ((Primrec.list_append.comp
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)).to₂)
  exact h.of_eq fun m => by
    induction m with
    | zero => rfl
    | succ m ih => simp only [allBoolLists, ← ih]

/-- The number whose little-endian bits are `σ` (using `cond`, matching the
`list_rec` normal form so `natOfBoolList_prim` is clean). -/
def natOfBoolList : List Bool → ℕ
  | [] => 0
  | b :: l => (bif b then 1 else 0) + 2 * natOfBoolList l

theorem natOfBoolList_lt : ∀ σ : List Bool, natOfBoolList σ < 2 ^ σ.length
  | [] => by simp [natOfBoolList]
  | b :: l => by
      have := natOfBoolList_lt l
      simp only [natOfBoolList, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

theorem natOfBoolList_inj : ∀ {σ σ' : List Bool}, σ.length = σ'.length →
    natOfBoolList σ = natOfBoolList σ' → σ = σ'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, heq => by
      simp only [natOfBoolList] at heq
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hb : b = b' := by cases b <;> cases b' <;> simp_all <;> omega
      have hl : natOfBoolList l = natOfBoolList l' := by cases b <;> cases b' <;> simp_all <;> omega
      rw [hb, natOfBoolList_inj hlen hl]

/-- A globally-injective, `2^(len+1)`-bounded position for a binary string: the
length-`m` strings occupy `[2^m, 2^(m+1))`, so distinct lengths land in disjoint
blocks. -/
def treePos (σ : List Bool) : ℕ := 2 ^ σ.length + natOfBoolList σ

theorem treePos_lt (σ : List Bool) : treePos σ < 2 ^ (σ.length + 1) := by
  have := natOfBoolList_lt σ
  simp only [treePos, pow_succ]; omega

theorem treePos_inj {σ σ' : List Bool} (h : treePos σ = treePos σ') : σ = σ' := by
  have h1 := natOfBoolList_lt σ
  have h2 := natOfBoolList_lt σ'
  have hlen : σ.length = σ'.length := by
    by_contra hne
    rcases Nat.lt_or_ge σ.length σ'.length with hlt | hge
    · have : 2 ^ σ.length + natOfBoolList σ < 2 ^ σ'.length := by
        calc 2 ^ σ.length + natOfBoolList σ < 2 ^ σ.length + 2 ^ σ.length := by omega
          _ = 2 ^ (σ.length + 1) := by rw [pow_succ]; omega
          _ ≤ 2 ^ σ'.length := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [treePos] at h; omega
    · have hlt : σ'.length < σ.length := by omega
      have : 2 ^ σ'.length + natOfBoolList σ' < 2 ^ σ.length := by
        calc 2 ^ σ'.length + natOfBoolList σ' < 2 ^ σ'.length + 2 ^ σ'.length := by omega
          _ = 2 ^ (σ'.length + 1) := by rw [pow_succ]; omega
          _ ≤ 2 ^ σ.length := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [treePos] at h; omega
  refine natOfBoolList_inj hlen ?_
  simp only [treePos, hlen] at h; omega

/-! ### Primitive-recursive scaffolding -/

/-- `fbit` (the bit code `e` computes from the finite oracle prefix `σ`) is
primitive recursive jointly in `(e, σ, j)`. -/
theorem fbit_prim : Primrec (fun p : (ℕ × List Bool) × ℕ => fbit p.1.1 p.1.2 p.2) := by
  have hlen : Primrec (fun p : (ℕ × List Bool) × ℕ => p.1.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)
  have hmap : Primrec (fun p : (ℕ × List Bool) × ℕ => p.1.2.map bbit) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst) (bbit_prim.comp Primrec.snd)
  have hcode : Primrec (fun p : (ℕ × List Bool) × ℕ => ofNatCode p.1.1) :=
    (Primrec.ofNat OracleCode).comp (Primrec.fst.comp Primrec.fst)
  exact (OracleCode.evaln_prim.comp
    (Primrec.pair (Primrec.pair (Primrec.pair hlen hmap) hcode) Primrec.snd)).of_eq fun p => rfl

theorem natOfBoolList_prim : Primrec natOfBoolList := by
  have := Primrec.list_rec (α := List Bool) (β := Bool) (σ := ℕ) Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp
      (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂)
  exact this.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons b l ih => simp only [natOfBoolList, ← ih]; rfl

theorem pow2_prim : Primrec (fun n : ℕ => 2 ^ n) := by
  have h : Primrec (fun n : ℕ =>
      Nat.rec (motive := fun _ => ℕ) 1 (fun _ prev => 2 * prev) n) :=
    Primrec.nat_rec' Primrec.id (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ]; simp only [ih]; ring

theorem treePos_prim : Primrec treePos :=
  (Primrec.nat_add.comp (pow2_prim.comp Primrec.list_length) natOfBoolList_prim).of_eq
    fun _ => rfl

/-- `foldr (&&)` / `foldr (||)` are primitive recursive — the `all`/`any` building
blocks (Mathlib's `Primrec` has no `list_all`/`list_filter`). -/
theorem foldr_and_prim : Primrec (fun l : List Bool => l.foldr (· && ·) true) := by
  have := Primrec.list_rec (α := List Bool) (β := Bool) (σ := Bool) Primrec.id
    (Primrec.const true)
    ((Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const false)).to₂)
  exact this.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons, ← ih]; cases a <;> rfl

theorem foldr_or_prim : Primrec (fun l : List Bool => l.foldr (· || ·) false) := by
  have := Primrec.list_rec (α := List Bool) (β := Bool) (σ := Bool) Primrec.id
    (Primrec.const false)
    ((Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const true)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)
  exact this.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons, ← ih]; cases a <;> rfl

/-! ### The search predicate on an oracle prefix -/

/-- `g x`'s `j`-th bit, read from the (even part of the) oracle prefix. -/
def gxb (pre : List ℕ) (j : ℕ) : ℕ := pre.getD (2 * j) 0

/-- Consistency at bit `j`: whatever `fbit e σ j` converges to must match `g x`'s
bit (`getD` makes divergence vacuously consistent). -/
def consBit (pre : List ℕ) (e : ℕ) (σ : List Bool) (j : ℕ) : Bool :=
  decide ((fbit e σ j).getD (gxb pre j) = gxb pre j)

/-- `σ` is consistent (all converged bits match `g x`) — a bounded check. -/
def consb (pre : List ℕ) (e : ℕ) (σ : List Bool) : Bool :=
  ((List.range σ.length).map (consBit pre e σ)).foldr (· && ·) true

/-- Tree membership of `σ`, read from the (odd part of the) oracle prefix. -/
def trbb (pre : List ℕ) (σ : List Bool) : Bool :=
  decide (pre.getD (2 * treePos σ + 1) 0 = 1)

/-- `σ` is an OK node: in the tree and consistent. -/
def okb (pre : List ℕ) (e : ℕ) (σ : List Bool) : Bool := trbb pre σ && consb pre e σ

theorem consBit_prim :
    Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => consBit q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hpre : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hσ : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => q.2) := Primrec.snd
  have hgxb : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => gxb q.1.1.1 q.2) :=
    (Primrec.list_getD (0 : ℕ)).comp hpre (Primrec.nat_mul.comp (Primrec.const 2) hj)
  have hfbit : Primrec (fun q : ((List ℕ × ℕ) × List Bool) × ℕ => fbit q.1.1.2 q.1.2 q.2) :=
    fbit_prim.comp (Primrec.pair (Primrec.pair he hσ) hj)
  exact (Primrec.eq.comp (Primrec.option_getD.comp hfbit hgxb) hgxb).decide

theorem consb_prim :
    Primrec (fun q : (List ℕ × ℕ) × List Bool => consb q.1.1 q.1.2 q.2) := by
  have hmap : Primrec (fun q : (List ℕ × ℕ) × List Bool =>
      (List.range q.2.length).map (consBit q.1.1 q.1.2 q.2)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
      consBit_prim.to₂
  exact foldr_and_prim.comp hmap

theorem trbb_prim : Primrec (fun q : List ℕ × List Bool => trbb q.1 q.2) :=
  (Primrec.eq.comp
    ((Primrec.list_getD (0 : ℕ)).comp Primrec.fst
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (treePos_prim.comp Primrec.snd))
        (Primrec.const 1)))
    (Primrec.const 1)).decide

theorem okb_prim : Primrec (fun q : (List ℕ × ℕ) × List Bool => okb q.1.1 q.1.2 q.2) :=
  Primrec.and.comp
    (trbb_prim.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
    consb_prim

/-- A reusable "foldr is primitive recursive" combinator (Mathlib has `list_rec`
but no `list_foldr`). -/
theorem list_foldr_prim {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {base : α → γ} {op : α → β → γ → γ}
    (hf : Primrec f) (hbase : Primrec base)
    (hop : Primrec (fun p : (α × β) × γ => op p.1.1 p.1.2 p.2)) :
    Primrec (fun a => (f a).foldr (op a) (base a)) := by
  have := Primrec.list_rec hf hbase
    ((hop.comp (Primrec.pair (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂)
  exact this.of_eq fun a => by
    generalize f a = L
    induction L with
    | nil => rfl
    | cons b l ih => simp only [List.foldr_cons]; exact congrArg _ ih

/-! ### The level predicate -/

/-- The first `n` bits of `σ` (= `σ.take n` for `n ≤ |σ|`; primrec-friendly). -/
def prefixN (σ : List Bool) (n : ℕ) : List Bool := (List.range n).map (fun i => σ.getD i false)

theorem prefixN_eq_take {σ : List Bool} {n : ℕ} (h : n ≤ σ.length) : prefixN σ n = σ.take n := by
  apply List.ext_getElem (by simp [prefixN]; omega)
  intro i h1 h2
  simp only [prefixN, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h2; omega)]; rfl

/-- The take-`n` prefix of the first OK length-`m` node (`[]` if none). -/
def pickN (pre : List ℕ) (e n m : ℕ) : List Bool :=
  (allBoolLists m).foldr (fun σ acc => bif okb pre e σ then prefixN σ n else acc) []

/-- Some OK length-`m` node exists. -/
def existsOK (pre : List ℕ) (e m : ℕ) : Bool :=
  (allBoolLists m).foldr (fun σ acc => okb pre e σ || acc) false

/-- Every OK length-`m` node has `prefixN · n` equal to `pickN`. -/
def allAgree (pre : List ℕ) (e n m : ℕ) : Bool :=
  (allBoolLists m).foldr
    (fun σ acc => (!okb pre e σ || decide (prefixN σ n = pickN pre e n m)) && acc) true

/-- The level is "good": some OK node, and all OK nodes agree on `prefixN · n`. -/
def sgb (pre : List ℕ) (e n m : ℕ) : Bool := existsOK pre e m && allAgree pre e n m

end Martin
