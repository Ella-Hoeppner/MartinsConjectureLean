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
  (allBoolLists m).foldr (fun σ acc => if okb pre e σ = true then prefixN σ n else acc) []

/-- Some OK length-`m` node exists. -/
def existsOK (pre : List ℕ) (e m : ℕ) : Bool :=
  (allBoolLists m).foldr (fun σ acc => okb pre e σ || acc) false

/-- Every OK length-`m` node has `prefixN · n` equal to `pickN`. -/
def allAgree (pre : List ℕ) (e n m : ℕ) : Bool :=
  (allBoolLists m).foldr
    (fun σ acc => (!okb pre e σ || decide (prefixN σ n = pickN pre e n m)) && acc) true

/-- The level is "good": some OK node, and all OK nodes agree on `prefixN · n`. -/
def sgb (pre : List ℕ) (e n m : ℕ) : Bool := existsOK pre e m && allAgree pre e n m

theorem prefixN_prim : Primrec (fun q : List Bool × ℕ => prefixN q.1 q.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem existsOK_prim : Primrec (fun q : (List ℕ × ℕ) × ℕ => existsOK q.1.1 q.1.2 q.2) :=
  list_foldr_prim (allBoolLists_prim.comp Primrec.snd) (Primrec.const false)
    (Primrec.or.comp
      (okb_prim.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

set_option maxHeartbeats 8000000 in
theorem pickN_prim :
    Primrec (fun q : ((List ℕ × ℕ) × ℕ) × ℕ => pickN q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold pickN
  exact list_foldr_prim
    (f := fun q : ((List ℕ × ℕ) × ℕ) × ℕ => allBoolLists q.2) (base := fun _ => [])
    (op := fun q σ acc => if okb q.1.1.1 q.1.1.2 σ = true then prefixN σ q.1.2 else acc)
    (allBoolLists_prim.comp Primrec.snd) (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp (okb_prim.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))) (Primrec.const true))
      (prefixN_prim.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
      Primrec.snd)

set_option maxHeartbeats 8000000 in
theorem allAgree_prim :
    Primrec (fun q : ((List ℕ × ℕ) × ℕ) × ℕ => allAgree q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold allAgree
  exact list_foldr_prim
    (f := fun q : ((List ℕ × ℕ) × ℕ) × ℕ => allBoolLists q.2) (base := fun _ => true)
    (op := fun q σ acc =>
      (!okb q.1.1.1 q.1.1.2 σ || decide (prefixN σ q.1.2 = pickN q.1.1.1 q.1.1.2 q.1.2 q.2)) && acc)
    (allBoolLists_prim.comp Primrec.snd) (Primrec.const true)
    (Primrec.and.comp
      (Primrec.or.comp
        (Primrec.not.comp (okb_prim.comp (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))))
        (Primrec.eq.comp
          (prefixN_prim.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
            (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
          (pickN_prim.comp (Primrec.fst.comp Primrec.fst))).decide)
      Primrec.snd)

theorem sgb_prim : Primrec (fun q : ((List ℕ × ℕ) × ℕ) × ℕ => sgb q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold sgb
  exact Primrec.and.comp
    (existsOK_prim.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
    allAgree_prim

/-! ### Correctness: the primrec predicate reflects the abstract search -/

/-- Tree membership encoded in a real: `σ` is in the tree iff `Tr (treePos σ)`. -/
def treeMem (Tr : ℕ → Bool) (σ : List Bool) : Prop := Tr (treePos σ) = true

theorem graphOf_getD {f : ℕ → ℕ} {K i : ℕ} (h : i < K) : (graphOf f K).getD i 0 = f i := by
  simp only [graphOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h,
    ite_true, Option.map_some, Option.getD_some]

theorem bitg_join_even (A B : ℕ → Bool) (j : ℕ) : bitg (Cantor.join A B) (2 * j) = bitg A j := by
  simp only [bitg, Cantor.join]; rw [if_pos (by omega), show 2 * j / 2 = j by omega]

theorem bitg_join_odd (A B : ℕ → Bool) (k : ℕ) :
    bitg (Cantor.join A B) (2 * k + 1) = bitg B k := by
  simp only [bitg, Cantor.join]; rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]

theorem gxb_reflect {gx Tr : ℕ → Bool} {K j : ℕ} (h : 2 * j < K) :
    gxb (graphOf (bitg (Cantor.join gx Tr)) K) j = bitg gx j := by
  rw [gxb, graphOf_getD h, bitg_join_even]

theorem trbb_reflect {gx Tr : ℕ → Bool} {K : ℕ} {σ : List Bool} (h : 2 * treePos σ + 1 < K) :
    trbb (graphOf (bitg (Cantor.join gx Tr)) K) σ = true ↔ treeMem Tr σ := by
  simp only [trbb]
  rw [graphOf_getD h, bitg_join_odd]
  unfold bitg treeMem
  cases Tr (treePos σ) <;> simp

theorem foldr_and_all {l : List Bool} : (l.foldr (· && ·) true = true) ↔ ∀ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
      rw [ih]

/-- The bounded consistency check reflects `Consistent` when the prefix is long
enough (using `evaln_bound`: `fbit e σ j` converges only for `j < |σ|`). -/
theorem consb_reflect {gx Tr : ℕ → Bool} {K e : ℕ} {σ : List Bool} (h : 2 * σ.length ≤ K) :
    consb (graphOf (bitg (Cantor.join gx Tr)) K) e σ = true ↔ Consistent e gx σ := by
  set pre := graphOf (bitg (Cantor.join gx Tr)) K with hpre
  have hgx : ∀ j, j < σ.length → gxb pre j = bitg gx j := fun j hj => gxb_reflect (by omega)
  rw [consb, foldr_and_all]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hall j v hv
    have hjlen : j < σ.length := by
      have := evaln_bound (by simpa only [fbit] using hv); simpa only [fbit] using this
    have hc := hall j hjlen
    simp only [consBit, hgx j hjlen, decide_eq_true_eq, hv, Option.getD_some] at hc
    exact hc
  · intro hcons j hjlen
    simp only [consBit, hgx j hjlen, decide_eq_true_eq]
    cases hf : fbit e σ j with
    | none => simp
    | some v => simp only [Option.getD_some]; exact hcons j v hf

theorem foldr_or_all {l : List Bool} : (l.foldr (· || ·) false = true) ↔ ∃ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
      rw [ih]

/-- The prefix length that makes every length-`m` node's oracle positions available. -/
def bnd (m : ℕ) : ℕ := 2 ^ (m + 2) + 2

theorem bnd_bounds {σ : List Bool} {m : ℕ} (hm : σ.length = m) :
    2 * treePos σ + 1 < bnd m ∧ 2 * σ.length ≤ bnd m := by
  have ht := treePos_lt σ
  rw [hm] at ht
  have hp : m < 2 ^ m := Nat.lt_two_pow_self
  refine ⟨?_, ?_⟩
  · simp only [bnd, pow_succ] at ht ⊢; omega
  · simp only [bnd, hm, pow_succ]; omega

theorem okb_reflect {gx Tr : ℕ → Bool} {K e : ℕ} {σ : List Bool}
    (h1 : 2 * treePos σ + 1 < K) (h2 : 2 * σ.length ≤ K) :
    okb (graphOf (bitg (Cantor.join gx Tr)) K) e σ = true ↔ treeMem Tr σ ∧ Consistent e gx σ := by
  simp only [okb, Bool.and_eq_true, trbb_reflect h1, consb_reflect h2]

theorem foldr_or_mem {X : Type} (p : X → Bool) {l : List X} :
    (l.foldr (fun a acc => p a || acc) false = true) ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]; rw [ih]

theorem foldr_and_mem {X : Type} (q : X → Bool) {l : List X} :
    (l.foldr (fun a acc => q a && acc) true = true) ↔ ∀ a ∈ l, q a = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]; rw [ih]

theorem foldr_if_spec {X Y : Type} (p : X → Bool) (f : X → Y) (d : Y) :
    ∀ {l : List X}, (∃ a ∈ l, p a = true) →
      ∃ a ∈ l, p a = true ∧ l.foldr (fun a acc => if p a = true then f a else acc) d = f a := by
  intro l
  induction l with
  | nil => rintro ⟨a, ha, _⟩; exact absurd ha (by simp)
  | cons b l ih =>
      intro h
      simp only [List.foldr_cons]
      by_cases hb : p b = true
      · exact ⟨b, List.mem_cons_self, hb, if_pos hb⟩
      · rw [if_neg hb]
        obtain ⟨a, ha, hpa⟩ := h
        rcases List.mem_cons.mp ha with rfl | hal
        · exact absurd hpa hb
        · obtain ⟨a', ha', hpa', heq⟩ := ih ⟨a, hal, hpa⟩
          exact ⟨a', List.mem_cons_of_mem _ ha', hpa', heq⟩

theorem mem_allBoolLists_iff {σ : List Bool} {m : ℕ} : σ ∈ allBoolLists m ↔ σ.length = m :=
  ⟨allBoolLists_length m σ, fun h => h ▸ allBoolLists_complete σ⟩

theorem existsOK_reflect {gx Tr : ℕ → Bool} {K e m : ℕ} (hK : bnd m ≤ K) :
    existsOK (graphOf (bitg (Cantor.join gx Tr)) K) e m = true ↔
      ∃ σ, σ.length = m ∧ treeMem Tr σ ∧ Consistent e gx σ := by
  rw [existsOK, foldr_or_mem]
  constructor
  · rintro ⟨σ, hσmem, hok⟩
    have hlen := allBoolLists_length m σ hσmem
    obtain ⟨hb1, hb2⟩ := bnd_bounds hlen
    exact ⟨σ, hlen, (okb_reflect (by omega) (by omega)).mp hok⟩
  · rintro ⟨σ, hlen, habs⟩
    obtain ⟨hb1, hb2⟩ := bnd_bounds hlen
    exact ⟨σ, mem_allBoolLists_iff.mpr hlen, (okb_reflect (by omega) (by omega)).mpr habs⟩

theorem allAgree_reflect {gx Tr : ℕ → Bool} {K e n m : ℕ} (hK : bnd m ≤ K) :
    allAgree (graphOf (bitg (Cantor.join gx Tr)) K) e n m = true ↔
      ∀ σ, σ.length = m → treeMem Tr σ → Consistent e gx σ →
        prefixN σ n = pickN (graphOf (bitg (Cantor.join gx Tr)) K) e n m := by
  set pre := graphOf (bitg (Cantor.join gx Tr)) K with hpre
  rw [allAgree, foldr_and_mem]
  constructor
  · intro hall σ hlen hT hC
    obtain ⟨hb1, hb2⟩ := bnd_bounds hlen
    have hok : okb pre e σ = true := (okb_reflect (by omega) (by omega)).mpr ⟨hT, hC⟩
    have h := hall σ (mem_allBoolLists_iff.mpr hlen)
    simp only [hok, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · intro hagree σ hmem
    have hlen := allBoolLists_length m σ hmem
    obtain ⟨hb1, hb2⟩ := bnd_bounds hlen
    by_cases hok : okb pre e σ = true
    · obtain ⟨hT, hC⟩ := (okb_reflect (by omega) (by omega)).mp hok
      simp only [hok, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact hagree σ hlen hT hC
    · simp only [Bool.not_eq_true] at hok; simp [hok]

theorem pickN_spec {gx Tr : ℕ → Bool} {K e n m : ℕ}
    (h : ∃ σ ∈ allBoolLists m, okb (graphOf (bitg (Cantor.join gx Tr)) K) e σ = true) :
    ∃ σ ∈ allBoolLists m, okb (graphOf (bitg (Cantor.join gx Tr)) K) e σ = true ∧
      pickN (graphOf (bitg (Cantor.join gx Tr)) K) e n m = prefixN σ n :=
  foldr_if_spec (okb (graphOf (bitg (Cantor.join gx Tr)) K) e) (fun σ => prefixN σ n) [] h

theorem sgb_iff_searchGood {gx Tr : ℕ → Bool} {K e n m : ℕ} (hK : bnd m ≤ K) (hnm : n ≤ m) :
    sgb (graphOf (bitg (Cantor.join gx Tr)) K) e n m = true ↔
      searchGood (treeMem Tr) e gx n m := by
  set pre := graphOf (bitg (Cantor.join gx Tr)) K with hpre
  rw [sgb, Bool.and_eq_true, existsOK_reflect hK, allAgree_reflect hK, searchGood]
  constructor
  · rintro ⟨⟨σ₀, hlen₀, hT₀, hC₀⟩, hagree⟩
    refine ⟨⟨σ₀, hT₀, hlen₀, hC₀⟩, ?_⟩
    intro τ τ' hTτ hlenτ hCτ hTτ' hlenτ' hCτ'
    rw [← prefixN_eq_take (hnm.trans_eq hlenτ.symm), ← prefixN_eq_take (hnm.trans_eq hlenτ'.symm),
      hagree τ hlenτ hTτ hCτ, hagree τ' hlenτ' hTτ' hCτ']
  · rintro ⟨⟨σ₀, hT₀, hlen₀, hC₀⟩, hpairs⟩
    obtain ⟨hb0a, hb0b⟩ := bnd_bounds hlen₀
    refine ⟨⟨σ₀, hlen₀, hT₀, hC₀⟩, ?_⟩
    intro σ hlenσ hTσ hCσ
    have hex : ∃ σ ∈ allBoolLists m, okb pre e σ = true :=
      ⟨σ₀, mem_allBoolLists_iff.mpr hlen₀, (okb_reflect (by omega) (by omega)).mpr ⟨hT₀, hC₀⟩⟩
    obtain ⟨σ₁, hmem₁, hok₁, hpick⟩ := pickN_spec hex
    have hlen₁ := allBoolLists_length m σ₁ hmem₁
    obtain ⟨hb1a, hb1b⟩ := bnd_bounds hlen₁
    obtain ⟨hT₁, hC₁⟩ := (okb_reflect (by omega) (by omega)).mp hok₁
    rw [hpick, prefixN_eq_take (hnm.trans_eq hlenσ.symm), prefixN_eq_take (hnm.trans_eq hlen₁.symm)]
    exact hpairs σ σ₁ hTσ hlenσ hCσ hT₁ hlen₁ hC₁

/-! ### Oracle assembly -/

/-- `sgb` on the *encoded* prefix (`decode` composed in), for the oracle code. -/
def sgbNat (enc e n m : ℕ) : Bool := sgb ((Encodable.decode enc).getD []) e n m

set_option maxHeartbeats 8000000 in
theorem sgbNat_prim :
    Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => sgbNat w.1.1.1 w.1.1.2 w.1.2 w.2) := by
  unfold sgbNat
  have hpre : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ =>
      (Encodable.decode w.1.1.1 : Option (List ℕ)).getD []) :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const [])
  exact sgb_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hpre
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem bnd_prim : Primrec bnd :=
  Primrec.nat_add.comp (pow2_prim.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
    (Primrec.const 2)

/-- The rfind step: `0` iff `n < m` and level `m` is good (at prefix `enc`). -/
def goodTest (enc e n m : ℕ) : ℕ := bif (decide (n < m) && sgbNat enc e (n + 1) m) then 0 else 1

set_option maxHeartbeats 4000000 in
theorem goodTest_prim :
    Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => goodTest w.1.1.1 w.1.1.2 w.1.2 w.2) := by
  unfold goodTest
  have hn : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => w.1.2) := Primrec.snd.comp Primrec.fst
  have hlt : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => decide (w.1.2 < w.2)) :=
    (Primrec.nat_lt.comp hn Primrec.snd).decide
  have hsgb : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => sgbNat w.1.1.1 w.1.1.2 (w.1.2 + 1) w.2) :=
    sgbNat_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.succ.comp hn)) Primrec.snd)
  exact Primrec.cond (Primrec.and.comp hlt hsgb) (Primrec.const 0) (Primrec.const 1)

theorem goodBit_recursiveIn (O : ℕ → Bool) (e : ℕ) :
    Nat.RecursiveIn {toPFun O} (fun q =>
      ((goodTest (Encodable.encode (graphOf (bitg O) (bnd (Nat.unpair q).2))) e
        (Nat.unpair q).1 (Nat.unpair q).2 : ℕ) : Part ℕ)) := by
  have hg : Nat.RecursiveIn {toPFun O} (fun q => graphEnc O (bnd (Nat.unpair q).2)) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn O)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (bnd_prim.comp (Primrec.snd.comp Primrec.unpair))))).of_eq
      fun q => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun O} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun O}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> graphEnc O (bnd (Nat.unpair q).2)) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec (fun w => goodTest (Nat.unpair w).2 e
      (Nat.unpair (Nat.unpair w).1).1 (Nat.unpair (Nat.unpair w).1).2) :=
    Primrec.nat_iff.mp (goodTest_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair
      (Primrec.snd.comp Primrec.unpair) (Primrec.const e))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun q => ?_
  simp only [graphEnc, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]

/-- The extracted bit: `x n` (as `0/1`) read off `pickN` at level `m`. -/
def bitTest (enc e n m : ℕ) : ℕ :=
  bif ((pickN ((Encodable.decode enc).getD []) e (n + 1) m).getD n false) then 1 else 0

set_option maxHeartbeats 8000000 in
theorem bitTest_prim :
    Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => bitTest w.1.1.1 w.1.1.2 w.1.2 w.2) := by
  unfold bitTest
  have hn : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ => w.1.2) := Primrec.snd.comp Primrec.fst
  have hpre : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ =>
      (Encodable.decode w.1.1.1 : Option (List ℕ)).getD []) :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const [])
  have hpick : Primrec (fun w : ((ℕ × ℕ) × ℕ) × ℕ =>
      pickN ((Encodable.decode w.1.1.1 : Option (List ℕ)).getD []) w.1.1.2 (w.1.2 + 1) w.2) :=
    pickN_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair hpre
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.succ.comp hn)) Primrec.snd)
  exact Primrec.cond ((Primrec.list_getD false).comp hpick hn) (Primrec.const 1) (Primrec.const 0)

set_option maxHeartbeats 4000000 in
theorem extractBit_recursiveIn (O : ℕ → Bool) (e : ℕ) :
    Nat.RecursiveIn {toPFun O} (fun q =>
      ((bitTest (Encodable.encode (graphOf (bitg O) (bnd (Nat.unpair q).2))) e
        (Nat.unpair q).1 (Nat.unpair q).2 : ℕ) : Part ℕ)) := by
  have hg : Nat.RecursiveIn {toPFun O} (fun q => graphEnc O (bnd (Nat.unpair q).2)) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn O)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp
        (bnd_prim.comp (Primrec.snd.comp Primrec.unpair))))).of_eq
      fun q => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun O} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun O}
      (fun q => Nat.pair <$> ((q : ℕ) : Part ℕ) <*> graphEnc O (bnd (Nat.unpair q).2)) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec (fun w => bitTest (Nat.unpair w).2 e
      (Nat.unpair (Nat.unpair w).1).1 (Nat.unpair (Nat.unpair w).1).2) :=
    Primrec.nat_iff.mp (bitTest_prim.comp (Primrec.pair (Primrec.pair (Primrec.pair
      (Primrec.snd.comp Primrec.unpair) (Primrec.const e))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun q => ?_
  simp only [graphEnc, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]

variable {Tr : ℕ → Bool} {e : ℕ} {g : (ℕ → Bool) → (ℕ → Bool)}

theorem pickN_eq_branch (hTclosed : ∀ σ b, treeMem Tr (σ ++ [b]) → treeMem Tr σ)
    (hg : ∀ y, IsBranch (treeMem Tr) y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    (hinj : ∀ y y', IsBranch (treeMem Tr) y → IsBranch (treeMem Tr) y' → g y = g y' → y = y')
    {x : ℕ → Bool} (hx : IsBranch (treeMem Tr) x) {n m : ℕ} (hnm : n + 1 ≤ m)
    (hsgb : sgb (graphOf (bitg (Cantor.join (g x) Tr)) (bnd m)) e (n + 1) m = true) :
    pickN (graphOf (bitg (Cantor.join (g x) Tr)) (bnd m)) e (n + 1) m = (List.range (n + 1)).map x := by
  set pre := graphOf (bitg (Cantor.join (g x) Tr)) (bnd m) with hpre
  have hgood : searchGood (treeMem Tr) e (g x) (n + 1) m :=
    (sgb_iff_searchGood (le_refl _) hnm).mp hsgb
  obtain ⟨σ₀, hT₀, hlen₀, hC₀⟩ := hgood.1
  obtain ⟨hb1, hb2⟩ := bnd_bounds hlen₀
  have hex : ∃ σ ∈ allBoolLists m, okb pre e σ = true :=
    ⟨σ₀, mem_allBoolLists_iff.mpr hlen₀, (okb_reflect (by omega) (by omega)).mpr ⟨hT₀, hC₀⟩⟩
  obtain ⟨σ₁, hmem₁, hok₁, hpick⟩ := pickN_spec hex
  have hlen₁ := allBoolLists_length m σ₁ hmem₁
  obtain ⟨hb1', hb2'⟩ := bnd_bounds hlen₁
  obtain ⟨hT₁, hC₁⟩ := (okb_reflect (by omega) (by omega)).mp hok₁
  rw [hpick, prefixN_eq_take (by omega : n + 1 ≤ σ₁.length)]
  exact search_correct hg hx hnm hgood hT₁ hlen₁ hC₁

theorem bitTest_correct (hTclosed : ∀ σ b, treeMem Tr (σ ++ [b]) → treeMem Tr σ)
    (hg : ∀ y, IsBranch (treeMem Tr) y → eval (toPFun y) (ofNatCode e) = toPFun (g y))
    (hinj : ∀ y y', IsBranch (treeMem Tr) y → IsBranch (treeMem Tr) y' → g y = g y' → y = y')
    {x : ℕ → Bool} (hx : IsBranch (treeMem Tr) x) {n m : ℕ} (hnm : n < m)
    (hsgb : sgb (graphOf (bitg (Cantor.join (g x) Tr)) (bnd m)) e (n + 1) m = true) :
    bitTest (Encodable.encode (graphOf (bitg (Cantor.join (g x) Tr)) (bnd m))) e n m = bitg x n := by
  unfold bitTest
  rw [show (Encodable.decode (α := List ℕ)
      (Encodable.encode (graphOf (bitg (Cantor.join (g x) Tr)) (bnd m)))).getD []
      = graphOf (bitg (Cantor.join (g x) Tr)) (bnd m) by rw [Encodable.encodek]; rfl]
  rw [pickN_eq_branch hTclosed hg hinj hx (by omega) hsgb]
  have : ((List.range (n + 1)).map x).getD n false = x n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some]
  rw [this]; rfl

/-! ### Remaining: rfind + final theorem

`existsOK_prim` (above) shows the `||`-fold pattern compiles.  `pickN_prim`
(`cond`-fold, `List Bool`-valued) and `allAgree_prim` (which references `pickN`)
trip a Lean elaboration blow-up (runaway `whnf` in `list_foldr_prim`'s
higher-order match, even with explicit `op` / `irreducible okb` / raised
heartbeats).  The mathematically-clean fix is to make `pickN` **`ℕ`-valued**
(fold accumulating `Encodable.encode (prefixN σ n)` instead of the list — the
`ℕ`-valued fold `natOfBoolList_prim` elaborates fine) and to flatten the input
tuple; then `sgb = existsOK && allAgree`.

The reduction is then completed (all *mathematically* done, `search_computes`):
* `okb`-reflects-abstract: for `pre = graphOf (bitg (join (g x) Tr)) K` with
  `K > 2·treePos σ + 1`, `trbb pre σ = decide (Tr (treePos σ))` and (with `K > 2m`)
  `consb pre e σ = decide (Consistent e (g x) σ)` (bounded by `evaln_bound`), so
  `sgb pre e n m ↔ searchGood (treeMem Tr) e (g x) n m`;
* the reduction `fun n => decode (rfind (m ↦ sgb (graphOf … (B m)) e (n+1) m); pickN)`,
  `B m = 2^(m+2)+2`, is `RecursiveIn {toPFun (join (g x) Tr)}` via the `cGraph`
  code (prefix read) + `exists_code_of_partrec (sgb_prim)` + `Nat.RecursiveIn.rfind`;
* correct (computes `bitg x`) by `search_correct`/`search_terminates`; conclude
  `x ≤ᵀ join (g x) Tr` by `Cantor.le_iff_bitg`. -/

end Martin
