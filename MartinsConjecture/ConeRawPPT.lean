/-
**The `Y`-coding tree in the `treeMem` coding.**

`ConeTree.lean` built the pointed / realizing / perfect content of the cone tree
abstractly (`CodedBranch Y = {join Y Z}`).  To obtain a genuine `RawPPT` — and
hence, via `RawPPT.toPPT`/`lemma21`, the effective `recover` field — the tree must
be presented in the `treeMem` coding used by `lemma21`: a characteristic real
`codeReal Y` whose branches are exactly the even-`Y` reals.

This file supplies the *combinatorial* reflection (`treeMem_codeReal`,
`closed_codeReal`, `isBranch_codeReal`), reducing a full invariant `RawPPT` to the
single recursion-theoretic fact `codeReal Y ≡ᵀ Y`.
-/
import MartinsConjecture.RawPPT
import MartinsConjecture.ConeTree

open scoped Computability
open Cantor OracleCode
open Classical

namespace Martin

/-- `σ`'s even positions spell the prefix of `Y`. -/
def EvenMatch (Y : ℕ → Bool) (σ : List Bool) : Prop :=
  ∀ k, 2 * k < σ.length → σ.getD (2 * k) false = Y k

/-- Boolean even-match test, over the positions of `σ` (`foldr` form, so it is
directly primitive recursive via `foldr_and_mem`/`list_foldr_prim`). -/
def evenMatchB (Y : ℕ → Bool) (σ : List Bool) : Bool :=
  (List.range σ.length).foldr
    (fun i acc => (!(i % 2 == 0) || (σ.getD i false == Y (i / 2))) && acc) true

theorem evenMatchB_iff (Y : ℕ → Bool) (σ : List Bool) :
    evenMatchB Y σ = true ↔ EvenMatch Y σ := by
  unfold evenMatchB EvenMatch
  rw [foldr_and_mem]
  constructor
  · intro h k hk
    have := h (2 * k) (by simp only [List.mem_range]; omega)
    simp only [Nat.mul_mod_right, beq_self_eq_true, Bool.not_true, Bool.false_or,
      beq_iff_eq] at this
    rwa [show 2 * k / 2 = k by omega] at this
  · intro h i hi
    simp only [List.mem_range] at hi
    rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hget : (σ.getD (k + k) false == Y ((k + k) / 2)) = true := by
        rw [beq_iff_eq, show (k + k) / 2 = k by omega, show k + k = 2 * k by omega]
        exact h k (by omega)
      simp only [hget, Bool.or_true]
    · rw [show (2 * k + 1) % 2 = 1 by omega]; rfl

/-- **Finite use of the even-match test.**  `evenMatchB Y σ` reads `Y` only at
positions `< σ.length`, so agreeing prefixes of `Y` give the same test.  This is
the mathematical seed of `codeReal · ≤ᵀ ·` (the test, hence the coding real, is
computable from a finite prefix of `Y`). -/
theorem evenMatchB_congr {Y Y' : ℕ → Bool} {σ : List Bool}
    (h : ∀ j, 2 * j < σ.length → Y j = Y' j) : evenMatchB Y σ = evenMatchB Y' σ := by
  have hiff : EvenMatch Y σ ↔ EvenMatch Y' σ := by
    constructor <;> intro hEM k hk
    · rw [← h k hk]; exact hEM k hk
    · rw [h k hk]; exact hEM k hk
  cases hY : evenMatchB Y σ <;> cases hY' : evenMatchB Y' σ <;>
    first
      | rfl
      | (rw [evenMatchB_iff] at hY; rw [Bool.eq_false_iff, ne_eq, evenMatchB_iff] at hY';
         exact absurd (hiff.mp hY) hY')
      | (rw [evenMatchB_iff] at hY'; rw [Bool.eq_false_iff, ne_eq, evenMatchB_iff] at hY;
         exact absurd (hiff.mpr hY') hY)

/-- Characteristic real of the even-`Y` coding tree: at `treePos σ` it records
whether `σ`'s even positions match `Y`, found by a bounded search over the finite
strings.  Constructive (so its computability from `Y` is reachable); off the range
of `treePos` it is `false`, which is irrelevant since `treeMem` reads only
`treePos` positions. -/
def codeReal (Y : ℕ → Bool) (p : ℕ) : Bool :=
  (List.range (p + 1)).foldr
    (fun L acc =>
      ((allBoolLists L).foldr
        (fun σ acc2 => ((treePos σ == p) && evenMatchB Y σ) || acc2) false) || acc)
    false

/-- The search evaluates the even-match test at the (unique) string coded by
`treePos σ`. -/
theorem codeReal_treePos (Y : ℕ → Bool) (σ : List Bool) :
    codeReal Y (treePos σ) = evenMatchB Y σ := by
  unfold codeReal
  have hlen : σ.length < treePos σ + 1 := by
    have := Nat.lt_two_pow_self (n := σ.length)
    unfold treePos; omega
  cases hem : evenMatchB Y σ with
  | true =>
    rw [foldr_or_mem]
    exact ⟨σ.length, by simp only [List.mem_range]; omega, by
      rw [foldr_or_mem]
      exact ⟨σ, allBoolLists_complete σ, by simp [hem]⟩⟩
  | false =>
    rw [Bool.eq_false_iff, ne_eq, foldr_or_mem]
    rintro ⟨L, _, hL⟩
    rw [foldr_or_mem] at hL
    obtain ⟨σ', _, hσ'⟩ := hL
    simp only [Bool.and_eq_true, beq_iff_eq] at hσ'
    obtain ⟨hpos, hev⟩ := hσ'
    have : σ' = σ := treePos_inj hpos
    subst this; rw [hem] at hev; exact Bool.false_ne_true hev

/-- Membership in the coding tree is exactly the even-match predicate. -/
theorem treeMem_codeReal (Y : ℕ → Bool) (σ : List Bool) :
    treeMem (codeReal Y) σ ↔ EvenMatch Y σ := by
  unfold treeMem
  rw [codeReal_treePos, evenMatchB_iff]

/-- **Finite use of the coding real.**  `codeReal Y p` depends only on `Y` below
`p`: the only string the search can match at `treePos σ = p` has length `< p`, so
the even-match test there reads `Y` only below `p`.  This is exactly the use
property behind `codeReal Y ≤ᵀ Y` (the coding real is computable from `Y`); the
remaining step to a Turing reduction is the (bulky, `lemma21`-scale) `Primrec`
presentation of the search reading an oracle graph-prefix. -/
theorem codeReal_use {Y Y' : ℕ → Bool} {p : ℕ}
    (h : ∀ j, 2 * j < p → Y j = Y' j) : codeReal Y p = codeReal Y' p := by
  unfold codeReal
  have hpred : (fun (σ : List Bool) (acc2 : Bool) =>
                 ((treePos σ == p) && evenMatchB Y σ) || acc2)
             = (fun σ acc2 => ((treePos σ == p) && evenMatchB Y' σ) || acc2) := by
    funext σ acc2
    have hσ : ((treePos σ == p) && evenMatchB Y σ)
            = ((treePos σ == p) && evenMatchB Y' σ) := by
      by_cases hp : treePos σ = p
      · have hlt : σ.length < treePos σ := by
          have := Nat.lt_two_pow_self (n := σ.length); unfold treePos; omega
        rw [evenMatchB_congr (fun j hj => h j (by omega))]
      · rw [beq_eq_false_iff_ne.mpr hp, Bool.false_and, Bool.false_and]
    rw [hσ]
  simp only [hpred]

/-- The coding tree is downward closed. -/
theorem closed_codeReal (Y : ℕ → Bool) :
    ∀ σ b, treeMem (codeReal Y) (σ ++ [b]) → treeMem (codeReal Y) σ := by
  intro σ b h
  rw [treeMem_codeReal] at h ⊢
  intro k hk
  have hk' : 2 * k < (σ ++ [b]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hval := h k hk'
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk] at hval
  rw [List.getD_eq_getElem?_getD]
  exact hval

/-- A real is a branch of the coding tree iff its even bits spell `Y` — i.e. iff
it is `join Y Z` for some `Z` (`CodedBranch Y`). -/
theorem isBranch_codeReal (Y : ℕ → Bool) (x : ℕ → Bool) :
    IsBranch (treeMem (codeReal Y)) x ↔ CodedBranch Y x := by
  simp only [IsBranch, treeMem_codeReal]
  constructor
  · intro h
    -- every even bit of `x` equals the corresponding bit of `Y`
    have heven : ∀ k, x (2 * k) = Y k := by
      intro k
      have hmatch := h (2 * k + 1) k (by
        simp only [List.length_map, List.length_range]; omega)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega), Option.map_some, Option.getD_some] at hmatch
    refine ⟨fun k => x (2 * k + 1), ?_⟩
    funext n
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [Cantor.join, if_pos (by omega), show (k + k) / 2 = k by omega,
        show k + k = 2 * k by omega]
      exact heven k
    · rw [Cantor.join, if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
  · rintro ⟨Z, rfl⟩ n k hk
    simp only [List.length_map, List.length_range] at hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some, Cantor.join,
      if_pos (by omega), show 2 * k / 2 = k by omega]

/-! ### The Turing reduction `codeReal Y ≤ᵀ Y`

`codeReal Y p` is computed by the same bounded search, but reading the bits of `Y`
off an oracle graph-prefix `g = graphOf (bitg Y) K` instead of `Y` directly.  This
graph version is primitive recursive, so the reduction assembles as
`graphEnc`-then-`Primrec`, exactly as in `goodBit_recursiveIn`. -/

/-- `foldr`-with-`&&` respects pointwise equality of the head function on the list. -/
theorem foldr_and_congr {f g : ℕ → Bool} {l : List ℕ} (h : ∀ a ∈ l, f a = g a) :
    l.foldr (fun a acc => f a && acc) true = l.foldr (fun a acc => g a && acc) true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.foldr_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `foldr`-with-`||` respects pointwise equality of the head function on the list. -/
theorem foldr_or_congr {α : Type} {f g : α → Bool} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    l.foldr (fun a acc => f a || acc) false = l.foldr (fun a acc => g a || acc) false := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.foldr_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem bbit_beq (a b : Bool) : (bbit a == bbit b) = (a == b) := by
  cases a <;> cases b <;> rfl

/-- Graph-prefix version of the even-match test: reads `Y (i/2)` as the `i/2`-th
entry of an oracle graph-prefix. -/
def evenMatchG (g : List ℕ) (σ : List Bool) : Bool :=
  (List.range σ.length).foldr
    (fun i acc => (!(i % 2 == 0) || (bbit (σ.getD i false) == g.getD (i / 2) 0)) && acc) true

/-- On a long-enough prefix, the graph version agrees with `evenMatchB`. -/
theorem evenMatchG_eq (Y : ℕ → Bool) (σ : List Bool) {K : ℕ} (hK : σ.length ≤ K) :
    evenMatchG (graphOf (bitg Y) K) σ = evenMatchB Y σ := by
  unfold evenMatchG evenMatchB
  refine foldr_and_congr (fun i hi => ?_)
  simp only [List.mem_range] at hi
  have hik : i / 2 < K := by omega
  rw [graphOf_getD hik, bitg_eq_bbit, bbit_beq]

/-- Graph-prefix version of the coding real. -/
def codeG (g : List ℕ) (p : ℕ) : Bool :=
  (List.range (p + 1)).foldr
    (fun L acc =>
      ((allBoolLists L).foldr
        (fun σ acc2 => ((treePos σ == p) && evenMatchG g σ) || acc2) false) || acc)
    false

/-- On the prefix of length `p + 1`, the graph version computes `codeReal Y p`
(every string the search visits has length `≤ p`, so its even-match reads are
covered). -/
theorem codeG_eq (Y : ℕ → Bool) (p : ℕ) :
    codeG (graphOf (bitg Y) (p + 1)) p = codeReal Y p := by
  unfold codeG codeReal
  refine foldr_or_congr (fun L hL => ?_)
  simp only [List.mem_range] at hL
  refine foldr_or_congr (fun σ hσ => ?_)
  have hlen : σ.length = L := allBoolLists_length L σ hσ
  rw [evenMatchG_eq Y σ (K := p + 1) (by omega)]

/-- `ℕ`-`BEq` is primitive recursive (bridge to `Primrec.eq`). -/
theorem primrec_beq {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => (f x == g x)) :=
  ((Primrec.eq.comp hf hg).decide).of_eq (fun x => (beq_eq_decide (f x) (g x)).symm)

theorem evenMatchG_prim : Primrec (fun q : List ℕ × List Bool => evenMatchG q.1 q.2) := by
  unfold evenMatchG
  refine list_foldr_prim (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
    (Primrec.const true) ?_
  have hg : Primrec (fun p : ((List ℕ × List Bool) × ℕ) × Bool => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hσ : Primrec (fun p : ((List ℕ × List Bool) × ℕ) × Bool => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hi : Primrec (fun p : ((List ℕ × List Bool) × ℕ) × Bool => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hnot : Primrec (fun p : ((List ℕ × List Bool) × ℕ) × Bool => !(p.1.2 % 2 == 0)) :=
    Primrec.not.comp (primrec_beq (Primrec.nat_mod.comp hi (Primrec.const 2)) (Primrec.const 0))
  have hbeq : Primrec (fun p : ((List ℕ × List Bool) × ℕ) × Bool =>
      (bbit (p.1.1.2.getD p.1.2 false) == p.1.1.1.getD (p.1.2 / 2) 0)) :=
    primrec_beq (bbit_prim.comp ((Primrec.list_getD false).comp hσ hi))
      ((Primrec.list_getD 0).comp hg (Primrec.nat_div.comp hi (Primrec.const 2)))
  exact Primrec.and.comp (Primrec.or.comp hnot hbeq) Primrec.snd

set_option maxHeartbeats 8000000 in
theorem codeG_prim : Primrec (fun q : List ℕ × ℕ => codeG q.1 q.2) := by
  unfold codeG
  -- inner foldr over `allBoolLists L`, as a function of `((g, p), L)`
  have hinner : Primrec (fun r : (List ℕ × ℕ) × ℕ =>
      (allBoolLists r.2).foldr
        (fun σ acc2 => ((treePos σ == r.1.2) && evenMatchG r.1.1 σ) || acc2) false) := by
    refine list_foldr_prim
      (f := fun r : (List ℕ × ℕ) × ℕ => allBoolLists r.2) (base := fun _ => false)
      (op := fun r σ acc2 => ((treePos σ == r.1.2) && evenMatchG r.1.1 σ) || acc2)
      (allBoolLists_prim.comp Primrec.snd) (Primrec.const false) ?_
    have hg : Primrec (fun s : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => s.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hp : Primrec (fun s : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => s.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hσ : Primrec (fun s : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => s.1.2) :=
      Primrec.snd.comp Primrec.fst
    exact Primrec.or.comp
      (Primrec.and.comp (primrec_beq (treePos_prim.comp hσ) hp)
        (evenMatchG_prim.comp (Primrec.pair hg hσ))) Primrec.snd
  exact list_foldr_prim
    (f := fun q : List ℕ × ℕ => List.range (q.2 + 1)) (base := fun _ => false)
    (op := fun q L acc =>
      ((allBoolLists L).foldr
        (fun σ acc2 => ((treePos σ == q.2) && evenMatchG q.1 σ) || acc2) false) || acc)
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) (Primrec.const false)
    (Primrec.or.comp
      (hinner.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

/-- **`codeReal Y ≤ᵀ Y`.**  The oracle reads its own graph-prefix of length `p+1`
and runs the (primitive recursive) graph search `codeG`. -/
theorem codeReal_le (Y : ℕ → Bool) : codeReal Y ≤ₜ Y := by
  rw [Cantor.le_iff_bitg]
  have hg : Nat.RecursiveIn {toPFun Y} (fun p => graphEnc Y (p + 1)) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn Y)
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp Primrec.succ))).of_eq
      fun p => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun Y} (fun p : ℕ => ((p : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun Y}
      (fun p => Nat.pair <$> ((p : ℕ) : Part ℕ) <*> graphEnc Y (p + 1)) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec (fun w => bbit (codeG
      ((Encodable.decode (α := List ℕ) (Nat.unpair w).2).getD []) (Nat.unpair w).1)) :=
    Primrec.nat_iff.mp (bbit_prim.comp (codeG_prim.comp (Primrec.pair
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const []))
      (Primrec.fst.comp Primrec.unpair))))
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun p => ?_
  simp only [graphEnc, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]
  rw [show (Encodable.decode (α := List ℕ)
      (Encodable.encode (graphOf (bitg Y) (p + 1)))).getD [] = graphOf (bitg Y) (p + 1) by
    rw [Encodable.encodek]; rfl]
  rw [codeG_eq, bitg_eq_bbit]

/-! ### The Turing reduction `Y ≤ᵀ codeReal Y`

To recover `Y k`, search the length-`2k+1` strings for one in the tree (read off
the oracle's graph-prefix) and take its bit `2k`: any in-tree string of that
length has its even bits equal to `Y`, and the even-`Y` prefix witnesses that one
exists. -/

/-- Search the length-`2k+1` strings for one in the tree (`h.getD (treePos σ) = 1`)
and return its `2k`-th bit. -/
def recoverBit (h : List ℕ) (k : ℕ) : Bool :=
  (allBoolLists (2 * k + 1)).foldr
    (fun σ acc => if (h.getD (treePos σ) 0 == 1) = true then σ.getD (2 * k) false else acc) false

set_option maxHeartbeats 8000000 in
theorem recoverBit_prim : Primrec (fun q : List ℕ × ℕ => recoverBit q.1 q.2) := by
  unfold recoverBit
  exact list_foldr_prim
    (f := fun q : List ℕ × ℕ => allBoolLists (2 * q.2 + 1)) (base := fun _ => false)
    (op := fun q σ acc =>
      if (q.1.getD (treePos σ) 0 == 1) = true then σ.getD (2 * q.2) false else acc)
    (allBoolLists_prim.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)))
    (Primrec.const false)
    (Primrec.ite
      (Primrec.eq.comp
        (primrec_beq
          ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (treePos_prim.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.const 1))
        (Primrec.const true))
      ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst)
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)

/-- Given `codeReal Y ≡ᵀ Y`, the even-`Y` coding tree is a genuine `RawPPT`. -/
noncomputable def coneRawPPT (Y : ℕ → Bool) (hequiv : codeReal Y ≡ₜ Y) : RawPPT where
  code := codeReal Y
  closed := closed_codeReal Y
  pointed := by
    intro x hx
    rw [isBranch_codeReal] at hx
    obtain ⟨Z, rfl⟩ := hx
    exact hequiv.1.trans (Cantor.left_le_join Y Z)
  realizes := by
    intro d hd
    have hYd : Y ≤ₜ d := hequiv.2.trans hd
    refine ⟨Cantor.join Y d, ?_, ?_⟩
    · rw [isBranch_codeReal]; exact ⟨d, rfl⟩
    · exact ⟨Cantor.join_le hYd (Cantor.le.refl d), Cantor.right_le_join Y d⟩

/-- **Full invariant Martin Lemma 2.3, modulo `codeReal · ≡ᵀ ·`.**  If the coding
real is Turing-equivalent to its parameter (a pure computability fact), then every
Turing-invariant cofinal determined set contains a *full* pointed perfect tree — a
`PPT` with the effective `recover` field supplied by `lemma21` — whose branches
lie in the set. -/
theorem invariant_cofinal_contains_PPT
    (hcode : ∀ Y : ℕ → Bool, codeReal Y ≡ₜ Y)
    (A : Set (ℕ → Bool)) (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hcof : Cofinal (· ∈ A)) (hDet : GameDetermined A) :
    ∃ T : PPT, ∀ x, T.mem x → x ∈ A := by
  obtain ⟨Y, hY⟩ := cone_of_invariant_cofinal A hTI hcof hDet
  refine ⟨(coneRawPPT Y (hcode Y)).toPPT, fun x hx => ?_⟩
  -- `T.mem` unfolds to `IsBranch (treeMem (codeReal Y))`, i.e. `CodedBranch Y`
  have : CodedBranch Y x := (isBranch_codeReal Y x).mp hx
  exact hY (coneEmbedding_pointed Y x this)

#print axioms treeMem_codeReal
#print axioms isBranch_codeReal
#print axioms invariant_cofinal_contains_PPT

end Martin
