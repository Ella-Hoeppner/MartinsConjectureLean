/-
**`GameCodeBelow` discharged: the game even-part tree's characteristic is computable from `σ`.**

`MartinGameTree.lean` reduced *all* of Martin's Lemma 2.3 (via `lemma21`/`recover`) to the single
computability fact `GameCodeBelow : ∀ σ, codeGame σ ≤ᵀ σ`.  This file proves it.

The heart is the **emb-recursion** `embVal_le`: the functional
`embVal σ (pair m i) = evenPart (gamePlay σ (copyStrategy (join (padList m) σ))) i` — the game
embedding, uniformly over the finite padding-encoding `m` — is recursive in `σ`.  It is built by
primitive recursion on histories via the `prec` constructor of `Nat.RecursiveIn` (mirroring
`gamePlay_le`), reading `σ` at the accumulated history for player I's even moves and at `n/4` for
player II's σ-part, and the finite padding `m` (via `Encodable.decode`) for player II's z-part.

Given the emb-recursion, `codeGame σ ≤ᵀ embVal σ` follows by the graph-prefix + `Primrec` pattern of
`codeReal_le`: the bounded search `codeGame σ p` reads `embVal σ`-bits off a graph prefix of a
computable length `codeBound p` (every queried position is `< codeBound p`), and the graph search
`codeGameG` is primitive recursive.  Composing with `embVal σ ≤ᵀ σ` gives `codeGame σ ≤ᵀ σ`, i.e.
`gameCodeBelow : GameCodeBelow` — with only the standard axioms.
-/
import MartinsConjecture.MartinGameTree
import MartinsConjecture.ConeRawPPT

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- Decode a nat to a Boolean padding function (used as player II's `z`-input in
the emb-recursion). -/
def padList (m : ℕ) : ℕ → Bool :=
  fun j => ((Encodable.decode (α := List Bool) m).getD []).getD j false

/-- The emb-value indexed by an encoded pair `q = pair m i`: the even-part bit of
the play against `copyStrategy (join (padList m) σ)` at index `i`. -/
def embVal (σ : ℕ → Bool) (q : ℕ) : Bool :=
  evenPart (gamePlay σ (copyStrategy (Cantor.join (padList (Nat.unpair q).1) σ)))
    (Nat.unpair q).2

/-- The strategy used in the emb-play for padding-encoding `m`. -/
def embTau (σ : ℕ → Bool) (m : ℕ) : ℕ → Bool :=
  copyStrategy (Cantor.join (padList m) σ)

/-- The move at step `n` of the emb-play, as a 3-case formula reading `σ` and the
padding directly. -/
theorem emb_move (σ : ℕ → Bool) (m n : ℕ) :
    (if n % 2 = 0 then σ (histPlay σ (embTau σ m) n) else (embTau σ m) (histPlay σ (embTau σ m) n))
      = (if n % 2 = 0 then σ (histPlay σ (embTau σ m) n)
         else if (n / 2) % 2 = 0 then padList m (n / 4) else σ (n / 4)) := by
  by_cases hn : n % 2 = 0
  · simp only [if_pos hn]
  · simp only [if_neg hn]
    rw [embTau, copyStrategy, hlen_histPlay, Cantor.join]
    by_cases hp : (n / 2) % 2 = 0
    · simp only [if_pos hp]
      congr 1; omega
    · simp only [if_neg hp]
      congr 1; omega

/-! ### The step function's arithmetic -/

/-- Numeric selection of the move at step `y`: `A` for even, `C` for z-odd, `B`
for σ-odd; all three inputs are `0/1`. -/
def moveSel (y A B C : ℕ) : ℕ :=
  (1 - y % 2) * A + (y % 2) * ((1 - (y / 2) % 2) * C + ((y / 2) % 2) * B)

theorem moveSel_even {y A B C : ℕ} (hy : y % 2 = 0) : moveSel y A B C = A := by
  simp only [moveSel, hy]; omega

theorem moveSel_zodd {y A B C : ℕ} (hy : y % 2 = 1) (hp : (y / 2) % 2 = 0) :
    moveSel y A B C = C := by
  simp only [moveSel, hy, hp]; omega

theorem moveSel_sodd {y A B C : ℕ} (hy : y % 2 = 1) (hp : (y / 2) % 2 = 1) :
    moveSel y A B C = B := by
  simp only [moveSel, hy, hp]; omega

/-! ### The history recursion, recursive in `σ` -/

/-- The padding bit `c` at step-input `w = pair m (pair y i)`: `bbit (padList m (y/4))`. -/
def padBit (w : ℕ) : ℕ :=
  bbit (((Encodable.decode (α := List Bool) (Nat.unpair w).1).getD []).getD
    ((Nat.unpair (Nat.unpair w).2).1 / 4) false)

theorem padBit_prim : Primrec padBit := by
  unfold padBit
  refine bbit_prim.comp ?_
  refine (Primrec.list_getD false).comp ?_ ?_
  · exact Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  · exact Primrec.nat_div.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.const 4)

/-- The combining map on `v = pair w (pair a b)` (with `w = pair m (pair y i)`):
output `pair i (moveSel y a b (padBit w) + 1)`. -/
def combStep (v : ℕ) : ℕ :=
  Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2
    (moveSel (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1
        (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2
        (padBit (Nat.unpair v).1) + 1)

theorem combStep_prim : Nat.Primrec combStep := by
  refine Primrec.nat_iff.mp ?_
  have hw : Primrec (fun v : ℕ => (Nat.unpair v).1) := Primrec.fst.comp Primrec.unpair
  have hy : Primrec (fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hw)))
  have hi : Primrec (fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hw)))
  have ha : Primrec (fun v : ℕ => (Nat.unpair (Nat.unpair v).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hb : Primrec (fun v : ℕ => (Nat.unpair (Nat.unpair v).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hc : Primrec (fun v : ℕ => padBit (Nat.unpair v).1) := padBit_prim.comp hw
  -- moveSel y a b c = (1 - y%2)*a + (y%2)*((1 - (y/2)%2)*c + ((y/2)%2)*b)
  have hmod : Primrec (fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 % 2) :=
    Primrec.nat_mod.comp hy (Primrec.const 2)
  have hmod2 : Primrec (fun v : ℕ =>
      ((Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 / 2) % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hy (Primrec.const 2)) (Primrec.const 2)
  have hsel : Primrec (fun v : ℕ => moveSel
      (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1
      (Nat.unpair (Nat.unpair v).2).1
      (Nat.unpair (Nat.unpair v).2).2
      (padBit (Nat.unpair v).1)) := by
    unfold moveSel
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.nat_sub.comp (Primrec.const 1) hmod) ha)
      (Primrec.nat_mul.comp hmod
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.nat_sub.comp (Primrec.const 1) hmod2) hc)
          (Primrec.nat_mul.comp hmod2 hb)))
  exact Primrec₂.natPair.comp hi (Primrec.nat_add.comp hsel (Primrec.const 1))

/-- Extraction: `i` (accumulated history) from step-input `w = pair m (pair y i)`. -/
def gIdxI (w : ℕ) : ℕ := (Nat.unpair (Nat.unpair w).2).2
/-- Extraction: `y/4` (σ-read position) from step-input `w = pair m (pair y i)`. -/
def gIdxY4 (w : ℕ) : ℕ := (Nat.unpair (Nat.unpair w).2).1 / 4

theorem gIdxI_prim : Nat.Primrec gIdxI :=
  Primrec.nat_iff.mp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
theorem gIdxY4_prim : Nat.Primrec gIdxY4 :=
  Primrec.nat_iff.mp (Primrec.nat_div.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.const 4))

/-- The RecursiveIn step function (as a raw `ℕ →. ℕ`). -/
def histStepFn (σ : ℕ → Bool) : ℕ → Part ℕ := fun w : ℕ =>
  (Nat.pair <$> ((w : ℕ) : Part ℕ) <*>
    (Nat.pair <$> (((gIdxI w : ℕ) : Part ℕ) >>= toPFun σ)
      <*> (((gIdxY4 w : ℕ) : Part ℕ) >>= toPFun σ)))
  >>= fun v : ℕ => ((combStep v : ℕ) : Part ℕ)

theorem histStepFn_recursiveIn (σ : ℕ → Bool) :
    Nat.RecursiveIn {toPFun σ} (histStepFn σ) := by
  have hs1 : Nat.RecursiveIn {toPFun σ}
      (fun w : ℕ => ((gIdxI w : ℕ) : Part ℕ) >>= toPFun σ) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) gIdxI_prim.recursiveIn
  have hs2 : Nat.RecursiveIn {toPFun σ}
      (fun w : ℕ => ((gIdxY4 w : ℕ) : Part ℕ) >>= toPFun σ) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) gIdxY4_prim.recursiveIn
  have hid : Nat.RecursiveIn {toPFun σ} (fun w : ℕ => ((w : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hP1 : Nat.RecursiveIn {toPFun σ} (fun w : ℕ =>
      Nat.pair <$> ((w : ℕ) : Part ℕ) <*>
        (Nat.pair <$> (((gIdxI w : ℕ) : Part ℕ) >>= toPFun σ)
          <*> (((gIdxY4 w : ℕ) : Part ℕ) >>= toPFun σ))) :=
    Nat.RecursiveIn.pair hid (Nat.RecursiveIn.pair hs1 hs2)
  exact Nat.RecursiveIn.comp combStep_prim.recursiveIn hP1

/-- **The history recursion is recursive in `σ`** (raw `prec` form). -/
theorem histPrec_recursiveIn (σ : ℕ → Bool) :
    Nat.RecursiveIn {toPFun σ}
      (fun p => let (a, n) := Nat.unpair p
        n.rec (Part.some 0) fun y IH => IH >>= fun i =>
          histStepFn σ (Nat.pair a (Nat.pair y i))) := by
  have h := Nat.RecursiveIn.prec (Nat.RecursiveIn.zero (O := {toPFun σ})) (histStepFn_recursiveIn σ)
  exact h

/-- The move produced at step `y` when the accumulated history is `i` (which, in the
real recursion, equals `histPlay σ (embTau σ m) y`). -/
def embMove (σ : ℕ → Bool) (m y i : ℕ) : Bool :=
  if y % 2 = 0 then σ i else if (y / 2) % 2 = 0 then padList m (y / 4) else σ (y / 4)

/-- `combStep` on the fully-decomposed input. -/
theorem combStep_pair (m y i a b : ℕ) :
    combStep (Nat.pair (Nat.pair m (Nat.pair y i)) (Nat.pair a b))
      = Nat.pair i (moveSel y a b (bbit (padList m (y / 4))) + 1) := by
  unfold combStep padBit padList
  simp only [Nat.unpair_pair]

/-- The move arithmetic: `moveSel` on the queried `0/1` bits equals `cond (embMove) 1 0`. -/
theorem moveSel_embMove (σ : ℕ → Bool) (m y i : ℕ) :
    moveSel y (cond (σ i) 1 0) (cond (σ (y / 4)) 1 0) (bbit (padList m (y / 4)))
      = cond (embMove σ m y i) 1 0 := by
  unfold embMove
  by_cases hy : y % 2 = 0
  · rw [moveSel_even hy, if_pos hy]
  · rw [if_neg hy]
    have hy1 : y % 2 = 1 := by omega
    by_cases hp : (y / 2) % 2 = 0
    · rw [moveSel_zodd hy1 hp, if_pos hp, bbit]
    · have hp1 : (y / 2) % 2 = 1 := by omega
      rw [moveSel_sodd hy1 hp1, if_neg hp]

/-- Oracle query in the step form. -/
theorem query_val (σ : ℕ → Bool) (n : ℕ) :
    (((n : ℕ) : Part ℕ) >>= toPFun σ) = Part.some (cond (σ n) 1 0) :=
  show (Part.some n >>= toPFun σ) = Part.some (cond (σ n) 1 0) from Part.bind_some _ _

/-- **Value of the step function.** -/
theorem histStepFn_val (σ : ℕ → Bool) (m y i : ℕ) :
    histStepFn σ (Nat.pair m (Nat.pair y i))
      = Part.some (Nat.pair i (cond (embMove σ m y i) 1 0 + 1)) := by
  unfold histStepFn
  have hI : gIdxI (Nat.pair m (Nat.pair y i)) = i := by
    simp [gIdxI, Nat.unpair_pair]
  have hY : gIdxY4 (Nat.pair m (Nat.pair y i)) = y / 4 := by
    simp [gIdxY4, Nat.unpair_pair]
  rw [hI, hY, query_val, query_val]
  simp only [Part.coe_some, Seq.seq, Part.map_eq_map, Part.map_some,
    Part.bind_eq_bind, Part.bind_some]
  rw [combStep_pair, moveSel_embMove]

/-- The step move at `y` with history `= histPlay ...` equals the actual play move. -/
theorem embMove_histPlay (σ : ℕ → Bool) (m y : ℕ) :
    cond (embMove σ m y (histPlay σ (embTau σ m) y)) 1 0
      = cond (if y % 2 = 0 then σ (histPlay σ (embTau σ m) y)
              else (embTau σ m) (histPlay σ (embTau σ m) y)) 1 0 := by
  rw [emb_move σ m y]
  unfold embMove
  by_cases hy : y % 2 = 0
  · simp only [if_pos hy]
  · simp only [if_neg hy]

/-- **Value of the history recursion.** -/
theorem histRec_val (σ : ℕ → Bool) (m : ℕ) : ∀ n : ℕ,
    (Nat.rec (motive := fun _ => Part ℕ) (Part.some 0)
      (fun y IH => IH >>= fun i => histStepFn σ (Nat.pair m (Nat.pair y i))) n)
      = Part.some (histPlay σ (embTau σ m) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (Nat.rec (motive := fun _ => Part ℕ) _ _ n >>= _) = _
    rw [ih]
    rw [show (Part.some (histPlay σ (embTau σ m) n) >>=
        fun i => histStepFn σ (Nat.pair m (Nat.pair n i)))
        = histStepFn σ (Nat.pair m (Nat.pair n (histPlay σ (embTau σ m) n)))
        from Part.bind_some _ _]
    rw [histStepFn_val, embMove_histPlay, histPlay]

/-- `embVal σ q` is `σ` applied to the history at the even index `2·(unpair q).2`. -/
theorem embVal_eq (σ : ℕ → Bool) (q : ℕ) :
    embVal σ q = σ (histPlay σ (embTau σ (Nat.unpair q).1) (2 * (Nat.unpair q).2)) := by
  unfold embVal evenPart embTau gamePlay
  rw [if_pos (by omega)]

/-- The prec-then-bind, at input `q`, computes the history at `2·(unpair q).2`. -/
theorem histPrec_at (σ : ℕ → Bool) (q : ℕ) :
    (((Nat.pair (Nat.unpair q).1 (2 * (Nat.unpair q).2) : ℕ) : Part ℕ)
      >>= fun p => let (a, k) := Nat.unpair p
        k.rec (Part.some 0) fun y IH => IH >>= fun i =>
          histStepFn σ (Nat.pair a (Nat.pair y i)))
    = Part.some (histPlay σ (embTau σ (Nat.unpair q).1) (2 * (Nat.unpair q).2)) := by
  have hb : (((Nat.pair (Nat.unpair q).1 (2 * (Nat.unpair q).2) : ℕ) : Part ℕ)
      >>= fun p => let (a, k) := Nat.unpair p
        k.rec (Part.some 0) fun y IH => IH >>= fun i =>
          histStepFn σ (Nat.pair a (Nat.pair y i)))
    = ((fun p => let (a, k) := Nat.unpair p
        k.rec (Part.some 0) fun y IH => IH >>= fun i =>
          histStepFn σ (Nat.pair a (Nat.pair y i)))
        (Nat.pair (Nat.unpair q).1 (2 * (Nat.unpair q).2))) := Part.bind_some _ _
  rw [hb]
  simp only [Nat.unpair_pair]
  exact histRec_val σ (Nat.unpair q).1 (2 * (Nat.unpair q).2)

/-- **The emb-value is recursive in `σ`.**  `embVal σ q = σ(histPlay σ (embTau σ m) (2i))`
with `q = pair m i`, packaged as the bit-graph query so it is `≤ᵀ σ`. -/
theorem embVal_le (σ : ℕ → Bool) :
    Nat.RecursiveIn {toPFun σ} (fun q : ℕ => ((bitg (embVal σ) q : ℕ) : Part ℕ)) := by
  have hprec := histPrec_recursiveIn σ
  have hin : Nat.RecursiveIn {toPFun σ}
      (fun q : ℕ => ((Nat.pair (Nat.unpair q).1 (2 * (Nat.unpair q).2) : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair)))).recursiveIn
  have hH := Nat.RecursiveIn.comp hprec hin
  have horacle : Nat.RecursiveIn {toPFun σ} (toPFun σ) := Nat.RecursiveIn.oracle _ rfl
  have hquery := Nat.RecursiveIn.comp horacle hH
  refine hquery.of_eq fun q => ?_
  show (((Nat.pair (Nat.unpair q).1 (2 * (Nat.unpair q).2) : ℕ) : Part ℕ)
      >>= fun p => let (a, k) := Nat.unpair p
        k.rec (Part.some 0) fun y IH => IH >>= fun i =>
          histStepFn σ (Nat.pair a (Nat.pair y i)))
    >>= toPFun σ = _
  rw [histPrec_at,
    show (Part.some (histPlay σ (embTau σ (Nat.unpair q).1) (2 * (Nat.unpair q).2)) >>= toPFun σ)
      = toPFun σ (histPlay σ (embTau σ (Nat.unpair q).1) (2 * (Nat.unpair q).2))
      from Part.bind_some _ _]
  rw [toPFun, ← embVal_eq σ q]
  rfl

/-! ### `codeGame σ ≤ᵀ embVal σ ≤ᵀ σ` via the graph search -/

/-- `padOf zp` (the finite padding used in `evenMatchGame`) is `padList (encode zp)`. -/
theorem padOf_eq_padList (zp : List Bool) :
    (fun j => zp.getD j false) = padList (Encodable.encode zp) := by
  funext j
  unfold padList
  rw [Encodable.encodek, Option.getD_some]

/-- The even-match test's read is exactly an `embVal` query. -/
theorem evenMatch_read (σ : ℕ → Bool) (zp : List Bool) (i : ℕ) :
    evenPart (gamePlay σ (copyStrategy (Cantor.join (fun j => zp.getD j false) σ))) i
      = embVal σ (Nat.pair (Encodable.encode zp) i) := by
  unfold embVal
  rw [Nat.unpair_pair, padOf_eq_padList]

/-- `evenMatchGame` rewritten as `embVal` queries. -/
theorem evenMatchGame_embVal (σ : ℕ → Bool) (s : List Bool) :
    evenMatchGame σ s
      = (allBoolLists (2 * s.length)).any fun zp =>
          (List.range s.length).all fun i =>
            embVal σ (Nat.pair (Encodable.encode zp) i) == s.getD i false := by
  unfold evenMatchGame
  congr 1
  funext zp
  congr 1
  funext i
  rw [evenMatch_read]

/-- Generic: a value produced by an element of the list is `≤` the `max`-`foldr`. -/
theorem foldr_max_mem {α : Type} (f : α → ℕ) {l : List α} {a : α} (ha : a ∈ l) :
    f a ≤ l.foldr (fun x acc => max (f x) acc) 0 := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact le_max_left _ _
    · exact le_trans (ih hmem) (le_max_right _ _)

/-- Flat list of every `embVal`-position `codeGame σ p` can query. -/
def candPos (p : ℕ) : List ℕ :=
  (List.range (p + 1)).flatMap fun L =>
    (allBoolLists (2 * L)).flatMap fun zp =>
      (List.range L).map fun i => Nat.pair (Encodable.encode zp) i

theorem mem_candPos (p L : ℕ) (hL : L ∈ List.range (p + 1))
    (zp : List Bool) (hzp : zp ∈ allBoolLists (2 * L)) (i : ℕ) (hi : i ∈ List.range L) :
    Nat.pair (Encodable.encode zp) i ∈ candPos p := by
  unfold candPos
  rw [List.mem_flatMap]
  exact ⟨L, hL, by
    rw [List.mem_flatMap]
    exact ⟨zp, hzp, List.mem_map.mpr ⟨i, hi, rfl⟩⟩⟩

/-- The computable bound: every `embVal`-position queried by `codeGame σ p` is `< codeBound p`. -/
def codeBound (p : ℕ) : ℕ :=
  (candPos p).foldr (fun q acc => max (q + 1) acc) 0

theorem codeBound_spec (p L : ℕ) (hL : L ∈ List.range (p + 1))
    (zp : List Bool) (hzp : zp ∈ allBoolLists (2 * L)) (i : ℕ) (hi : i ∈ List.range L) :
    Nat.pair (Encodable.encode zp) i < codeBound p := by
  have := foldr_max_mem (fun q => q + 1) (mem_candPos p L hL zp hzp i hi)
  simpa [codeBound] using this

/-! ### Graph search versions -/

/-- `List.all` respects agreement of the predicate on list members. -/
theorem list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp only [List.all_cons, h b (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `List.any` respects agreement of the predicate on list members. -/
theorem list_any_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp only [List.any_cons, h b (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Graph-prefix even-match test: reads `embVal σ (pair (encode zp) i)` off the graph `g`. -/
def evenMatchGameG (g : List ℕ) (s : List Bool) : Bool :=
  (allBoolLists (2 * s.length)).any fun zp =>
    (List.range s.length).all fun i =>
      (g.getD (Nat.pair (Encodable.encode zp) i) 0 == bbit (s.getD i false))

/-- Graph-prefix version of the game coding real. -/
def codeGameG (g : List ℕ) (p : ℕ) : Bool :=
  (List.range (p + 1)).foldr (fun L acc =>
    ((allBoolLists L).foldr (fun s acc2 =>
      ((treePos s == p) && evenMatchGameG g s) || acc2) false) || acc) false

/-- On a long-enough graph prefix, the graph even-match agrees with the real one. -/
theorem evenMatchGameG_eq (σ : ℕ → Bool) (s : List Bool) {K : ℕ}
    (hK : ∀ zp ∈ allBoolLists (2 * s.length), ∀ i ∈ List.range s.length,
      Nat.pair (Encodable.encode zp) i < K) :
    evenMatchGameG (graphOf (bitg (embVal σ)) K) s = evenMatchGame σ s := by
  rw [evenMatchGame_embVal]
  unfold evenMatchGameG
  refine list_any_congr (fun zp hzp => ?_)
  refine list_all_congr (fun i hi => ?_)
  rw [graphOf_getD (hK zp hzp i hi), bitg_eq_bbit]
  cases embVal σ (Nat.pair (Encodable.encode zp) i) <;> cases s.getD i false <;> rfl

/-- On the graph prefix of length `codeBound p`, the graph search computes `codeGame σ p`. -/
theorem codeGameG_eq (σ : ℕ → Bool) (p : ℕ) :
    codeGameG (graphOf (bitg (embVal σ)) (codeBound p)) p = codeGame σ p := by
  unfold codeGameG codeGame
  refine foldr_or_congr (fun L hL => ?_)
  refine foldr_or_congr (fun s hs => ?_)
  have hslen : s.length = L := allBoolLists_length L s hs
  rw [evenMatchGameG_eq σ s (K := codeBound p) (fun zp hzp i hi => ?_)]
  rw [hslen] at hzp hi
  exact codeBound_spec p L hL zp hzp i hi

/-! ### Primitive recursiveness of the graph search -/

/-- `List.any` as an explicit `foldr` (bridge to `list_foldr_prim`). -/
theorem any_eq_foldr {α : Type} (l : List α) (p : α → Bool) :
    l.any p = l.foldr (fun a acc => p a || acc) false := by
  induction l with
  | nil => rfl
  | cons b t ih => simp only [List.any_cons, List.foldr_cons, ih]

/-- `List.all` as an explicit `foldr`. -/
theorem all_eq_foldr {α : Type} (l : List α) (p : α → Bool) :
    l.all p = l.foldr (fun a acc => p a && acc) true := by
  induction l with
  | nil => rfl
  | cons b t ih => simp only [List.all_cons, List.foldr_cons, ih]

theorem candPos_prim : Primrec candPos := by
  unfold candPos
  have hmid : Primrec₂ (fun (pL : ℕ × ℕ) (zp : List Bool) =>
      (List.range pL.2).map fun i => Nat.pair (Encodable.encode zp) i) := by
    have hL : Primrec (fun r : (ℕ × ℕ) × List Bool => r.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hzp : Primrec (fun r : (ℕ × ℕ) × List Bool => r.2) := Primrec.snd
    have hg : Primrec₂ (fun (r : (ℕ × ℕ) × List Bool) (i : ℕ) =>
        Nat.pair (Encodable.encode r.2) i) :=
      Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact (Primrec.list_map (Primrec.list_range.comp hL) hg).to₂
  have houter : Primrec₂ (fun (p : ℕ) (L : ℕ) =>
      (allBoolLists (2 * L)).flatMap fun zp =>
        (List.range L).map fun i => Nat.pair (Encodable.encode zp) i) := by
    have hf : Primrec (fun r : ℕ × ℕ => allBoolLists (2 * r.2)) :=
      allBoolLists_prim.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    exact (Primrec.list_flatMap hf hmid).to₂
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) houter

theorem codeBound_prim : Primrec codeBound := by
  unfold codeBound
  refine list_foldr_prim candPos_prim (Primrec.const 0) ?_
  exact Primrec.nat_max.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd

/-- `evenMatchGameG` in explicit `foldr` form (bridge to `list_foldr_prim`). -/
theorem evenMatchGameG_foldr (g : List ℕ) (s : List Bool) :
    evenMatchGameG g s
      = (allBoolLists (2 * s.length)).foldr (fun zp acc =>
          ((List.range s.length).foldr (fun i acc2 =>
            (g.getD (Nat.pair (Encodable.encode zp) i) 0 == bbit (s.getD i false)) && acc2)
            true) || acc)
          false := by
  unfold evenMatchGameG
  rw [any_eq_foldr]
  congr 1
  funext zp acc
  rw [all_eq_foldr]

set_option maxHeartbeats 4000000 in
theorem evenMatchGameG_prim :
    Primrec (fun q : List ℕ × List Bool => evenMatchGameG q.1 q.2) := by
  have hfun : (fun q : List ℕ × List Bool => evenMatchGameG q.1 q.2)
      = fun q : List ℕ × List Bool =>
          (allBoolLists (2 * q.2.length)).foldr (fun zp acc =>
            ((List.range q.2.length).foldr (fun i acc2 =>
              (q.1.getD (Nat.pair (Encodable.encode zp) i) 0 == bbit (q.2.getD i false)) && acc2)
              true) || acc)
            false := by
    funext q; exact evenMatchGameG_foldr q.1 q.2
  rw [hfun]
  -- inner foldr over range |s|, function of `((g, s), zp)`
  have hinner : Primrec (fun r : (List ℕ × List Bool) × List Bool =>
      (List.range r.1.2.length).foldr (fun i acc2 =>
        (r.1.1.getD (Nat.pair (Encodable.encode r.2) i) 0 == bbit (r.1.2.getD i false)) && acc2)
        true) := by
    refine list_foldr_prim
      (f := fun r : (List ℕ × List Bool) × List Bool => List.range r.1.2.length)
      (base := fun _ => true)
      (op := fun r i acc2 =>
        (r.1.1.getD (Nat.pair (Encodable.encode r.2) i) 0 == bbit (r.1.2.getD i false)) && acc2)
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.const true) ?_
    have hg : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool => t.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hs : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool => t.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hzp : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool => t.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hi : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool => t.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hpos : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool =>
        Nat.pair (Encodable.encode t.1.1.2) t.1.2) :=
      Primrec₂.natPair.comp (Primrec.encode.comp hzp) hi
    have hread : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool =>
        t.1.1.1.1.getD (Nat.pair (Encodable.encode t.1.1.2) t.1.2) 0) :=
      (Primrec.list_getD 0).comp hg hpos
    have hbit : Primrec (fun t : (((List ℕ × List Bool) × List Bool) × ℕ) × Bool =>
        bbit (t.1.1.1.2.getD t.1.2 false)) :=
      bbit_prim.comp ((Primrec.list_getD false).comp hs hi)
    exact Primrec.and.comp (primrec_beq hread hbit) Primrec.snd
  refine list_foldr_prim
    (f := fun q : List ℕ × List Bool => allBoolLists (2 * q.2.length))
    (base := fun _ => false)
    (op := fun q zp acc =>
      ((List.range q.2.length).foldr (fun i acc2 =>
        (q.1.getD (Nat.pair (Encodable.encode zp) i) 0 == bbit (q.2.getD i false)) && acc2)
        true) || acc)
    (allBoolLists_prim.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.snd)))
    (Primrec.const false) ?_
  exact Primrec.or.comp
    (hinner.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
    Primrec.snd

set_option maxHeartbeats 4000000 in
theorem codeGameG_prim : Primrec (fun q : List ℕ × ℕ => codeGameG q.1 q.2) := by
  unfold codeGameG
  have hinner : Primrec (fun r : (List ℕ × ℕ) × ℕ =>
      (allBoolLists r.2).foldr (fun s acc2 =>
        ((treePos s == r.1.2) && evenMatchGameG r.1.1 s) || acc2) false) := by
    refine list_foldr_prim
      (f := fun r : (List ℕ × ℕ) × ℕ => allBoolLists r.2) (base := fun _ => false)
      (op := fun r s acc2 => ((treePos s == r.1.2) && evenMatchGameG r.1.1 s) || acc2)
      (allBoolLists_prim.comp Primrec.snd) (Primrec.const false) ?_
    have hg : Primrec (fun t : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => t.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hp : Primrec (fun t : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => t.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hs : Primrec (fun t : (((List ℕ × ℕ) × ℕ) × List Bool) × Bool => t.1.2) :=
      Primrec.snd.comp Primrec.fst
    exact Primrec.or.comp
      (Primrec.and.comp (primrec_beq (treePos_prim.comp hs) hp)
        (evenMatchGameG_prim.comp (Primrec.pair hg hs))) Primrec.snd
  exact list_foldr_prim
    (f := fun q : List ℕ × ℕ => List.range (q.2 + 1)) (base := fun _ => false)
    (op := fun q L acc =>
      ((allBoolLists L).foldr (fun s acc2 =>
        ((treePos s == q.2) && evenMatchGameG q.1 s) || acc2) false) || acc)
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) (Primrec.const false)
    (Primrec.or.comp
      (hinner.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

/-! ### The reduction `codeGame σ ≤ᵀ embVal σ ≤ᵀ σ` -/

/-- `embVal σ ≤ᵀ σ` (from the emb-recursion in bit-graph form). -/
theorem embVal_reduces (σ : ℕ → Bool) : embVal σ ≤ₜ σ :=
  Cantor.le_iff_bitg.mpr (embVal_le σ)

/-- **`codeGame σ ≤ᵀ embVal σ`.**  The oracle reads its own graph-prefix of length
`codeBound p` and runs the (primitive recursive) graph search `codeGameG`. -/
theorem codeGame_le_embVal (σ : ℕ → Bool) : codeGame σ ≤ₜ embVal σ := by
  rw [Cantor.le_iff_bitg]
  have hg : Nat.RecursiveIn {toPFun (embVal σ)} (fun p => graphEnc (embVal σ) (codeBound p)) :=
    (Nat.RecursiveIn.comp (graphEnc_recursiveIn (embVal σ))
      (Nat.Primrec.recursiveIn (Primrec.nat_iff.mp codeBound_prim))).of_eq
      fun p => by simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {toPFun (embVal σ)} (fun p : ℕ => ((p : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hpair : Nat.RecursiveIn {toPFun (embVal σ)}
      (fun p => Nat.pair <$> ((p : ℕ) : Part ℕ) <*> graphEnc (embVal σ) (codeBound p)) :=
    Nat.RecursiveIn.pair hid hg
  have htest : Nat.Primrec (fun w => bbit (codeGameG
      ((Encodable.decode (α := List ℕ) (Nat.unpair w).2).getD []) (Nat.unpair w).1)) :=
    Primrec.nat_iff.mp (bbit_prim.comp (codeGameG_prim.comp (Primrec.pair
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
        (Primrec.const []))
      (Primrec.fst.comp Primrec.unpair))))
  refine (Nat.RecursiveIn.comp htest.recursiveIn hpair).of_eq fun p => ?_
  simp only [graphEnc, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_some,
    Part.coe_some, Nat.unpair_pair]
  rw [show (Encodable.decode (α := List ℕ)
      (Encodable.encode (graphOf (bitg (embVal σ)) (codeBound p)))).getD []
      = graphOf (bitg (embVal σ)) (codeBound p) by rw [Encodable.encodek]; rfl]
  rw [codeGameG_eq, bitg_eq_bbit]

/-- **`codeGame σ ≤ᵀ σ`** — the remaining computability fact behind `GameCodeBelow`. -/
theorem codeGame_le (σ : ℕ → Bool) : codeGame σ ≤ₜ σ :=
  (codeGame_le_embVal σ).trans (embVal_reduces σ)

/-- **`GameCodeBelow` is a theorem.** -/
theorem gameCodeBelow : GameCodeBelow := fun σ => codeGame_le σ

/-! ### Capstones: `GameCodeBelow` is discharged, so the Martin-game route no longer carries it -/

/-- **Martin's Lemma 2.3 (`MartinPPT`), machine-checked modulo *only* determinacy of the
Martin games.**  With `gameCodeBelow` proved, `martinPPT_of_codeBelow` no longer carries the
computability hypothesis: every cofinal set contains a pointed perfect tree, provided only that
the asymmetric Martin games are determined.  Every recursion-theoretic ingredient — the game,
`winsI_martinGame_of_cofinal`, `emb_locality`, `exists_z_of_branch`, the `codeGame` tree and
`lemma21`/`recover`, and now `codeGame σ ≤ᵀ σ` itself — is proved. -/
theorem martinPPT_of_gameDeterminacy
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) : MartinPPT :=
  martinPPT_of_codeBelow gameCodeBelow hdet

/-- **Part 1 of Martin's conjecture via the Martin game, with `GameCodeBelow` discharged.**
Part 1 holds given determinacy of the Martin games, Turing determinacy, and `escaping ⟹ MP` —
the last being the *only* genuinely-open input (the incomparable core).  The entire Martin
Lemma 2.3 / MartinPPT / Theorem 3.4 pipeline is now machine-checked. -/
theorem partI_of_gameDeterminacy_escaping
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_codeBelow_escaping gameCodeBelow hdet hTD hesc

#print axioms gameCodeBelow
#print axioms martinPPT_of_gameDeterminacy
#print axioms partI_of_gameDeterminacy_escaping

end Martin
