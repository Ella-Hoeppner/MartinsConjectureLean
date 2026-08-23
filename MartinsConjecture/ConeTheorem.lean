/-
Martin's cone theorem, with determinacy as an explicit hypothesis.

We formalize Gale–Stewart games on `2^ω` directly: positions are histories,
encoded as iterated `Nat.pair`-chains (`histPlay`), and a strategy for either
player is a function `ℕ → Bool` from encoded histories to moves.  Player I
moves at even positions, player II at odd positions.  Payoff sets
`A ⊆ (ℕ → Bool)` are judged on the full play `gamePlay σ τ : ℕ → Bool`.

**No determinacy is provable from current Mathlib** (Borel determinacy exists
only in Sven Manthe's external repository), so determinacy of the payoff set
is taken as an explicit *hypothesis* `GameDetermined A` — never an axiom.

Main result (`cone_theorem`): if `A` is Turing invariant and determined, then
`A` contains a cone or is disjoint from a cone.  The cone base is the winning
strategy itself, viewed as a point of Cantor space; this is Martin's original
argument.  The computational heart is `gamePlay_le`: the play against the
"copy `Y`" opponent is computable from `Y` together with any strategy
recursive in `Y`, proved by primitive recursion on histories via the `prec`
constructor of `Nat.RecursiveIn`.
-/
import MartinsConjecture.Martin

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Games on Cantor space -/

/-- The (encoded) history of the game after `n` moves, when player I follows
`σ` and player II follows `τ`.  A history is an iterated-pair chain; move
bits are stored shifted by one so that no nonempty history is encoded by `0`. -/
def histPlay (σ τ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    Nat.pair (histPlay σ τ n)
      (cond (if n % 2 = 0 then σ (histPlay σ τ n) else τ (histPlay σ τ n)) 1 0 + 1)

/-- The infinite play produced by strategies `σ` (player I, even positions)
and `τ` (player II, odd positions). -/
def gamePlay (σ τ : ℕ → Bool) (n : ℕ) : Bool :=
  if n % 2 = 0 then σ (histPlay σ τ n) else τ (histPlay σ τ n)

/-- `σ` is a winning strategy for player I in the game with payoff `A`. -/
def WinsI (A : Set (ℕ → Bool)) (σ : ℕ → Bool) : Prop := ∀ τ, gamePlay σ τ ∈ A

/-- `τ` is a winning strategy for player II in the game with payoff `A`. -/
def WinsII (A : Set (ℕ → Bool)) (τ : ℕ → Bool) : Prop := ∀ σ, gamePlay σ τ ∉ A

/-- The game with payoff `A` is determined. -/
def GameDetermined (A : Set (ℕ → Bool)) : Prop :=
  (∃ σ, WinsI A σ) ∨ ∃ τ, WinsII A τ

/-- Length of an encoded history (chain depth). -/
def hlen (h : ℕ) : ℕ :=
  if h0 : h = 0 then 0
  else
    have : (Nat.unpair h).1 < h := Nat.unpair_lt (by omega)
    hlen (Nat.unpair h).1 + 1

/-- The strategy that ignores the opponent and plays out the bits of `Y`
(at position `n` it plays `Y (n / 2)`, its own move counter). -/
def copyStrategy (Y : ℕ → Bool) : ℕ → Bool := fun h => Y (hlen h / 2)

theorem histPlay_ne_zero (σ τ : ℕ → Bool) (n : ℕ) : histPlay σ τ (n + 1) ≠ 0 := by
  intro h
  have h1 := congrArg Nat.unpair h
  rw [histPlay, Nat.unpair_pair] at h1
  have h2 := congrArg Prod.snd h1
  simp [Nat.unpair_zero] at h2

theorem hlen_histPlay (σ τ : ℕ → Bool) : ∀ n, hlen (histPlay σ τ n) = n
  | 0 => by rw [histPlay]; rw [hlen]; simp
  | n + 1 => by
    rw [hlen, dif_neg (histPlay_ne_zero σ τ n)]
    simp only [histPlay, Nat.unpair_pair]
    exact congrArg Nat.succ (hlen_histPlay σ τ n)

theorem gamePlay_copy_odd (σ Y : ℕ → Bool) (n : ℕ) (hn : n % 2 = 1) :
    gamePlay σ (copyStrategy Y) n = Y (n / 2) := by
  rw [gamePlay, if_neg (by omega), copyStrategy, hlen_histPlay]

theorem gamePlay_copy_even (τ Y : ℕ → Bool) (n : ℕ) (hn : n % 2 = 0) :
    gamePlay (copyStrategy Y) τ n = Y (n / 2) := by
  rw [gamePlay, if_pos hn, copyStrategy, hlen_histPlay]

/-! ### The play is computable from the opponent's real -/

/-- **Computability of the play.**  Suppose that in `gamePlay σ τ`, moves at
positions of parity `e` are the bits of `Y` (in order), while moves at the
other parity are given by a strategy `ρ` recursive in `Y`.  Then the whole
play is recursive in `Y`.  Proved by primitive recursion on histories using
the `prec` constructor of `Nat.RecursiveIn`. -/
theorem gamePlay_le (e : ℕ) (σ τ ρ Y : ℕ → Bool)
    (hρ : ρ ≤ₜ Y)
    (hstrat : ∀ n, n % 2 ≠ e % 2 →
      (if n % 2 = 0 then σ (histPlay σ τ n) else τ (histPlay σ τ n))
        = ρ (histPlay σ τ n))
    (hYq : ∀ n, n % 2 = e % 2 →
      (if n % 2 = 0 then σ (histPlay σ τ n) else τ (histPlay σ τ n))
        = Y (n / 2)) :
    gamePlay σ τ ≤ₜ Y := by
  refine RecursiveIn.iff_nat.mpr ?_
  obtain ⟨cρ, hcρ⟩ := exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp hρ)
  -- Extraction functions on step inputs `q = pair a (pair y i)`
  -- (`y` = step counter, `i` = accumulated history).
  set g1 : ℕ → ℕ := fun q => (Nat.unpair (Nat.unpair q).2).2 with hg1
  set g2 : ℕ → ℕ := fun q => (Nat.unpair (Nat.unpair q).2).1 / 2 with hg2
  -- Parity indicator `d y = 1` iff `y % 2 = e % 2`.
  set d : ℕ → ℕ := fun y => 1 - ((y % 2 - e % 2) + (e % 2 - y % 2)) with hd
  -- Combining map on `w = pair q (pair s t)`:
  -- output `pair i ((1 - d y) * s + d y * t + 1)`.
  set comb : ℕ → ℕ := fun w =>
    Nat.pair (g1 (Nat.unpair w).1)
      ((1 - d (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1)
          * (Nat.unpair (Nat.unpair w).2).1
        + d (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1
          * (Nat.unpair (Nat.unpair w).2).2 + 1) with hcomb
  have hg1P : Nat.Primrec g1 := Primrec.nat_iff.mp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hg2P : Nat.Primrec g2 := Primrec.nat_iff.mp
    (Primrec.nat_div.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.const 2))
  have hdP : Primrec d := by
    rw [hd]
    exact Primrec.nat_sub.comp (Primrec.const 1)
      (Primrec.nat_add.comp
        (Primrec.nat_sub.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
          (Primrec.const (e % 2)))
        (Primrec.nat_sub.comp (Primrec.const (e % 2))
          (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))))
  have hcombP : Nat.Primrec comb := by
    rw [hcomb]
    refine Primrec.nat_iff.mp ?_
    have hq : Primrec fun w : ℕ => (Nat.unpair w).1 := Primrec.fst.comp Primrec.unpair
    have hy : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hq)))
    have hs : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have ht : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    exact Primrec₂.natPair.comp
      ((Primrec.nat_iff.mpr hg1P).comp hq)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp
            (Primrec.nat_sub.comp (Primrec.const 1) (hdP.comp hy)) hs)
          (Primrec.nat_mul.comp (hdP.comp hy) ht))
        (Primrec.const 1))
  -- Step function, via the `Nat.RecursiveIn` constructors.
  have hs1 : Nat.RecursiveIn {toPFun Y}
      (fun q : ℕ => ((g1 q : ℕ) : Part ℕ) >>= eval (toPFun Y) cρ) :=
    Nat.RecursiveIn.comp (eval_recursiveIn (toPFun Y) cρ) hg1P.recursiveIn
  have hs2 : Nat.RecursiveIn {toPFun Y}
      (fun q : ℕ => ((g2 q : ℕ) : Part ℕ) >>= toPFun Y) :=
    Nat.RecursiveIn.comp (.oracle _ rfl) hg2P.recursiveIn
  have hid : Nat.RecursiveIn {toPFun Y} (fun q : ℕ => ((q : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hP1 : Nat.RecursiveIn {toPFun Y} (fun q : ℕ =>
      Nat.pair <$> ((q : ℕ) : Part ℕ) <*>
        (Nat.pair <$> (((g1 q : ℕ) : Part ℕ) >>= eval (toPFun Y) cρ)
          <*> (((g2 q : ℕ) : Part ℕ) >>= toPFun Y))) :=
    Nat.RecursiveIn.pair hid (Nat.RecursiveIn.pair hs1 hs2)
  have hstep : Nat.RecursiveIn {toPFun Y} (fun q : ℕ =>
      (Nat.pair <$> ((q : ℕ) : Part ℕ) <*>
        (Nat.pair <$> (((g1 q : ℕ) : Part ℕ) >>= eval (toPFun Y) cρ)
          <*> (((g2 q : ℕ) : Part ℕ) >>= toPFun Y)))
      >>= fun v : ℕ => ((comb v : ℕ) : Part ℕ)) :=
    Nat.RecursiveIn.comp hcombP.recursiveIn hP1
  have hprec := Nat.RecursiveIn.prec (Nat.RecursiveIn.zero (O := {toPFun Y})) hstep
  have hpair0 : Nat.RecursiveIn {toPFun Y}
      (fun n : ℕ => ((Nat.pair 0 (n + 1) : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.succ)).recursiveIn
  have hG := Nat.RecursiveIn.comp hprec hpair0
  set extr : ℕ → ℕ := fun w => (Nat.unpair w).2 - 1 with hextr
  have hextrP : Nat.Primrec extr := Primrec.nat_iff.mp
    (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))
  have hF := Nat.RecursiveIn.comp hextrP.recursiveIn hG
  -- Value computation.
  -- The parity-combination arithmetic, shared by the two value lemmas below.
  have harith : ∀ n : ℕ,
      (1 - d n) * cond (ρ (histPlay σ τ n)) 1 0 + d n * cond (Y (n / 2)) 1 0
        = cond (if n % 2 = 0 then σ (histPlay σ τ n) else τ (histPlay σ τ n)) 1 0 := by
    intro n
    by_cases hm : n % 2 = e % 2
    · rw [hYq n hm]
      have hdm : d n = 1 := by simp only [hd]; omega
      rw [hdm]
      omega
    · rw [hstrat n hm]
      have hdm : d n = 0 := by simp only [hd]; omega
      rw [hdm]
      omega
  -- Step values (stated in `Part.some`/`.bind` normal form):
  have hstepVal : ∀ a y i : ℕ,
      ((Nat.pair <$> Part.some (Nat.pair a (Nat.pair y i)) <*>
        (Nat.pair <$> (Part.some (g1 (Nat.pair a (Nat.pair y i)))
            >>= eval (toPFun Y) cρ)
          <*> (Part.some (g2 (Nat.pair a (Nat.pair y i))) >>= toPFun Y))).bind
      fun v : ℕ => Part.some (comb v))
      = Part.some (Nat.pair i
          ((1 - d y) * cond (ρ i) 1 0 + d y * cond (Y (y / 2)) 1 0 + 1)) := by
    intro a y i
    have e1 : g1 (Nat.pair a (Nat.pair y i)) = i := by
      simp [hg1, Nat.unpair_pair]
    have e2 : g2 (Nat.pair a (Nat.pair y i)) = y / 2 := by
      simp [hg2, Nat.unpair_pair]
    rw [e1, e2, hcρ,
      show (Part.some i >>= toPFun ρ) = toPFun ρ i from Part.bind_some _ _,
      show (Part.some (y / 2) >>= toPFun Y) = toPFun Y (y / 2) from Part.bind_some _ _]
    simp only [toPFun, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind,
      Part.bind_some]
    simp only [hcomb, Nat.unpair_pair, e1]
  -- The primitive recursion computes the history:
  have hRval : ∀ m : ℕ,
      (Nat.rec (motive := fun _ => Part ℕ) (0 : Part ℕ)
        (fun y IH => IH.bind fun i =>
          (Nat.pair <$> Part.some (Nat.pair 0 (Nat.pair y i)) <*>
            (Nat.pair <$> (Part.some (g1 (Nat.pair 0 (Nat.pair y i)))
                >>= eval (toPFun Y) cρ)
              <*> (Part.some (g2 (Nat.pair 0 (Nat.pair y i))) >>= toPFun Y))).bind
          fun v : ℕ => Part.some (comb v)) m)
      = Part.some (histPlay σ τ m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      show (Nat.rec (motive := fun _ => Part ℕ) _ _ m).bind _ = _
      rw [ih, Part.bind_some, hstepVal 0 m (histPlay σ τ m)]
      rw [histPlay, ← harith m]
  -- Conclude by rewriting the assembled derivation to `toPFun (gamePlay σ τ)`.
  refine hF.of_eq fun n => ?_
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair,
    Nat.rec_add_one]
  rw [hRval n, Part.bind_some, hstepVal 0 n (histPlay σ τ n), Part.bind_some]
  simp only [hextr, Nat.unpair_pair, Nat.add_sub_cancel]
  rw [toPFun, gamePlay, ← harith n]

/-! ### Martin's cone theorem -/

/-- **Martin's cone theorem** (with determinacy as an explicit hypothesis).
If `A ⊆ 2^ω` is Turing invariant and the associated game is determined, then
`A` contains a cone or is disjoint from a cone.  The cone base is the winning
strategy itself. -/
theorem cone_theorem (A : Set (ℕ → Bool))
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hDet : GameDetermined A) :
    (∃ Y, cone Y ⊆ A) ∨ ∃ Y, cone Y ⊆ Aᶜ := by
  rcases hDet with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · left
    refine ⟨σ, fun X hX => ?_⟩
    have hZle : gamePlay σ (copyStrategy X) ≤ₜ X := by
      refine gamePlay_le 1 σ (copyStrategy X) σ X hX (fun n hn => ?_) (fun n hn => ?_)
      · rw [if_pos (by omega)]
      · rw [if_neg (by omega), copyStrategy, hlen_histPlay]
    have hXle : X ≤ₜ gamePlay σ (copyStrategy X) := by
      refine le_of_precomp (g := fun k => 2 * k + 1)
        (Primrec.nat_iff.mp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
        fun k => ?_
      rw [gamePlay_copy_odd σ X (2 * k + 1) (by omega)]
      congr 1
      omega
    exact (hTI _ X ⟨hZle, hXle⟩).mp (hσ (copyStrategy X))
  · right
    refine ⟨τ, fun X hX => ?_⟩
    intro hXA
    have hZle : gamePlay (copyStrategy X) τ ≤ₜ X := by
      refine gamePlay_le 0 (copyStrategy X) τ τ X hX (fun n hn => ?_) (fun n hn => ?_)
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega), copyStrategy, hlen_histPlay]
    have hXle : X ≤ₜ gamePlay (copyStrategy X) τ := by
      refine le_of_precomp (g := fun k => 2 * k)
        (Primrec.nat_iff.mp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
        fun k => ?_
      rw [gamePlay_copy_even τ X (2 * k) (by omega)]
      congr 1
      omega
    exact hτ (copyStrategy X) ((hTI _ X ⟨hZle, hXle⟩).mpr hXA)

/-- **A player-I winning strategy makes `A` realize a cone of degrees — without invariance.**  If `σ`
wins the payoff-`A` game for player I, then for every `X ≥ᵀ σ` some member of `A` is Turing-equivalent
to `X`: the play `gamePlay σ (copyStrategy X)`, which is `≡ᵀ X` (as in `cone_theorem`) and lies in `A`
because `σ` wins.  This is the `WinsI` branch of `cone_theorem` with the *final invariance transfer
omitted* — exactly what survives for a **non-invariant** `A`, and the "realizes" content of Martin's
pointed-perfect-tree extraction (Lemma 2.3) from a winning strategy. -/
theorem winsI_realizes {A : Set (ℕ → Bool)} {σ : ℕ → Bool} (hσ : WinsI A σ)
    {X : ℕ → Bool} (hX : σ ≤ₜ X) :
    ∃ z, z ∈ A ∧ z ≡ₜ X := by
  refine ⟨gamePlay σ (copyStrategy X), hσ (copyStrategy X), ?_, ?_⟩
  · refine gamePlay_le 1 σ (copyStrategy X) σ X hX (fun n hn => ?_) (fun n hn => ?_)
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), copyStrategy, hlen_histPlay]
  · refine le_of_precomp (g := fun k => 2 * k + 1)
      (Primrec.nat_iff.mp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
      fun k => ?_
    rw [gamePlay_copy_odd σ X (2 * k + 1) (by omega)]
    congr 1
    omega

/-- **A player-I win implies the payoff set is cofinal.**  By `winsI_realizes`, `A` realizes every
degree `≥ᵀ σ`, hence meets every cone (`w ≤ᵀ w ⊕ σ ≡ᵀ` some member of `A`).  This is the *easy*
direction relating the game to cofinality; the **converse** — a cofinal set yields a player-I winning
strategy — is the hard content of Martin's Lemma 2.3 and does *not* follow from cofinality alone. -/
theorem winsI_cofinal {A : Set (ℕ → Bool)} {σ : ℕ → Bool} (hσ : WinsI A σ) :
    ∀ w : ℕ → Bool, ∃ x, w ≤ₜ x ∧ x ∈ A := by
  intro w
  obtain ⟨z, hzA, hzeq⟩ := winsI_realizes hσ (X := Cantor.join w σ) (Cantor.right_le_join w σ)
  exact ⟨z, (Cantor.left_le_join w σ).trans hzeq.2, hzA⟩

/-- Cone-theorem consequence in "on a cone" form: a determined Turing
invariant set either holds on a cone or fails on a cone. -/
theorem cone_theorem_onCone (A : Set (ℕ → Bool))
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A))
    (hDet : GameDetermined A) :
    OnCone (· ∈ A) ∨ OnCone (· ∉ A) := by
  rcases cone_theorem A hTI hDet with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact Or.inl ⟨Y, fun X hX => hY hX⟩
  · exact Or.inr ⟨Y, fun X hX => hY hX⟩

#print axioms cone_theorem

end Martin
