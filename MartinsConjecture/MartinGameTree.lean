/-
**The even-part tree of the Martin game, as a `treeMem` tree, and the `recover` reduction.**

`MartinGameFusion` reduced Martin's Lemma 2.3 (via the abstract `PPT`, `code := σ`) to a single
obligation `GameRecover`: a computable injective functional `g` on the branch set `{emb z}` recovers each
branch from `g(emb z) ⊕ σ`.  Here we discharge that obligation by **reusing the codebase's `lemma21`**:
present the game-embedding image as the branches of a `treeMem` tree `codeGame σ` whose characteristic
is `≤ᵀ σ` (`emb_locality` makes the defining search *bounded*).  `lemma21` then gives
`emb z ≤ᵀ g(emb z) ⊕ codeGame σ ≤ᵀ g(emb z) ⊕ σ` — which is exactly `GameRecover`.  Note we only need
`codeGame σ ≤ᵀ σ` (for `recover`), **not** `≡ᵀ σ`: pointedness and `realizes` were handled by taking the
`PPT.code` to be `σ` itself, sidestepping the earlier σ-encoding subtlety.

The one remaining computability fact is `codeGame σ ≤ᵀ σ` (`GameCodeBelow`), a `codeReal_le`-scale
`RecursiveIn` presentation of the bounded search; everything else — that `codeGame`'s branches are exactly
the image, and the `lemma21`/`recover` wiring — is proved.
-/
import MartinsConjecture.MartinGame
import MartinsConjecture.MartinGameFusion

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- The finite game-simulation match: `s` matches iff some length-`2|s|` prefix `zp` makes the
embedding `emb (pad zp)` agree with `s` on `[0, |s|)`.  Bounded (over `allBoolLists (2|s|)`), hence
computable-in-`σ`. -/
def evenMatchGame (σ : ℕ → Bool) (s : List Bool) : Bool :=
  (allBoolLists (2 * s.length)).any fun zp =>
    (List.range s.length).all fun i =>
      evenPart (gamePlay σ (copyStrategy (Cantor.join (fun j => zp.getD j false) σ))) i == s.getD i false

/-- **Correctness of the bounded match** (via `emb_locality`): `evenMatchGame σ s` is true iff `s` is a
node of the even-part tree, i.e. a prefix of some `emb z`.  The `⟸` direction uses locality: it suffices
to test `zp = z ↾ 2|s|`, since `emb (pad zp) ↾ |s| = emb z ↾ |s|`. -/
theorem evenMatchGame_iff (σ : ℕ → Bool) (s : List Bool) :
    evenMatchGame σ s = true ↔ evenTree σ s := by
  unfold evenMatchGame evenTree
  rw [List.any_eq_true]
  constructor
  · rintro ⟨zp, _, hzp⟩
    rw [List.all_eq_true] at hzp
    refine ⟨fun j => zp.getD j false, fun i hi => ?_⟩
    have := hzp i (List.mem_range.mpr hi)
    simpa [beq_iff_eq] using this
  · rintro ⟨z, hz⟩
    refine ⟨(List.range (2 * s.length)).map z, ?_, ?_⟩
    · have := allBoolLists_complete ((List.range (2 * s.length)).map z)
      rwa [List.length_map, List.length_range] at this
    · rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hi
      simp only [beq_iff_eq]
      rw [emb_locality σ (fun j => ((List.range (2 * s.length)).map z).getD j false) z i
        (fun j hj => getD_range_map z (2 * s.length) j (by omega))]
      exact hz i hi

/-- Characteristic real of the game even-part tree: `codeGame σ (treePos s)` records whether `s` matches
(via `evenMatchGame`), found by a bounded search over finite strings — exactly the `codeReal` pattern. -/
def codeGame (σ : ℕ → Bool) (p : ℕ) : Bool :=
  (List.range (p + 1)).foldr (fun L acc =>
    ((allBoolLists L).foldr (fun s acc2 =>
      ((treePos s == p) && evenMatchGame σ s) || acc2) false) || acc) false

theorem codeGame_treePos (σ : ℕ → Bool) (s : List Bool) :
    codeGame σ (treePos s) = evenMatchGame σ s := by
  unfold codeGame
  have hlen : s.length < treePos s + 1 := by
    have := Nat.lt_two_pow_self (n := s.length); unfold treePos; omega
  cases hem : evenMatchGame σ s with
  | true =>
    rw [foldr_or_mem]
    exact ⟨s.length, by simp only [List.mem_range]; omega, by
      rw [foldr_or_mem]; exact ⟨s, allBoolLists_complete s, by simp [hem]⟩⟩
  | false =>
    rw [Bool.eq_false_iff, ne_eq, foldr_or_mem]
    rintro ⟨L, _, hL⟩
    rw [foldr_or_mem] at hL
    obtain ⟨s', _, hs'⟩ := hL
    simp only [Bool.and_eq_true, beq_iff_eq] at hs'
    obtain ⟨hpos, hev⟩ := hs'
    have : s' = s := treePos_inj hpos
    subst this; rw [hem] at hev; exact Bool.false_ne_true hev

/-- Membership in the game tree is exactly being a node of the even-part tree. -/
theorem treeMem_codeGame (σ : ℕ → Bool) (s : List Bool) :
    treeMem (codeGame σ) s ↔ evenTree σ s := by
  unfold treeMem
  rw [codeGame_treePos]; exact evenMatchGame_iff σ s

/-- The game tree is downward closed. -/
theorem codeGame_closed (σ : ℕ → Bool) :
    ∀ s b, treeMem (codeGame σ) (s ++ [b]) → treeMem (codeGame σ) s := by
  intro s b hs
  rw [treeMem_codeGame] at hs ⊢
  obtain ⟨z, hz⟩ := hs
  refine ⟨z, fun i hi => ?_⟩
  have hi' : i < (s ++ [b]).length := by rw [List.length_append]; simp; omega
  rw [← getD_append_lt s [b] i hi]; exact hz i hi'

/-- **The game tree's branches are exactly the game-embedding image.**  `⟹` is compactness
(`exists_z_of_branch`); `⟸` is that each `emb z` is a branch. -/
theorem isBranch_codeGame (σ x : ℕ → Bool) :
    IsBranch (treeMem (codeGame σ)) x ↔
      ∃ z, ∀ i, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) i = x i := by
  constructor
  · intro hx
    refine exists_z_of_branch σ x (fun n => ?_)
    obtain ⟨z, hz⟩ := (treeMem_codeGame σ _).mp (hx n)
    refine ⟨z, fun i hi => ?_⟩
    have hi' : i < ((List.range n).map x).length := by rw [List.length_map, List.length_range]; exact hi
    rw [← getD_range_map x n i hi]; exact hz i hi'
  · rintro ⟨z, hz⟩ n
    rw [treeMem_codeGame]
    refine ⟨z, fun i hi => ?_⟩
    rw [List.length_map, List.length_range] at hi
    rw [getD_range_map x n i hi]; exact hz i

/-! ### Discharging `GameRecover` (hence all of Martin's Lemma 2.3) via `lemma21`, modulo `codeGame ≤ᵀ σ` -/

/-- **The one remaining computability fact:** the game tree's characteristic is computable from `σ`.
`emb_locality` makes the defining search bounded (`codeReal_le`-scale `RecursiveIn` presentation). -/
def GameCodeBelow : Prop := ∀ σ : ℕ → Bool, codeGame σ ≤ₜ σ

/-- **`GameRecover` holds given `codeGame σ ≤ᵀ σ`** — the game embedding's `recover` obligation, via the
codebase's `lemma21` on `codeGame σ`.  `lemma21` gives `emb z ≤ᵀ g(emb z) ⊕ codeGame σ`; since
`codeGame σ ≤ᵀ σ`, this is `≤ᵀ g(emb z) ⊕ σ`.  (`code ≤ᵀ σ` suffices here — no `≡ᵀ σ` needed — because
`PPT.code` was taken to be `σ` itself.) -/
theorem gameRecover_of_codeBelow (hbelow : GameCodeBelow) : GameRecover := by
  intro σ g hg hinj x hx
  have hmem_iff : ∀ y, (∃ z, evenPart (gamePlay σ (copyStrategy (Cantor.join z σ))) = y) ↔
      IsBranch (treeMem (codeGame σ)) y := fun y => by
    rw [isBranch_codeGame]
    exact ⟨fun ⟨z, hzy⟩ => ⟨z, fun i => congrFun hzy i⟩, fun ⟨z, hz⟩ => ⟨z, funext hz⟩⟩
  obtain ⟨c, hc⟩ := hg
  have hrec := lemma21 (Tr := codeGame σ) (e := c) (g := g) (codeGame_closed σ)
    (fun y hy => hc y ((hmem_iff y).mpr hy))
    (fun y y' hy hy' => hinj y y' ((hmem_iff y).mpr hy) ((hmem_iff y').mpr hy'))
    ((hmem_iff x).mp hx)
  exact hrec.trans (Cantor.join_le (Cantor.left_le_join (g x) σ)
    ((hbelow σ).trans (Cantor.right_le_join (g x) σ)))

/-- **`MartinPPT` from the single computability fact `GameCodeBelow`** — all determinacy and all tree
mathematics machine-checked. -/
theorem martinPPT_of_codeBelow (hbelow : GameCodeBelow)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A)) :
    MartinPPT :=
  martinPPT_of_recover (gameRecover_of_codeBelow hbelow) hdet

/-- **Part 1 of Martin's conjecture from `GameCodeBelow`.**  Part 1 holds given: `GameCodeBelow`
(`codeGame σ ≤ᵀ σ` — a single `codeReal_le`-scale computability fact), full determinacy of the Martin
games, Turing determinacy, and `escaping ⟹ MP`.  The *only genuinely open* input is the last (the
incomparable core).  Martin's Lemma 2.3 is thus reduced to `GameCodeBelow`, with its **entire**
mathematical content machine-checked: the asymmetric game, `winsI_martinGame_of_cofinal`, `emb_locality`,
`exists_z_of_branch`, the whole `treeMem` tree (`codeGame`, its `treeMem`/`IsBranch` characterizations,
closedness) and the `lemma21`/`recover` reduction. -/
theorem partI_of_codeBelow_escaping (hbelow : GameCodeBelow)
    (hdet : ∀ A : Set (ℕ → Bool), GameDetermined (martinGame A))
    (hTD : TuringDeterminacy fun _ => True)
    (hesc : ∀ F, TuringInvariant F → Escaping F → MeasurePreserving F) :
    ∀ F, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_of_gameRecover_escaping (gameRecover_of_codeBelow hbelow) hdet hTD hesc

#print axioms treeMem_codeGame
#print axioms isBranch_codeGame
#print axioms gameRecover_of_codeBelow
#print axioms partI_of_codeBelow_escaping

end Martin
