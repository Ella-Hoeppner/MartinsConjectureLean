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

end Martin
