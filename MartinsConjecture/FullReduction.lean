/-
The full reduction: Martin's conjecture, both parts, reduced to five cores.

Extending `Reduction.lean` (Part I) to Part II: under Turing determinacy,
the pairwise comparability of invariant functions also trichotomizes on a
cone (`comparison_on_cone`), so the *totality* half of the prewellordering
claim reduces to ruling out pointwise-incomparable pairs of regular
functions; *well-foundedness* classically reduces to ruling out strictly
descending ω-chains; and the *successor* claim splits into the provable half
(`martinLT_jump`) and a minimality core.

The capstone (`martinConjecture_of_cores`): **the Borel Martin conjecture in
its entirety follows, under Turing determinacy, from five precisely isolated
open cores**:

1. `RegressiveImpliesConstant`   (Part I, regressive case)
2. `IncomparableImpliesConstant` (Part I, incomparable case)
3. `ComparisonCore`              (Part II totality: no incomparable pairs)
4. `DescendingChainCore`         (Part II well-foundedness: no descending chains)
5. `JumpMinimalityCore`          (Part II successor: nothing strictly between
                                  `F` and `jump ∘ F`)

Each core is a known theorem for uniformly invariant functions
(Steel; Slaman–Steel) and for order-preserving functions (Lutz–Siskind), and
open in general.  Everything *around* them is machine-checked here.
-/
import MartinsConjecture.BoundedCase
import Mathlib.Order.OrderIsoNat

open scoped Computability
open OracleCode Cantor

namespace Martin

/-! ### Pairwise comparison on a cone -/

private theorem le_congr₂ {F G : (ℕ → Bool) → ℕ → Bool}
    (hF : TuringInvariant F) (hG : TuringInvariant G) {X Y : ℕ → Bool}
    (hXY : X ≡ₜ Y) (h : F X ≤ₜ G X) : F Y ≤ₜ G Y :=
  ((hF X Y hXY).2.trans h).trans (hG X Y hXY).1

/-- Under Turing determinacy, any two invariant functions compare on a cone:
`F ≤ₘ G`, or `G <ₘ F` pointwise, or they are pointwise incomparable. -/
theorem comparison_on_cone (hTD : TuringDeterminacy fun _ => True)
    {F G : (ℕ → Bool) → ℕ → Bool}
    (hF : TuringInvariant F) (hG : TuringInvariant G) :
    OnCone (fun X => F X ≤ₜ G X) ∨ OnCone (fun X => G X <ₜ F X) ∨
    OnCone (fun X => ¬ F X ≤ₜ G X ∧ ¬ G X ≤ₜ F X) := by
  set A : ℕ → Set (ℕ → Bool) := fun n =>
    match n with
    | 0 => {X | F X ≤ₜ G X}
    | 1 => {X | G X <ₜ F X}
    | _ + 2 => {X | ¬ F X ≤ₜ G X ∧ ¬ G X ≤ₜ F X} with hA
  have hTI : ∀ n, TuringInvariantSet (A n) := by
    intro n
    match n with
    | 0 =>
      intro X Y hXY
      exact ⟨le_congr₂ hF hG hXY, le_congr₂ hF hG hXY.symm⟩
    | 1 =>
      intro X Y hXY
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨le_congr₂ hG hF hXY h1, fun hc => h2 (le_congr₂ hF hG hXY.symm hc)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨le_congr₂ hG hF hXY.symm h1, fun hc => h2 (le_congr₂ hF hG hXY hc)⟩
    | m + 2 =>
      intro X Y hXY
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun hc => h1 (le_congr₂ hF hG hXY.symm hc),
          fun hc => h2 (le_congr₂ hG hF hXY.symm hc)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun hc => h1 (le_congr₂ hF hG hXY hc),
          fun hc => h2 (le_congr₂ hG hF hXY hc)⟩
  have hcover : cone (fun _ => false) ⊆ ⋃ n, A n := by
    intro X _
    by_cases h1 : F X ≤ₜ G X
    · exact Set.mem_iUnion.mpr ⟨0, h1⟩
    · by_cases h2 : G X ≤ₜ F X
      · exact Set.mem_iUnion.mpr ⟨1, ⟨h2, h1⟩⟩
      · exact Set.mem_iUnion.mpr ⟨2, ⟨h1, h2⟩⟩
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover
  match n with
  | 0 => exact Or.inl hn
  | 1 => exact Or.inr (Or.inl hn)
  | m + 2 => exact Or.inr (Or.inr hn)

/-! ### The Part II cores -/

/-- **Open core 3 (comparison)**: no two regular functions are pointwise
incomparable on a cone.  (This is the totality content of the Part II
prewellordering claim.) -/
def ComparisonCore : Prop :=
  ∀ F G : (ℕ → Bool) → ℕ → Bool, Regular F → Regular G →
    OnCone (fun X => ¬ F X ≤ₜ G X ∧ ¬ G X ≤ₜ F X) → False

/-- **Open core 4 (descending chains)**: there is no strictly ≤ₘ-descending
ω-sequence of regular functions.  (Classically equivalent to the
well-foundedness content of Part II.) -/
def DescendingChainCore : Prop :=
  ∀ Fs : ℕ → (ℕ → Bool) → ℕ → Bool, (∀ n, Regular (Fs n)) →
    (∀ n, MartinLT (Fs (n + 1)) (Fs n)) → False

/-- **Open core 5 (jump minimality)**: nothing regular fits strictly between
`F` and `jump ∘ F`.  (The other half of the successor claim; the provable
half is `martinLT_jump`.) -/
def JumpMinimalityCore : Prop :=
  ∀ F G : (ℕ → Bool) → ℕ → Bool, Regular F → Regular G → MartinLT F G →
    MartinLE (fun X => Cantor.jump (F X)) G

/-! ### The Part II reductions -/

theorem partII_total_of_core (hTD : TuringDeterminacy fun _ => True)
    (hcore : ComparisonCore) : PartII_Borel_Total := by
  intro F G hF hG
  rcases comparison_on_cone hTD hF.2.1 hG.2.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (onCone_mono (fun X hX => hX.1) h)
  · exact absurd h (fun hc => hcore F G hF hG hc)

theorem partII_WF_of_core (hcore : DescendingChainCore) : PartII_Borel_WF := by
  letI : IsIrrefl {F // Regular F} (fun F G => MartinLT F.1 G.1) :=
    ⟨fun F h => h.2 h.1⟩
  letI : IsTrans {F // Regular F} (fun F G => MartinLT F.1 G.1) :=
    ⟨fun F G H h1 h2 => ⟨h1.1.trans h2.1, fun hc => h2.2 (hc.trans h1.1)⟩⟩
  letI : IsStrictOrder {F // Regular F} (fun F G => MartinLT F.1 G.1) := ⟨⟩
  refine RelEmbedding.wellFounded_iff_isEmpty.mpr ⟨fun emb => ?_⟩
  exact hcore (fun n => (emb n).1) (fun n => (emb n).2)
    (fun n => emb.map_rel_iff.mpr (Nat.lt_succ_self n))

theorem partII_succ_of_core (hcore : JumpMinimalityCore) : PartII_Borel_Succ :=
  fun F hF => ⟨martinLT_jump F, fun G hG hFG => hcore F G hF hG hFG⟩

/-! ### The capstone -/

/-- **The full reduction of Martin's conjecture**: under Turing determinacy,
the Borel Martin conjecture — both parts — follows from the five isolated
open cores.  Every ingredient outside the cores is machine-checked. -/
theorem martinConjecture_of_cores (hTD : TuringDeterminacy fun _ => True)
    (h1 : RegressiveImpliesConstant) (h2 : IncomparableImpliesConstant)
    (h3 : ComparisonCore) (h4 : DescendingChainCore)
    (h5 : JumpMinimalityCore) : MartinConjecture_Borel :=
  ⟨partI_Borel_of_cores hTD h1 h2,
   partII_total_of_core hTD h3,
   partII_WF_of_core h4,
   partII_succ_of_core h5⟩

#print axioms comparison_on_cone
#print axioms partII_total_of_core
#print axioms partII_WF_of_core
#print axioms partII_succ_of_core
#print axioms martinConjecture_of_cores

end Martin
