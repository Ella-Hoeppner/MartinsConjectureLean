/-
**Sharper constraints on a Part-1 counterexample.**

`nonMP_incomparable_cone` (`EscapingDichotomy`) says an escaping non-MP invariant `F`
is incomparable to *each fixed* degree `Z ≥ᵀ W₀` on a (Z-dependent) cone.  The
degrees `≤ᵀ W₁` are **countable**, so countable completeness of the cone filter
(`coneFilter_iInter`) upgrades this to a *single* cone on which `F` is incomparable
to the whole interval `[W₀, W₁]` at once.

This is a genuine strengthening (uniform over a countable interval), and it pins
the shape of a counterexample further: on one cone, `F X` is incomparable to every
fixed degree between `W₀` and `W₁`.
-/
import MartinsConjecture.EscapingDichotomy
import MartinsConjecture.ConeFilter
import MartinsConjecture.BoundedCase
import MartinsConjecture.PartIRecast
import MartinsConjecture.MartinResults

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool}

/-- **Interval incomparability.**  A counterexample `F` (escaping, invariant,
non-measure-preserving) is, for every fixed `W₁`, Turing-incomparable to *every*
degree `Z` with `W₀ ≤ᵀ Z ≤ᵀ W₁` — all on a single cone (the kernel bound `W₀` is
fixed once and for all). -/
theorem nonMP_incomparable_interval (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hesc : Escaping F) (hnmp : ¬ MeasurePreserving F) :
    ∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X) := by
  obtain ⟨W₀, hW₀⟩ := nonMP_incomparable_cone hTD hF hesc hnmp
  refine ⟨W₀, fun W₁ => ?_⟩
  -- countable family indexed by the `W₁`-computable reals
  set f : ℕ → Set (ℕ → Bool) := fun n =>
    {X | W₀ ≤ₜ nthComputableIn W₁ n →
      ¬ F X ≤ₜ nthComputableIn W₁ n ∧ ¬ nthComputableIn W₁ n ≤ₜ F X} with hf
  have hmem : ∀ n, f n ∈ coneFilter := by
    intro n
    by_cases hge : W₀ ≤ₜ nthComputableIn W₁ n
    · -- f n is exactly the incomparability cone for Z = nthComputableIn W₁ n
      have := hW₀ (nthComputableIn W₁ n) hge      -- IncomparableToFixed F Z
      unfold IncomparableToFixed at this
      rw [onCone_iff_mem_coneFilter] at this
      refine Filter.mem_of_superset this (fun X hX => ?_)
      exact fun _ => hX
    · -- vacuous: f n = univ
      exact Filter.univ_mem' (fun _ hZ => absurd hZ hge)
  have hInter : (⋂ n, f n) ∈ coneFilter := coneFilter_iInter hmem
  rw [onCone_iff_mem_coneFilter]
  refine Filter.mem_of_superset hInter (fun X hX Z hW₀Z hZW₁ => ?_)
  obtain ⟨n, hn⟩ := exists_nthComputableIn hZW₁
  have hXn : X ∈ f n := Set.mem_iInter.mp hX n
  rw [hf] at hXn
  simp only [Set.mem_setOf_eq, hn] at hXn
  exact hXn hW₀Z

/-- **A nonconstant invariant function's values are "uncountable" on a cone.**
No countable family of degrees `c₀, c₁, …` covers the values of a nonconstant
invariant `F` on any cone.  (If they did, the invariant fibers `{X | F X ≡ᵀ cₙ}`
would cover a cone, and the σ-pigeonhole would put `F ≡ᵀ cₙ` on a cone = constant.)
This generalizes `bounded_implies_constant` (bounded values ⟹ countably covered ⟹
constant) and is the exact "escaping" content on the value side. -/
theorem nonconstant_values_uncountable (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) :
    ∀ c : ℕ → (ℕ → Bool), ¬ OnCone (fun X => ∃ n, F X ≡ₜ c n) := by
  intro c hcov
  set A : ℕ → Set (ℕ → Bool) := fun n => {X | F X ≡ₜ c n} with hA
  have hTI : ∀ n, TuringInvariantSet (A n) := fun n X X' hXX' =>
    ⟨fun h => (hF X X' hXX').symm.trans h, fun h => (hF X X' hXX').trans h⟩
  obtain ⟨W, hW⟩ := hcov
  have hcover : cone W ⊆ ⋃ n, A n := fun X hX => Set.mem_iUnion.mpr (hW X hX)
  obtain ⟨n, hn⟩ := exists_onCone_of_cover hTD (fun _ => trivial) hTI hcover
  exact hnc ⟨c n, hn⟩

/-- **Lutz–Siskind Theorem 4.6, as a named hypothesis**: a *non-constant* order-preserving invariant
function is measure-preserving.  Phrased via the exact conclusion of `nonconstant_values_uncountable`
(the values escape every countable family on every cone — this is what "non-constant" delivers) so it
composes directly.  Its proof (the perfect-set theorem + the Groszek–Slaman–Kihara coding of §4 of
Lutz–Siskind) is the genuine hard content and is not formalized here. -/
def OrderPreservingNonconstantMP : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F → TuringInvariant F →
    (∀ c : ℕ → (ℕ → Bool), ¬ OnCone (fun X => ∃ n, F X ≡ₜ c n)) → MeasurePreserving F

/-- **`AvoidingImpliesConstant` reduces to Theorem 4.6, with Case 1 discharged.**  The order-preserving
skeleton (`partI_orderPreserving_of_lemmas`) takes `AvoidingImpliesConstant` as a raw hypothesis.  Here
it is *derived* from `OrderPreservingNonconstantMP` — the content of Lutz–Siskind's Theorem 4.6 — with
the "countable range ⟹ constant" **Case 1 discharged** via the already-proved
`nonconstant_values_uncountable`.  Proof: a non-constant such `F` is measure-preserving (Thm 4.6), so its
values reach the cone above `Z₀` — contradicting that its range avoids that cone.  This isolates the
sole remaining unformalized ingredient of the order-preserving case as the *actual paper theorem*
(non-constant order-preserving ⟹ measure-preserving), rather than the ad-hoc `AvoidingImpliesConstant`. -/
theorem avoidingImpliesConstant_of_theorem46 (hTD : TuringDeterminacy fun _ => True)
    (h46 : OrderPreservingNonconstantMP) : AvoidingImpliesConstant := by
  intro F hop havoid
  by_contra hnc
  have hinv : TuringInvariant F := fun X Y hXY => ⟨hop X Y hXY.1, hop Y X hXY.2⟩
  have hmp : MeasurePreserving F := h46 F hop hinv (nonconstant_values_uncountable hTD hinv hnc)
  obtain ⟨Z₀, hZ₀⟩ := havoid
  obtain ⟨W, hW⟩ := hmp Z₀
  exact hZ₀ W (hW W (Cantor.le.refl W))

/-- **Part 1 for order-preserving functions, reduced to the two *actual* Lutz–Siskind theorems.**
Combining `partI_orderPreserving_of_lemmas` with the reduction above: Part 1 for order-preserving `F`
follows from `MeasurePreservingAboveId` (their **Theorem 3.4** — measure-preserving ⟹ above-id, already
proved here from `MartinPPT`) and `OrderPreservingNonconstantMP` (their **Theorem 4.6** — non-constant
order-preserving ⟹ measure-preserving).  Case 1 (countable range ⟹ constant) is *discharged*, so the
only unformalized inputs are the two named paper theorems themselves. -/
theorem partI_orderPreserving_of_theorem46 (hTD : TuringDeterminacy fun _ => True)
    (h1 : MeasurePreservingAboveId) (h46 : OrderPreservingNonconstantMP) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_orderPreserving_of_lemmas h1 (avoidingImpliesConstant_of_theorem46 hTD h46)

/-- **The perfect-set coding step, isolated** (Lutz–Siskind Corollary 4.5 content): for an
order-preserving invariant `F` with uncountable range, the range is *cofinal*.  This is the sole
remaining unformalized ingredient of the order-preserving case — the Groszek–Slaman–Kihara
finite-extension coding on a perfect subset of the range (their §4.1). -/
def OrderPreservingUncountableCofinal : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F → TuringInvariant F →
    (∀ c : ℕ → (ℕ → Bool), ¬ OnCone (fun X => ∃ n, F X ≡ₜ c n)) → ∀ Z : ℕ → Bool, ∃ X, Z ≤ₜ F X

/-- **Theorem 4.6 reduces further to just the coding step.**  The elementary `cofinal ⟹ MP` half is
discharged by `orderPreserving_mp_of_rangeCofinal`, so `OrderPreservingNonconstantMP` (Thm 4.6) follows
from `OrderPreservingUncountableCofinal` alone.  Net: the entire order-preserving case now rests on
exactly the perfect-set coding step plus the already-proved `MeasurePreservingAboveId`. -/
theorem orderPreservingNonconstantMP_of_uncountableCofinal
    (h : OrderPreservingUncountableCofinal) : OrderPreservingNonconstantMP :=
  fun F hop hinv huncount => orderPreserving_mp_of_rangeCofinal hop (h F hop hinv huncount)

/-- **The range of an order-preserving function is countably directed** (Lutz–Siskind §4.2 — the
directedness used inside Corollary 4.5).  Any countable family of reals each `≤ᵀ` some value of `F`
has a common upper bound that is itself `≤ᵀ` a single value of `F`: join the witnesses `Xₙ` (each
`Xₙ ≤ᵀ joinFam X` by `component_le_joinFam`) and push through order-preservation.  This discharges the
directedness hypothesis of the perfect-set coding step, leaving only the perfect-set/coding core. -/
theorem orderPreserving_range_countablyDirected (hop : OrderPreserving F)
    (d : ℕ → (ℕ → Bool)) (hd : ∀ n, ∃ X, d n ≤ₜ F X) : ∃ Y, ∀ n, d n ≤ₜ F Y := by
  choose X hX using hd
  exact ⟨joinFam X, fun n => (hX n).trans (hop (X n) (joinFam X) (Cantor.component_le_joinFam X n))⟩

/-- **Capstone: Part 1 for order-preserving functions rests on exactly `MartinPPT` + the coding step.**
Assembling this session's reductions: given `MartinPPT` (which supplies Theorem 3.4 via
`measurePreservingAboveId_of_martinPPT`) and `OrderPreservingUncountableCofinal` (the
Groszek–Slaman–Kihara perfect-set coding, Corollary 4.5), Part 1 holds for every order-preserving `F`.
Case 1 (countable range ⟹ constant), the `cofinal ⟹ MP` step, and the directedness of the range are
all *proved*; only the coding remains unformalized.  So the order-preserving case is now formally
reduced to a single atomic determinacy/coding statement. -/
theorem partI_orderPreserving_of_coding (hTD : TuringDeterminacy fun _ => True)
    (hM : MartinPPT) (hcoding : OrderPreservingUncountableCofinal) :
    ∀ F : (ℕ → Bool) → ℕ → Bool, OrderPreserving F → ConstantOnCone F ∨ AboveIdOnCone F :=
  partI_orderPreserving_of_theorem46 hTD
    (fun _ hF hmp => measurePreservingAboveId_of_martinPPT hM hF hmp)
    (orderPreservingNonconstantMP_of_uncountableCofinal hcoding)

/-- **The sole open core, handled for the order-preserving sub-class.**  An order-preserving function
that is incomparable to its argument on a cone is constant on a cone (given `MartinPPT` and the coding):
by `partI_orderPreserving_of_coding` it is constant or above-id, and incomparability rules out above-id.
So the incomparable core holds for order-preserving `F` — connecting the order-preserving reduction to
the genuinely-open incomparable core. -/
theorem incomparable_orderPreserving_constant (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hcoding : OrderPreservingUncountableCofinal) (hop : OrderPreserving F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ConstantOnCone F := by
  rcases partI_orderPreserving_of_coding hTD hM hcoding F hop with hc | hai
  · exact hc
  · exfalso
    obtain ⟨W, hW⟩ := onCone_and hincomp hai
    exact (hW W (Cantor.le.refl W)).1.2 (hW W (Cantor.le.refl W)).2

/-- **A Part-1 counterexample is not order-preserving** (given `MartinPPT` and the coding): were it
order-preserving, `partI_orderPreserving_of_coding` would force constant or above-id.  Sharpens the
"wildness" profile — a counterexample is not order-preserving, not (computably-)uniformly invariant
(`counterexample_not_uniformlyInvariant`), and incomparable to its argument. -/
theorem counterexample_not_orderPreserving (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hcoding : OrderPreservingUncountableCofinal) (hnc : ¬ ConstantOnCone F)
    (hnai : ¬ AboveIdOnCone F) : ¬ OrderPreserving F := by
  intro hop
  rcases partI_orderPreserving_of_coding hTD hM hcoding F hop with hc | hai
  · exact hnc hc
  · exact hnai hai

/-- **Lutz–Siskind Theorem 4.6, stated verbatim** (modulo the coding, supplied as
`OrderPreservingNonconstantMP`): every order-preserving invariant function is *constant on a cone or
measure-preserving*.  By cases on constancy: a non-constant such `F` has uncountable range
(`nonconstant_values_uncountable`), so Theorem 4.6's content applies. -/
theorem orderPreserving_constant_or_mp (hTD : TuringDeterminacy fun _ => True)
    (h46 : OrderPreservingNonconstantMP) (hop : OrderPreserving F) :
    ConstantOnCone F ∨ MeasurePreserving F := by
  by_cases hnc : ConstantOnCone F
  · exact Or.inl hnc
  · exact Or.inr (h46 F hop hop.turingInvariant
      (nonconstant_values_uncountable hTD hop.turingInvariant hnc))

/-- **The sole open core follows from Steel's conjecture.**  Since the regressive core is a KNOWN
Slaman–Steel theorem (`regressiveImpliesConstant_of_slamanSteel`), the only open content of Part 1 is
`IncomparableImpliesConstant` — and it in turn follows from Steel's conjecture (every invariant `F` is
`MartinEquiv` to a uniformly-invariant one), via `partI_general_of_steelBridge`.  So the incomparable
core is squarely a cone-uniformization problem. -/
theorem incomparableImpliesConstant_of_steelBridge (hTD : TuringDeterminacy fun _ => True)
    (bridge : ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
      ∃ G, UniformlyTuringInvariant G ∧ MartinEquiv F G) :
    IncomparableImpliesConstant :=
  incomparableImpliesConstant_of_partI (partI_general_of_steelBridge hTD bridge)

/-- **The project's two framings of Part 1's open content coincide** (given `MartinPPT` and the KNOWN
regressive theorem).  The "class-specific" open input `escaping ⟹ measure-preserving` and the sole
open core `IncomparableImpliesConstant` are **equivalent** — both are equivalent to Part 1 itself:
`escaping ⟹ MP` gives Part 1 via `partI_of_martinPPT_escaping`, and Part 1 gives `escaping ⟹ MP` since
an escaping function is non-constant, hence above-id, hence measure-preserving.  So there is genuinely
*one* open problem, viewable either way. -/
theorem escapingMP_iff_incomparable (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) :
    (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F → MeasurePreserving F)
      ↔ IncomparableImpliesConstant := by
  constructor
  · intro hesc
    exact incomparableImpliesConstant_of_partI (partI_of_martinPPT_escaping hM hTD hesc)
  · intro hincomp F hF hescF
    rcases partI_of_slamanSteel_incomparable hTD hSS hincomp F hF with hc | hai
    · exact absurd hc (not_constant_of_escaping hescF)
    · exact aboveId_measurePreserving hai

/-- **Part 1 ⟺ "escaping ⟹ measure-preserving"** (given `MartinPPT` and the known regressive theorem
`RegressiveSlamanSteel`): the single clean statement of exactly what remains open in Part 1.  Chains
`partI_iff_incomparable` with `escapingMP_iff_incomparable`. -/
theorem partI_iff_escapingMP (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) :
    (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F)
      ↔ (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F → MeasurePreserving F) :=
  (partI_iff_incomparable hTD hSS).trans (escapingMP_iff_incomparable hTD hM hSS).symm

/-- **The two natural formulations of the open core coincide** (given `MartinPPT` + the known regressive
theorem): the incomparable core (`F X ⊥ᵀ X` on a cone ⟹ constant) is equivalent to "no escaping
invariant `F` is incomparable to a *fixed* degree on a cone".  Chains `escapingMP_iff_incomparable`
with `escapingMP_iff_no_fixedIncomparable`. -/
theorem incomparable_iff_no_fixedIncomparable (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) :
    IncomparableImpliesConstant ↔
      (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F → ∀ Z, ¬ IncomparableToFixed F Z) :=
  (escapingMP_iff_incomparable hTD hM hSS).symm.trans (escapingMP_iff_no_fixedIncomparable hTD)

/-- **The definitive statement of Part 1's open content** (given `MartinPPT` and the known regressive
theorem): the following four are *all equivalent* — Part 1 itself, the incomparable core, "escaping ⟹
measure-preserving", and "no escaping `F` is incomparable to a fixed degree".  There is genuinely **one**
open problem, and this is exactly it. -/
theorem partI_open_content_TFAE (hTD : TuringDeterminacy fun _ => True) (hM : MartinPPT)
    (hSS : RegressiveSlamanSteel) :
    List.TFAE
      [ (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → ConstantOnCone F ∨ AboveIdOnCone F),
        IncomparableImpliesConstant,
        (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F → MeasurePreserving F),
        (∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F → Escaping F →
          ∀ Z, ¬ IncomparableToFixed F Z) ] := by
  tfae_have 1 ↔ 2 := partI_iff_incomparable hTD hSS
  tfae_have 2 ↔ 3 := (escapingMP_iff_incomparable hTD hM hSS).symm
  tfae_have 3 ↔ 4 := escapingMP_iff_no_fixedIncomparable hTD
  tfae_finish

/-- **The complete profile of a Part-1 counterexample.**  Under `MartinPPT` and
determinacy, a Turing-invariant `F` that is neither constant on a cone nor above
the identity on a cone must simultaneously:
1. be **regressive** (`F X <ᵀ X`) on a cone, *or* **incomparable to its argument**
   (`F X ⊥ᵀ X`) on a cone (the comparability trichotomy, minus the excluded
   `≡ᵀ`/`>ᵀ` cases which are above-id); and
2. be **Turing-incomparable to a whole cone of fixed degrees** (`Z ≥ᵀ W₀`), with
   the incomparability uniform over every countable initial interval `[W₀, W₁]`.

This is the sharpest statement of what a hypothetical counterexample looks like;
Part 1 asserts no `F` meets it. -/
theorem counterexample_full_profile (hM : MartinPPT)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    (OnCone (fun X => F X <ₜ X) ∨ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) ∧
    (∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) := by
  refine ⟨?_, nonMP_incomparable_interval hTD hF
    (escaping_of_not_constant hTD hF hnc)
    (fun hmp => hnai ((mp_iff_aboveId_of_martinPPT hM hF).mp hmp))⟩
  rcases comparability_on_cone hTD hF with heq | hgt | hlt | hincomp
  · exact absurd ⟨_, fun X hX => (heq.choose_spec X hX).2⟩ hnai
  · exact absurd ⟨_, fun X hX => (hgt.choose_spec X hX).1⟩ hnai
  · exact Or.inl hlt
  · exact Or.inr hincomp

/-- **The sharpened counterexample profile, using the KNOWN regressive theorem.**  Given
`RegressiveSlamanSteel`, a Part-1 counterexample is, on a cone, **incomparable to its argument** (not
merely "regressive or incomparable" — the regressive alternative is ruled out by Slaman–Steel), and
simultaneously incomparable to every fixed degree over `[W₀, W₁]`.  So a counterexample lives purely in
the incomparable core. -/
theorem counterexample_sharp_profile (hM : MartinPPT) (hSS : RegressiveSlamanSteel)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) ∧
    (∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) :=
  ⟨counterexample_incomparable_to_argument hTD hSS hF hnc hnai,
   (counterexample_full_profile hM hTD hF hnc hnai).2⟩

/-- **The definitive counterexample profile.**  Under `MartinPPT`, the known regressive theorem
(`RegressiveSlamanSteel`), and the order-preserving coding (`OrderPreservingUncountableCofinal`), any
Part-1 counterexample `F` (invariant, non-constant, non-above-id) must simultaneously, on a cone, be
**incomparable to its argument**, **incomparable to every fixed degree** over `[W₀, W₁]`, **not
order-preserving**, and **not uniformly Turing-invariant**.  This is the sharpest machine-checked
answer to "what must a counterexample look like" — it lives entirely in the incomparable core and is
maximally "wild". -/
theorem counterexample_wild_profile (hM : MartinPPT) (hSS : RegressiveSlamanSteel)
    (hcoding : OrderPreservingUncountableCofinal) (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) ∧
    (∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) ∧
    ¬ OrderPreserving F ∧ ¬ UniformlyTuringInvariant F :=
  ⟨(counterexample_sharp_profile hM hSS hTD hF hnc hnai).1,
   (counterexample_sharp_profile hM hSS hTD hF hnc hnai).2,
   counterexample_not_orderPreserving hTD hM hcoding hnc hnai,
   counterexample_not_uniformlyInvariant hTD F hnc hnai⟩

/-- **An incomparable counterexample escapes every parameter** (a NEW constraint, using the KNOWN
regressive theorem).  If an invariant `F` is incomparable to its argument on a cone, then for *no*
fixed real `p` is `F X ≤ᵀ X ⊕ p` on a cone.  Reason: if it were, then on `cone p` we'd have `F X ≤ᵀ X`
(regressive), so Slaman–Steel (`RegressiveSlamanSteel`) makes `F` constant or above-id — but
incomparability rules out above-id (`¬ X ≤ᵀ F X`), and a constant `c` is `≤ᵀ X` on `cone c`
(contradicting `¬ F X ≤ᵀ X`).  So a counterexample's values are not "`X`-plus-a-fixed-parameter"
computable — a strong escaping property beyond `nonMP_incomparable_cone`. -/
theorem incomparable_escapes_params (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (p : ℕ → Bool) :
    ¬ OnCone (fun X => F X ≤ₜ Cantor.join X p) := by
  intro hbound
  have hreg : OnCone (fun X => F X ≤ₜ X) := by
    obtain ⟨W, hW⟩ := hbound
    refine ⟨Cantor.join W p, fun X hX => ?_⟩
    have hWX : W ≤ₜ X := (Cantor.left_le_join W p).trans hX
    have hpX : p ≤ₜ X := (Cantor.right_le_join W p).trans hX
    exact (hW X hWX).trans (Cantor.join_le (Cantor.le.refl X) hpX)
  rcases hSS F hF hreg with hc | hai
  · obtain ⟨c, hcE⟩ := hc
    obtain ⟨W, hW⟩ := onCone_and hincomp hcE
    obtain ⟨h1, h2⟩ := hW (Cantor.join W c) (Cantor.left_le_join W c)
    exact h1.1 (h2.1.trans (Cantor.right_le_join W c))
  · obtain ⟨W, hW⟩ := onCone_and hincomp hai
    exact (hW W (Cantor.le.refl W)).1.2 (hW W (Cantor.le.refl W)).2

/-- **Strengthened escaping** (under determinacy): an incomparable counterexample has `F X ≰ᵀ X ⊕ p`
on a *whole cone*, for every fixed `p`.  The property `F X ≤ᵀ X ⊕ p` is degree-invariant in `X`, so
the cone dichotomy (`cone_theorem_onCone`) upgrades `incomparable_escapes_params`' "not on a cone"
into "the negation holds on a cone".  Thus a counterexample's values are eventually *strictly* not
`X`-plus-a-parameter computable — the sharpest available form of the escaping constraint. -/
theorem incomparable_escapes_params_onCone (hTD : TuringDeterminacy fun _ => True)
    (hSS : RegressiveSlamanSteel) (hF : TuringInvariant F)
    (hincomp : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) (p : ℕ → Bool) :
    OnCone (fun X => ¬ F X ≤ₜ Cantor.join X p) := by
  have hinv : TuringInvariantSet {X | F X ≤ₜ Cantor.join X p} := by
    intro X Y hXY
    have hFXY : F X ≡ₜ F Y := hF X Y hXY
    have hJ : Cantor.join X p ≡ₜ Cantor.join Y p :=
      ⟨Cantor.join_le (hXY.1.trans (Cantor.left_le_join Y p)) (Cantor.right_le_join Y p),
       Cantor.join_le (hXY.2.trans (Cantor.left_le_join X p)) (Cantor.right_le_join X p)⟩
    exact ⟨fun h => (hFXY.2.trans h).trans hJ.1, fun h => (hFXY.1.trans h).trans hJ.2⟩
  rcases cone_theorem_onCone {X | F X ≤ₜ Cantor.join X p} hinv (hTD _ trivial hinv) with hle | hnle
  · exact absurd hle (incomparable_escapes_params hSS hF hincomp p)
  · exact hnle

/-- **Counterexample-level escaping.**  A Part-1 counterexample `F` (invariant, not constant, not
above-id) has, for *every* fixed parameter `p`, `F X ≰ᵀ X ⊕ p` on a cone.  Combines
`counterexample_incomparable_to_argument` (the comparability trichotomy + the known regressive theorem
force incomparability) with `incomparable_escapes_params_onCone`.  So a hypothetical counterexample's
values are, uniformly in `X`, not computable from `X` together with any single fixed oracle. -/
theorem counterexample_escapes_all_params (hSS : RegressiveSlamanSteel)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) (p : ℕ → Bool) :
    OnCone (fun X => ¬ F X ≤ₜ Cantor.join X p) :=
  incomparable_escapes_params_onCone hTD hSS hF
    (counterexample_incomparable_to_argument hTD hSS hF hnc hnai) p

/-- **The definitive counterexample profile.**  Collects every machine-checked constraint a Part-1
counterexample must satisfy: incomparable to its argument, incomparable to every fixed degree across
an interval, escaping every fixed parameter (`F X ≰ᵀ X ⊕ p` on a cone, for all `p`), and outside every
known regularity class (not order-preserving, not uniformly invariant).  Extends
`counterexample_wild_profile` with the new escaping constraint.  This is the sharpest description the
corrected framework yields; only the incomparable-core proof (Posner–Robinson) would close the gap. -/
theorem counterexample_definitive_profile (hM : MartinPPT) (hSS : RegressiveSlamanSteel)
    (hcoding : OrderPreservingUncountableCofinal) (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) ∧
    (∃ W₀, ∀ W₁, OnCone (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) ∧
    (∀ p, OnCone (fun X => ¬ F X ≤ₜ Cantor.join X p)) ∧
    ¬ OrderPreserving F ∧ ¬ UniformlyTuringInvariant F :=
  ⟨(counterexample_sharp_profile hM hSS hTD hF hnc hnai).1,
   (counterexample_sharp_profile hM hSS hTD hF hnc hnai).2,
   fun p => counterexample_escapes_all_params hSS hTD hF hnc hnai p,
   counterexample_not_orderPreserving hTD hM hcoding hnc hnai,
   counterexample_not_uniformlyInvariant hTD F hnc hnai⟩

/-- **A regressive cone-preserving function generates an infinite descending Martin
chain.**  If an invariant `F` is, on `cone base`, both regressive (`F X <ᵀ X`) and
cone-preserving (`base ≤ᵀ F X`), then its iterates form an infinite strictly
Martin-descending chain `F ≻ₘ F² ≻ₘ F³ ≻ₘ …`.

*Caveat (honest):* this does **not** refute Part 2 as formalized — `DescendingChainCore`
forbids descending chains of `Regular` (= `AboveIdOnCone`) functions, whereas these
iterates are *below* the identity, a region the conjecture does not claim to
well-order.  So this is a structural fact about the below-id part of the Martin
order, not a cross-half contradiction.  (And the cone-preserving hypothesis is what
a bare regressive counterexample may fail — `F` can escape its own cone, the
non-uniformity wall.) -/
theorem regressive_conePreserving_descending_chain
    {F : (ℕ → Bool) → ℕ → Bool} {base : ℕ → Bool}
    (hyp : ∀ X, base ≤ₜ X → F X <ₜ X ∧ base ≤ₜ F X) :
    ∀ n, MartinLT (F^[n + 1]) (F^[n]) := by
  have hinv : ∀ n X, base ≤ₜ X → base ≤ₜ F^[n] X := by
    intro n
    induction n with
    | zero => intro X hX; simpa using hX
    | succ n ih => intro X hX; rw [Function.iterate_succ_apply']; exact (hyp _ (ih X hX)).2
  intro n
  refine ⟨⟨base, fun X hX => ?_⟩, ?_⟩
  · show F^[n + 1] X ≤ₜ F^[n] X
    rw [Function.iterate_succ_apply']; exact (hyp _ (hinv n X hX)).1.1
  · rintro ⟨base', hbase'⟩
    have hX : base ≤ₜ Cantor.join base base' := Cantor.left_le_join base base'
    have hX' : base' ≤ₜ Cantor.join base base' := Cantor.right_le_join base base'
    have h1 : F^[n + 1] (Cantor.join base base') <ₜ F^[n] (Cantor.join base base') := by
      rw [Function.iterate_succ_apply']; exact (hyp _ (hinv n _ hX)).1
    exact h1.2 (hbase' _ hX')

/-- **No idempotent cone-preserving regressive function** (unconditional).  If `F`
is, on `cone base`, regressive (`F X <ᵀ X`) and cone-preserving (`base ≤ᵀ F X`), it
cannot also be idempotent (`F (F X) ≡ᵀ F X`): at `X = base`, `F base` lies in the
cone, so regressivity gives `F (F base) <ᵀ F base`, contradicting idempotence's
`F base ≤ᵀ F (F base)`.  (The degenerate `F ≻ₘ F²` slice of the descending chain,
here needing no determinacy at all.) -/
theorem no_idempotent_conePreserving_regressive
    {F : (ℕ → Bool) → ℕ → Bool} {base : ℕ → Bool}
    (hreg : ∀ X, base ≤ₜ X → F X <ₜ X ∧ base ≤ₜ F X)
    (hidem : ∀ X, base ≤ₜ X → F (F X) ≡ₜ F X) : False := by
  have hFb : base ≤ₜ F base := (hreg base (Cantor.le.refl base)).2
  have h1 : F (F base) <ₜ F base := (hreg (F base) hFb).1
  have h2 : F (F base) ≡ₜ F base := hidem base (Cantor.le.refl base)
  exact h1.2 h2.2

/-- **An incomparable counterexample is *doubly* incomparable.**  If an invariant
`F` is incomparable to its argument on a cone (`F X ⊥ᵀ X`, the incomparable-core
hypothesis), then under `MartinPPT` it is also incomparable to a whole cone of
fixed degrees: for `Z ≥ᵀ W₀`, on one cone `F X` is incomparable to **both** `X`
and `Z`.  So a counterexample to the incomparable core is incomparable to its own
argument *and* to every sufficiently high fixed degree, simultaneously. -/
theorem incomparable_case_doubly_incomparable (hM : MartinPPT)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hincX : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) :
    ∃ W₀, ∀ Z, W₀ ≤ₜ Z →
      OnCone (fun X => (¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X) ∧ (¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) := by
  have hnc : ¬ ConstantOnCone F := by
    rintro ⟨C, hcon⟩
    obtain ⟨B, hB⟩ := onCone_and hincX hcon
    obtain ⟨hinc0, heq0⟩ := hB _ (Cantor.left_le_join B C)
    exact hinc0.1 (heq0.1.trans (Cantor.right_le_join B C))
  have hnai : ¬ AboveIdOnCone F := by
    rintro hai
    obtain ⟨B, hB⟩ := onCone_and hincX hai
    exact (hB B (Cantor.le.refl B)).1.2 (hB B (Cantor.le.refl B)).2
  obtain ⟨W₀, hW₀⟩ := nonMP_incomparable_cone hTD hF (escaping_of_not_constant hTD hF hnc)
    (fun hmp => hnai ((mp_iff_aboveId_of_martinPPT hM hF).mp hmp))
  exact ⟨W₀, fun Z hZ => onCone_and hincX (hW₀ Z hZ)⟩

/-- **Arithmetically-bounded ⟹ constant** (strengthens `bounded_implies_constant`).
If a Turing-invariant `F` has, on a cone, `F X ≤ᵀ c^(n)` for *some* finite `n` (i.e.
`F X` is arithmetic in a fixed `c`), then `F` is constant on a cone.  Reason: the
degrees `≤ᵀ c^(n)` over all `n` are a *countable* set (each `{≤ᵀ c^(n)}` is countable,
countable union), so the values are countably covered and `nonconstant_values_uncountable`
forces constancy.  Consequently **a counterexample is *arithmetically* escaping** — its
values leave every fixed arithmetic cone, not merely every fixed Turing cone. -/
theorem arithmetically_bounded_implies_constant (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) {c : ℕ → Bool}
    (hbd : OnCone fun X => ∃ n, F X ≤ₜ Cantor.jump^[n] c) : ConstantOnCone F := by
  by_contra hnc
  set d : ℕ → (ℕ → Bool) :=
    fun m => nthComputableIn (Cantor.jump^[m.unpair.1] c) m.unpair.2 with hd
  have hcov : OnCone (fun X => ∃ m, F X ≡ₜ d m) := by
    obtain ⟨Y, hY⟩ := hbd
    refine ⟨Y, fun X hX => ?_⟩
    obtain ⟨n, hn⟩ := hY X hX
    obtain ⟨k, hk⟩ := exists_nthComputableIn hn
    refine ⟨Nat.pair n k, ?_⟩
    have hdeq : d (Nat.pair n k) = F X := by
      rw [hd]; simp only [Nat.unpair_pair]; exact hk
    rw [hdeq]
    exact Cantor.equiv.refl (F X)
  exact nonconstant_values_uncountable hTD hF hnc d hcov

/-- **Per-degree trap.**  For a nonconstant invariant `F` and *any* fixed degree `A`,
on a cone either `A ≤ᵀ F X` (`F` reaches above `A`) or `F X ⊥ A` (`F` is incomparable
to `A`) — `F` is never eventually `≤ᵀ A` (that would be bounded, hence constant).  A
counterexample thus meets every fixed degree either from strictly above or sideways. -/
theorem nonconstant_above_or_incomparable_fixed (hTD : TuringDeterminacy fun _ => True)
    (hF : TuringInvariant F) (hnc : ¬ ConstantOnCone F) (A : ℕ → Bool) :
    OnCone (fun X => A ≤ₜ F X) ∨ OnCone (fun X => ¬ A ≤ₜ F X ∧ ¬ F X ≤ₜ A) := by
  have hTIa : TuringInvariantSet {X | A ≤ₜ F X} :=
    fun X Y hXY => ⟨fun h => h.trans (hF X Y hXY).1, fun h => h.trans (hF X Y hXY).2⟩
  rcases cone_theorem _ hTIa (hTD _ trivial hTIa) with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact Or.inl ⟨Y, fun X hX => hY hX⟩
  · have hnb : ¬ OnCone (fun X => F X ≤ₜ A) := fun hb => hnc (bounded_implies_constant hTD hF hb)
    have hTIb : TuringInvariantSet {X | F X ≤ₜ A} :=
      fun X Y hXY => ⟨fun h => (hF X Y hXY).2.trans h, fun h => (hF X Y hXY).1.trans h⟩
    rcases cone_theorem _ hTIb (hTD _ trivial hTIb) with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
    · exact absurd ⟨Z, fun X hX => hZ hX⟩ hnb
    · obtain ⟨B, hB⟩ := onCone_and (⟨Y, fun X hX => hY hX⟩ : OnCone (fun X => ¬ A ≤ₜ F X))
        (⟨Z, fun X hX => hZ hX⟩ : OnCone (fun X => ¬ F X ≤ₜ A))
      exact Or.inr ⟨B, hB⟩

/-- **The complete machine-checked profile of a Part-I counterexample.**  Bundling
every constraint proved here and in `MartinResults`, a Turing-invariant `F` that is
neither constant nor above-id on a cone must simultaneously be:
1. **regressive or incomparable to its argument** on a cone;
2. **incomparable to a whole cone of fixed degrees** `Z ≥ᵀ W₀`, uniformly over every
   countable interval `[W₀,W₁]`;
3. **not even computably-uniformly Turing-invariant** (genuinely "wild" — no uniform
   witness transform, not even a computable-on-a-cone one; a fortiori not
   `UniformlyTuringInvariant`);
4. **uncountably-valued** — its values are not covered by any countable set of degrees; and
5. **arithmetically escaping** — for every fixed `c`, on no cone is `F X ≤ᵀ c^(n)` for some
   `n` (it leaves every fixed *arithmetic* cone, strictly stronger than Turing-escaping).
This is the sharpest fully-verified description of a hypothetical counterexample; Part I
asserts no `F` meets it, and every known proof route to that assertion is blocked by the
barrier analysed in `ATTACK.md`. -/
theorem counterexample_complete_profile (hM : MartinPPT)
    (hTD : TuringDeterminacy fun _ => True) (hF : TuringInvariant F)
    (hnc : ¬ ConstantOnCone F) (hnai : ¬ AboveIdOnCone F) :
    (OnCone (fun X => F X <ₜ X) ∨ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) ∧
    (∃ W₀, ∀ W₁, OnCone
      (fun X => ∀ Z, W₀ ≤ₜ Z → Z ≤ₜ W₁ → ¬ F X ≤ₜ Z ∧ ¬ Z ≤ₜ F X)) ∧
    (¬ ComputablyUniformlyTuringInvariant F) ∧
    (∀ c : ℕ → (ℕ → Bool), ¬ OnCone (fun X => ∃ n, F X ≡ₜ c n)) ∧
    (∀ c : ℕ → Bool, ¬ OnCone (fun X => ∃ n, F X ≤ₜ Cantor.jump^[n] c)) :=
  ⟨(counterexample_full_profile hM hTD hF hnc hnai).1,
   (counterexample_full_profile hM hTD hF hnc hnai).2,
   counterexample_not_computablyUniform hTD F hnc hnai,
   nonconstant_values_uncountable hTD hF hnc,
   fun c hbd => hnc (arithmetically_bounded_implies_constant hTD hF hbd)⟩

#print axioms nonMP_incomparable_interval
#print axioms nonconstant_values_uncountable
#print axioms counterexample_full_profile
#print axioms regressive_conePreserving_descending_chain
#print axioms no_idempotent_conePreserving_regressive
#print axioms incomparable_case_doubly_incomparable
#print axioms arithmetically_bounded_implies_constant
#print axioms nonconstant_above_or_incomparable_fixed
#print axioms counterexample_complete_profile
#print axioms avoidingImpliesConstant_of_theorem46
#print axioms partI_orderPreserving_of_theorem46
#print axioms orderPreservingNonconstantMP_of_uncountableCofinal
#print axioms orderPreserving_range_countablyDirected
#print axioms partI_orderPreserving_of_coding
#print axioms escapingMP_iff_incomparable
#print axioms partI_open_content_TFAE
#print axioms orderPreserving_constant_or_mp

end Martin
