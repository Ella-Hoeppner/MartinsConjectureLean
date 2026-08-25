/-
**An attack on the incomparable core via an F-driven strictly-increasing chain (the `ω₁` approach).**

This file records the *choice-free substrate* of a genuine attempt to PROVE the incomparable core
(`IncomparableConstant`), the sole open content of Part 1. It is an approach, not a solve; the honest
obstruction is documented below and in `MARTIN_PART1_APPROACH_OMEGA1.md`.

**Reframing.** `IncomparableConstant` is *equivalent* to: no invariant `F` is Turing-incomparable to its
argument on a cone (`incomparableConstant_iff_noIncomparableSelfMap`). A constant `F ≡ c` fails `F X ⊥ X`
above `c`, so "⟹ constant" is really "the hypothesis is impossible". The target becomes: derive a
**contradiction** from `F X ⊥ᵀ X` on a cone.

**The device.** Iterating `F` is blocked because `F X ⊥ X` lets the orbit leave the cone. Iterate the
*graph* `graphFn F X = X ⊕ F X` instead: it is invariant, *increasing* (never leaves the cone), and on the
incomparability cone `graphFn F X >ᵀ X` **strictly** (since `F X ≰ᵀ X`). So the transfinite orbit
`X, graphFn F X, (graphFn F)² X, …, ⊕_{α<λ} (…), …` is a strictly `≤ᵀ`-increasing chain of degrees that
never stabilizes. `graphOrbit_strictMono` (below) proves the **successor dynamics are unconditional and
choice-free**.

**Where it points, and the wall.** A strictly increasing chain of length `ω₁` would inject `ω₁ ↪ reals`,
impossible under AD (perfect-set property) — a contradiction, proving the core. The successor step is
choice-free; the **limit** step `X_λ = ⊕_{α<λ} X_α` needs a real enumerating the countable ordinal `λ`,
and doing so cofinally to `ω₁` is exactly an injection `ω₁ ↪ reals` — the object AD denies. `F`'s
incomparability supplies successor dynamics but never the limit codes. This localizes the whole difficulty
to: *supply `F`-canonical limit-stage ordinal codes without choice.* (Iterating the function `Gᵅ` by
composition is choice-free but yields only an unbounded Martin-order ascent, no contradiction; evaluating
at a point returns to reals and reintroduces the limit-code need. That tension is the wall.)
-/
import MartinsConjecture.GraphFunction
import MartinsConjecture.RegressiveJumpDecomp

open scoped Computability
open Cantor

namespace Martin

variable {F : (ℕ → Bool) → ℕ → Bool} {B : ℕ → Bool}

/-- **An invariant `F` incomparable to its argument on a cone is not constant on a cone.**  A constant
value `c` has `c ≤ᵀ X` for `X ≥ᵀ c`, contradicting `F X ⊥ X`.  So the incomparable-core hypothesis and its
conclusion are mutually exclusive — "⟹ constant" means "the hypothesis is impossible". -/
theorem incomparable_not_constant
    (hinc : OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)) : ¬ ConstantOnCone F := by
  rintro ⟨C, hC⟩
  obtain ⟨B, hB⟩ := onCone_and hinc hC
  have hBX : B ≤ₜ Cantor.join B C := Cantor.left_le_join B C
  have hCX : C ≤ₜ Cantor.join B C := Cantor.right_le_join B C
  have hpair := hB (Cantor.join B C) hBX
  exact hpair.1.1 (hpair.2.1.trans hCX)

/-- **The incomparable core, reframed:** no invariant `F` is Turing-incomparable to its argument on a
cone. -/
def NoIncomparableSelfMap : Prop :=
  ∀ F : (ℕ → Bool) → ℕ → Bool, TuringInvariant F →
    ¬ OnCone (fun X => ¬ F X ≤ₜ X ∧ ¬ X ≤ₜ F X)

/-- **`IncomparableConstant ⟺ NoIncomparableSelfMap`.**  The two forms of the sole open Part-1 core:
"incomparable ⟹ constant" and "incomparable-to-argument is impossible". -/
theorem incomparableConstant_iff_noIncomparableSelfMap :
    IncomparableConstant ↔ NoIncomparableSelfMap := by
  constructor
  · intro h F hF hinc
    exact incomparable_not_constant hinc (h F hF hinc)
  · intro h F hF hinc
    exact absurd hinc (h F hF)

/-- On the incomparability cone the graph strictly increases: `graphFn F X ≰ᵀ X` (given `F X ≰ᵀ X`), so
`graphFn F X >ᵀ X`.  `F X ≤ᵀ graphFn F X`, hence `graphFn F X ≤ᵀ X` would force `F X ≤ᵀ X`. -/
theorem graphFn_strict_of_not_le {X : ℕ → Bool} (h : ¬ F X ≤ₜ X) : ¬ graphFn F X ≤ₜ X :=
  fun hle => h ((val_le_graphFn F X).trans hle)

/-- The graph-orbit is nondecreasing: `X ≤ᵀ (graphFn F)^[n] X`. -/
theorem self_le_graphIter (F : (ℕ → Bool) → ℕ → Bool) (X : ℕ → Bool) :
    ∀ n, X ≤ₜ (graphFn F)^[n] X
  | 0 => Cantor.le.refl X
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (self_le_graphIter F X n).trans (arg_le_graphFn F _)

/-- **The graph-orbit device (choice-free successor dynamics).**  If `F` is Turing-incomparable to its
argument above `B`, then from any `X ≥ᵀ B` the graph-orbit `(graphFn F)^[n] X` stays above `B` and
**strictly increases at every step**.  So the transfinite chain's successor stages are unconditional; the
only obstruction to reaching length `ω₁` (which would inject `ω₁ ↪ reals`, contradicting AD) is at limit
stages, where forming the join needs a real coding the ordinal. -/
theorem graphOrbit_strictMono
    (hinc : ∀ Y, B ≤ₜ Y → ¬ F Y ≤ₜ Y ∧ ¬ Y ≤ₜ F Y)
    {X : ℕ → Bool} (hX : B ≤ₜ X) (n : ℕ) :
    B ≤ₜ (graphFn F)^[n] X ∧ (graphFn F)^[n] X <ₜ (graphFn F)^[n + 1] X := by
  have hBn : B ≤ₜ (graphFn F)^[n] X := hX.trans (self_le_graphIter F X n)
  refine ⟨hBn, ?_⟩
  have hstep : (graphFn F)^[n + 1] X = graphFn F ((graphFn F)^[n] X) :=
    Function.iterate_succ_apply' _ _ _
  rw [hstep]
  exact ⟨arg_le_graphFn F _, graphFn_strict_of_not_le (hinc _ hBn).1⟩

/-- **The uniform-domination obstruction (why the Slaman–Steel domination is half-impossible for the
incomparable core).**  For an incomparable value (`X ≰ᵀ F X`), the jump `X′` is not `≤ᵀ F X` — since
`X ≤ᵀ X′`, `X′ ≤ᵀ F X` would give `X ≤ᵀ F X`.  A *single* function dominating every `X`-computable function
computes `X′` (the modulus); so this shows the **uniform** domination step (one `F X`-computable function
dominating all `X`-computable ones — equivalently `X′ ≤ᵀ F X`) is **impossible** for an incomparable `F`.
The coordinated-tree method can therefore only survive on *per-function* domination, isolating exactly the
open crux.  See `MARTIN_PART1_STRUCTURAL_AM.md` §2.5. -/
theorem incomparable_jump_not_below {F : (ℕ → Bool) → ℕ → Bool} {X : ℕ → Bool}
    (h : ¬ X ≤ₜ F X) : ¬ Cantor.jump X ≤ₜ F X :=
  fun hj => h ((Cantor.le_jump X).trans hj)

#print axioms incomparableConstant_iff_noIncomparableSelfMap
#print axioms graphOrbit_strictMono
#print axioms incomparable_jump_not_below

end Martin
