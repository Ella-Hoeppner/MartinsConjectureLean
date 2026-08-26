/-
**Lemma 2.11 (Lutz thesis; the computable uniformization lemma), pointed-tree form.**

Building on `Lemma210.lean`, this is the step that turns Lemma 2.10 (a countable-range function is
constant on a pointed tree) into a genuine *computable* uniformization: a relation `R` whose domain
is cofinal and which is *contained in `≥ᵀ`* (`R x y → y ≤ᵀ x`) is uniformized by a **single Turing
functional** on a pointed perfect tree — one fixed code `e` computes an `R`-witness `y = Φ_e(x)` from
every branch `x`.

The proof is exactly Lutz's: for each `x` in the domain there is a code `e` computing *some*
`R`-witness `y ≤ᵀ x` (`exists_code_of_recursiveIn`); the **least** such code — or here, any chosen
code, since Lemma 2.10 needs no minimality — is an ℕ-valued function of the single real `x`, so
`lemma210_of_martinPPT'` makes it constant `= e` on a pointed perfect subtree of the domain.  On that
tree the fixed code `e` uniformizes `R`.

This is the engine beneath the regressive / measure-preserving / order-preserving cases of Martin's
conjecture, and — via `Corollary 2.12` (right inverse of an increasing function) — the inversion step
of the Marks pointed-injective-tree route to the incomparable core (Lutz Prop 5.37).  The essential
hypothesis `R ⊆ ≥ᵀ` is precisely what the incomparable core lacks: its value `f(x)` is *not* `≤ᵀ x`,
so no reduction code exists and this engine cannot fire — the exact `ℕ`-range wall.
-/
import MartinsConjecture.Lemma210

open scoped Computability
open OracleCode Cantor

namespace Martin

/-- **Lemma 2.11 (computable uniformization), pointed-tree form.**  If `R` has cofinal domain and
`R ⊆ ≥ᵀ` (every related `y` is Turing-below its `x`), then there is a fixed code `e` and a pointed
perfect tree `T` such that on every branch `x ∈ [T]`, `Φ_e(x)` is total and `R x (Φ_e(x))` holds. -/
theorem lemma211_of_martinPPT' (hPPT : MartinPPT')
    (R : (ℕ → Bool) → (ℕ → Bool) → Prop)
    (hdom : Cofinal (fun x => ∃ y, R x y))
    (hsub : ∀ x y, R x y → y ≤ₜ x) :
    ∃ (e : ℕ) (T : RawPPT), ∀ x, IsBranch (treeMem T.code) x →
      ∃ y, eval (toPFun x) (ofNatCode e) = toPFun y ∧ R x y := by
  classical
  -- For every `x`, choose a code that witnesses `R` whenever `x` is in the domain (junk otherwise).
  have hex : ∀ x, ∃ e : ℕ, (∃ y, R x y) →
      ∃ y, eval (toPFun x) (ofNatCode e) = toPFun y ∧ R x y := by
    intro x
    by_cases hx : ∃ y, R x y
    · obtain ⟨y, hRy⟩ := hx
      obtain ⟨c, hc⟩ :=
        exists_code_of_recursiveIn (RecursiveIn.iff_nat.mp (hsub x y hRy))
      exact ⟨encodeCode c, fun _ => ⟨y, by rw [ofNatCode_encodeCode]; exact hc, hRy⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  -- The chosen code is an ℕ-valued function of `x`; make it constant on a pointed subtree of the domain.
  obtain ⟨n, T, hT⟩ :=
    lemma210_of_martinPPT' hPPT (fun x => ∃ y, R x y) hdom (fun x => (hex x).choose)
  refine ⟨n, T, fun x hx => ?_⟩
  obtain ⟨hxdom, hxn⟩ := hT x hx
  have hspec := (hex x).choose_spec hxdom
  rwa [show (hex x).choose = n from hxn] at hspec

/-- **Corollary 2.12 (Lutz thesis): an increasing function has a computable right inverse on a
pointed perfect tree.**  If `x ≤ᵀ f x` for every `x`, then there is a fixed code `e` and a pointed
perfect tree `T` such that on every branch `x ∈ [T]`, `Φ_e(x)` is a preimage of `x` under `f`
(`f (Φ_e(x)) = x`).  (`f` is *not* required to be Turing invariant.)

Immediate from Lemma 2.11 applied to `R x y := (f y = x)`: the domain is cofinal because `f z ≥ᵀ z`
puts `f z` in the range above any `z`; and `R ⊆ ≥ᵀ` because `f y = x` together with `y ≤ᵀ f y` gives
`y ≤ᵀ x`.  This is the inversion step used in the Marks pointed-injective-tree route (Prop 5.37): on
a tree where an invariant `f` is injective, inverting it shows `U_M ≤_RK f_*U_M`. -/
theorem cor212_of_martinPPT' (hPPT : MartinPPT') (f : (ℕ → Bool) → (ℕ → Bool))
    (hf : ∀ x, x ≤ₜ f x) :
    ∃ (e : ℕ) (T : RawPPT), ∀ x, IsBranch (treeMem T.code) x →
      ∃ y, eval (toPFun x) (ofNatCode e) = toPFun y ∧ f y = x :=
  lemma211_of_martinPPT' hPPT (fun x y => f y = x)
    (fun z => ⟨f z, hf z, z, rfl⟩)
    (fun _ y hxy => hxy ▸ hf y)

/-- **The right inverse computes the preimage from below.**  Repackaging `cor212_of_martinPPT'`:
on the tree, every branch `x` has a preimage `y ≤ᵀ x` with `f y = x`.  (Drops the explicit code in
favour of the degree statement `y ≤ᵀ x`, the form used downstream.) -/
theorem cor212_preimage_below (hPPT : MartinPPT') (f : (ℕ → Bool) → (ℕ → Bool))
    (hf : ∀ x, x ≤ₜ f x) :
    ∃ T : RawPPT, ∀ x, IsBranch (treeMem T.code) x → ∃ y, y ≤ₜ x ∧ f y = x := by
  obtain ⟨e, T, hT⟩ := cor212_of_martinPPT' hPPT f hf
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨y, hcomp, hfy⟩ := hT x hx
  exact ⟨y, hfy ▸ hf y, hfy⟩

#print axioms lemma211_of_martinPPT'
#print axioms cor212_of_martinPPT'
#print axioms cor212_preimage_below

end Martin
