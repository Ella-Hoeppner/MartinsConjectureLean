import Mathlib.Computability.TuringDegree
import Mathlib.Computability.PartrecCode

/-! Smoke test: check that Mathlib's oracle-computability API is usable downstream. -/

open scoped Computability

example (f : ℕ →. ℕ) : f ≤ᵀ f := TuringReducible.refl f

example (f g h : ℕ →. ℕ) (h1 : f ≤ᵀ g) (h2 : g ≤ᵀ h) : f ≤ᵀ h := h1.trans h2

#check @Nat.RecursiveIn
#check @Nat.Partrec.Code.rec
#check TuringDegree.instPartialOrder
