/-
Topological triviality of Turing-invariant sets, and the unconditional cone
dichotomy at the bottom of the Borel hierarchy.

The key observation (folklore): prepending a finite prefix to a real does not
change its Turing degree, and every basic open set of Cantor space is
determined by a finite prefix.  Hence **every nonempty open Turing-invariant
set is all of Cantor space** (`Martin.eq_univ_of_isOpen_turingInvariant`).

Consequently the conclusion of Martin's cone theorem holds for open and for
closed Turing-invariant sets **unconditionally** — no determinacy hypothesis
(`Martin.cone_dichotomy_of_isOpen`, `Martin.cone_dichotomy_of_isClosed`).
This is why the cone theorem (and Martin's conjecture) only become
interesting higher up the Borel hierarchy.

Computability core: `Cantor.patch_equiv` — `patch L X Y` (first `L` bits from
`X`, then the bits of `Y`) is Turing equivalent to `Y`.  The forward
reduction hard-codes the finite prefix as a lookup table.
-/
import MartinsConjecture.Martin
import Mathlib.Topology.Constructions

open scoped Computability
open OracleCode

namespace Cantor

/-- Replace the first `L` bits of (a shift of) `Y` by those of `X`. -/
def patch (L : ℕ) (X Y : ℕ → Bool) : ℕ → Bool :=
  fun n => if n < L then X n else Y (n - L)

theorem le_patch (L : ℕ) (X Y : ℕ → Bool) : Y ≤ₜ patch L X Y := by
  refine le_of_precomp (g := fun n => n + L)
    (Primrec.nat_iff.mp (Primrec.nat_add.comp Primrec.id (Primrec.const L)))
    fun n => ?_
  rw [patch, if_neg (by omega)]
  congr 1
  omega

theorem patch_le (L : ℕ) (X Y : ℕ → Bool) : patch L X Y ≤ₜ Y := by
  refine RecursiveIn.iff_nat.mpr ?_
  -- Hard-code the prefix as a lookup table.
  set t : List ℕ := (List.range L).map fun n => cond (X n) 1 0 with ht
  set comb : ℕ → ℕ := fun w =>
    (1 - (1 - (L - (Nat.unpair w).1))) * ((Nat.unpair (Nat.unpair w).2).1)
      + (1 - (L - (Nat.unpair w).1)) * ((Nat.unpair (Nat.unpair w).2).2) with hcomb
  have hcombP : Nat.Primrec comb := by
    rw [hcomb]
    refine Primrec.nat_iff.mp ?_
    have hn : Primrec fun w : ℕ => (Nat.unpair w).1 := Primrec.fst.comp Primrec.unpair
    have hs : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have hy : Primrec fun w : ℕ => (Nat.unpair (Nat.unpair w).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have hd : Primrec fun w : ℕ => 1 - (L - (Nat.unpair w).1) :=
      Primrec.nat_sub.comp (Primrec.const 1)
        (Primrec.nat_sub.comp (Primrec.const L) hn)
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp (Primrec.const 1) hd) hs)
      (Primrec.nat_mul.comp hd hy)
  have htbl : Nat.RecursiveIn {toPFun Y} (fun n : ℕ => ((t.getD n 0 : ℕ) : Part ℕ)) :=
    Nat.Primrec.recursiveIn
      (Primrec.nat_iff.mp ((Primrec.list_getD 0).comp (Primrec.const t) Primrec.id))
  have hquery : Nat.RecursiveIn {toPFun Y}
      (fun n : ℕ => ((n - L : ℕ) : Part ℕ) >>= toPFun Y) :=
    Nat.RecursiveIn.comp (.oracle _ rfl)
      (Nat.Primrec.recursiveIn
        (Primrec.nat_iff.mp (Primrec.nat_sub.comp Primrec.id (Primrec.const L))))
  have hid : Nat.RecursiveIn {toPFun Y} (fun n : ℕ => ((n : ℕ) : Part ℕ)) :=
    (Primrec.nat_iff.mp Primrec.id).recursiveIn
  have hP : Nat.RecursiveIn {toPFun Y} (fun n : ℕ =>
      Nat.pair <$> ((n : ℕ) : Part ℕ) <*>
        (Nat.pair <$> ((t.getD n 0 : ℕ) : Part ℕ)
          <*> (((n - L : ℕ) : Part ℕ) >>= toPFun Y))) :=
    Nat.RecursiveIn.pair hid (Nat.RecursiveIn.pair htbl hquery)
  have hF := Nat.RecursiveIn.comp hcombP.recursiveIn hP
  refine hF.of_eq fun n => ?_
  simp only [Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [show (Part.some (n - L) >>= toPFun Y) = toPFun Y (n - L) from Part.bind_some _ _]
  simp only [toPFun, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind,
    Part.bind_some]
  simp only [hcomb, Nat.unpair_pair, patch]
  by_cases hn : n < L
  · rw [if_pos hn]
    have htv : t.getD n 0 = cond (X n) 1 0 := by
      simp [ht, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hn]
    rw [htv]
    have h1 : 1 - (L - n) = 0 := by omega
    rw [h1]
    cases X n <;> simp
  · rw [if_neg hn]
    have h1 : 1 - (L - n) = 1 := by omega
    rw [h1]
    cases Y (n - L) <;> simp

/-- Prepending a finite prefix does not change the Turing degree. -/
theorem patch_equiv (L : ℕ) (X Y : ℕ → Bool) : patch L X Y ≡ₜ Y :=
  ⟨patch_le L X Y, le_patch L X Y⟩

end Cantor

namespace Martin

open Cantor

/-- **Topological triviality of Turing-invariant sets**: a nonempty *open*
Turing-invariant subset of Cantor space is the whole space.  (Every basic
open set is determined by a finite prefix, and finite prefixes are free for
Turing degrees.) -/
theorem eq_univ_of_isOpen_turingInvariant {U : Set (ℕ → Bool)} (hU : IsOpen U)
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ U ↔ Y ∈ U)) (hne : U.Nonempty) :
    U = Set.univ := by
  obtain ⟨X, hX⟩ := hne
  ext Y
  simp only [Set.mem_univ, iff_true]
  obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hU X hX
  set L : ℕ := I.sup id + 1 with hL
  have hZ : patch L X Y ∈ U := by
    apply hpi
    intro i hi
    have hiL : i < L := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    rw [patch, if_pos hiL]
    exact (hu i hi).2
  exact (hTI _ Y (patch_equiv L X Y)).mp hZ

/-- **Unconditional cone dichotomy for open sets**: an open Turing-invariant
set contains a cone or is disjoint from a cone — no determinacy needed
(trivially so: it is empty or everything). -/
theorem cone_dichotomy_of_isOpen {U : Set (ℕ → Bool)} (hU : IsOpen U)
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ U ↔ Y ∈ U)) :
    (∃ Y, cone Y ⊆ U) ∨ ∃ Y, cone Y ⊆ Uᶜ := by
  rcases U.eq_empty_or_nonempty with h | h
  · right
    exact ⟨fun _ => false, by simp [h]⟩
  · left
    refine ⟨fun _ => false, ?_⟩
    rw [eq_univ_of_isOpen_turingInvariant hU hTI h]
    exact fun X _ => Set.mem_univ X

/-- **Unconditional cone dichotomy for closed sets.** -/
theorem cone_dichotomy_of_isClosed {A : Set (ℕ → Bool)} (hA : IsClosed A)
    (hTI : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ A ↔ Y ∈ A)) :
    (∃ Y, cone Y ⊆ A) ∨ ∃ Y, cone Y ⊆ Aᶜ := by
  have hTIc : ∀ X Y : ℕ → Bool, X ≡ₜ Y → (X ∈ Aᶜ ↔ Y ∈ Aᶜ) :=
    fun X Y h => not_congr (hTI X Y h)
  rcases cone_dichotomy_of_isOpen hA.isOpen_compl hTIc with ⟨Y, hY⟩ | ⟨Y, hY⟩
  · exact Or.inr ⟨Y, hY⟩
  · refine Or.inl ⟨Y, fun X hX => ?_⟩
    have := hY hX
    simpa using this

#print axioms eq_univ_of_isOpen_turingInvariant
#print axioms cone_dichotomy_of_isClosed

end Martin
