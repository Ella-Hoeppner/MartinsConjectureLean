/-
**The relativized Church–Kleene ordinal `ω₁^X`, and the engine instantiated.**

`ω₁^X` = the supremum of order types of `X`-computable well-orders of `ℕ`.  This is the
canonical degree-invariant *ordinal* rank, and the one Lutz uses for the regressive case on
the hyperarithmetic degrees.  Here we define it (correctly: guarded by `≤ᵀ X` so non-total
oracle computations, which land in `X′`, are excluded), prove it is **monotone** and
**degree-invariant**, and instantiate the Fodor engine `no_regressive_of_ordinal_rank`:

> no `base`-cone-preserving regressive `F` strictly decreases `ω₁^X`.

Equivalently a regressive counterexample must be **`ω₁`-preserving** — it cannot strictly drop
the Church–Kleene ordinal.

**⚠️ NB (correction, 2026-08-23):** the *Turing* regressive core this file was built to attack is in
fact a **KNOWN Slaman–Steel theorem** (see `Reduction.RegressiveSlamanSteel`), *not* open — the earlier
framing conflated it with Lutz's *hyperarithmetic-degrees* result (`D_h`, a different structure).  The
machinery here is valid mathematics but targets an already-solved problem; the sole open Part-1 content
is the incomparable core.  See `ATTACK.md` and `Reduction.partI_iff_incomparable`.
-/
import MartinsConjecture.OrdinalUltrapower
import MartinsConjecture.BoundedCase
import Mathlib.SetTheory.Ordinal.Family

open scoped Computability
open Cantor

namespace Martin

/-- The relation on `ℕ` coded by a real `O` (via Cantor pairing). -/
def codedRel (O : ℕ → Bool) : ℕ → ℕ → Prop := fun m k => O (Nat.pair m k) = true

open Classical in
/-- The order type of the relation coded by `O` if it is a well-order, else `0`. -/
noncomputable def wellOrderType (O : ℕ → Bool) : Ordinal :=
  if h : IsWellOrder ℕ (codedRel O) then @Ordinal.type ℕ (codedRel O) h else 0

open Classical in
/-- The `n`-th candidate: the order type contributed by `nthComputableIn X n`, if it is a
genuinely `X`-computable (`≤ᵀ X`) well-order. -/
noncomputable def ckTerm (X : ℕ → Bool) (n : ℕ) : Ordinal :=
  if nthComputableIn X n ≤ₜ X then wellOrderType (nthComputableIn X n) else 0

/-- **The relativized Church–Kleene ordinal `ω₁^X`.**  The sup of order types of the
`X`-computable well-orders of `ℕ`, indexing the reals `≤ᵀ X` by `nthComputableIn X`. -/
noncomputable def churchKleene (X : ℕ → Bool) : Ordinal := ⨆ n : ℕ, ckTerm X n

/-- **`ω₁^X` is monotone in the Turing oracle.**  Every `X`-computable well-order is
`Y`-computable when `X ≤ᵀ Y`. -/
theorem churchKleene_mono {X Y : ℕ → Bool} (hXY : X ≤ₜ Y) :
    churchKleene X ≤ churchKleene Y := by
  apply Ordinal.iSup_le
  intro n
  by_cases h : nthComputableIn X n ≤ₜ X
  · have hX : ckTerm X n = wellOrderType (nthComputableIn X n) := by
      unfold ckTerm; rw [if_pos h]
    have hOY : nthComputableIn X n ≤ₜ Y := h.trans hXY
    obtain ⟨m, hm⟩ := exists_nthComputableIn hOY
    have hmY : nthComputableIn Y m ≤ₜ Y := by rw [hm]; exact hOY
    have hY : ckTerm Y m = wellOrderType (nthComputableIn X n) := by
      unfold ckTerm; rw [if_pos hmY, hm]
    rw [hX, ← hY]
    exact Ordinal.le_iSup _ m
  · have hX : ckTerm X n = 0 := by unfold ckTerm; rw [if_neg h]
    rw [hX]; exact zero_le'

/-- **`ω₁^X` is degree-invariant.** -/
theorem churchKleene_invariant {X Y : ℕ → Bool} (h : X ≡ₜ Y) :
    churchKleene X = churchKleene Y :=
  le_antisymm (churchKleene_mono h.1) (churchKleene_mono h.2)

/-- **No cone-preserving regressive `F` strictly decreases `ω₁^X`** (the engine, instantiated
with the genuine Church–Kleene rank).  A `base`-cone-preserving `F` with `ω₁^{F X} < ω₁^X` for
all `X ≥ᵀ base` is impossible: its iterates would descend the well-founded ordinal ultrapower.
So a regressive counterexample is `ω₁`-preserving. -/
theorem no_omega1_decreasing_conePreserving
    {F : (ℕ → Bool) → ℕ → Bool} {base : ℕ → Bool}
    (hstep : ∀ X, base ≤ₜ X → churchKleene (F X) < churchKleene X ∧ base ≤ₜ F X) : False :=
  no_regressive_of_ordinal_rank hstep

/-- **`ω₁^X ≥ ω` (non-degeneracy).**  The standard order on `ℕ`, coded via Cantor pairing, is a
computable well-order of type `ω`; being computable it is `≤ᵀ X`, so it contributes `ω` to the
supremum.  This confirms the rank is not the trivial `0` — the engine constraint is non-vacuous. -/
theorem omega_le_churchKleene (X : ℕ → Bool) : (Ordinal.omega0 : Ordinal) ≤ churchKleene X := by
  have hcomp : Computable (fun k => decide ((Nat.unpair k).1 < (Nat.unpair k).2)) := by
    obtain ⟨_, hpr⟩ := (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair) : PrimrecPred fun k => (Nat.unpair k).1 < (Nat.unpair k).2)
    exact hpr.to_comp.of_eq (fun k => by congr 1)
  set O : ℕ → Bool := fun k => decide ((Nat.unpair k).1 < (Nat.unpair k).2) with hOdef
  have hle : O ≤ₜ X := le_of_computable hcomp
  obtain ⟨n, hn⟩ := exists_nthComputableIn hle
  have hrel : codedRel O = (· < · : ℕ → ℕ → Prop) := by
    funext m k
    simp only [O, codedRel, Nat.unpair_pair, decide_eq_true_eq]
  have hwo : IsWellOrder ℕ (codedRel O) := by rw [hrel]; infer_instance
  have htype : wellOrderType O = Ordinal.omega0 := by
    unfold wellOrderType
    rw [dif_pos hwo]
    have heq : @Ordinal.type ℕ (codedRel O) hwo = @Ordinal.type ℕ (· < ·) inferInstance := by
      congr 1
    rw [heq]; exact Ordinal.type_nat_lt
  calc (Ordinal.omega0 : Ordinal) = wellOrderType O := htype.symm
    _ = ckTerm X n := by
        unfold ckTerm; rw [if_pos (by rw [hn]; exact hle), hn]
    _ ≤ churchKleene X := Ordinal.le_iSup _ n

/-- **The `ω₁`-behavior dichotomy.**  A regressive invariant `F` (on a cone `F X ≤ᵀ X`) either
**preserves** `ω₁^X` (`ω₁^{F X} = ω₁^X`) on a cone, or **strictly decreases** it (`ω₁^{F X} < ω₁^X`)
on a cone.  This is the first step of Lutz's reduction; combined with
`no_omega1_decreasing_conePreserving`, the strict-decrease branch forces `F` to escape its own cone,
so a genuine (cone-preserving) counterexample lands in the `ω₁`-preserving branch — the open case. -/
theorem regressive_omega1_dichotomy (hTD : TuringDeterminacy fun _ => True)
    {F : (ℕ → Bool) → ℕ → Bool} (hF : TuringInvariant F)
    (hreg : OnCone (fun X => F X ≤ₜ X)) :
    OnCone (fun X => churchKleene (F X) = churchKleene X) ∨
    OnCone (fun X => churchKleene (F X) < churchKleene X) := by
  have hTI : TuringInvariantSet {X | churchKleene (F X) < churchKleene X} := by
    intro X Y hXY
    have hFeq : churchKleene (F X) = churchKleene (F Y) := churchKleene_invariant (hF X Y hXY)
    have hXeq : churchKleene X = churchKleene Y := churchKleene_invariant hXY
    constructor
    · intro h; rw [Set.mem_setOf_eq, ← hFeq, ← hXeq]; exact h
    · intro h; rw [Set.mem_setOf_eq, hFeq, hXeq]; exact h
  rcases cone_theorem _ hTI (hTD _ trivial hTI) with ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inr ⟨W, fun X hX => hW hX⟩
  · obtain ⟨B, hB⟩ := onCone_and hreg ⟨W, fun X hX => hW hX⟩
    exact Or.inl ⟨B, fun X hX =>
      le_antisymm (churchKleene_mono (hB X hX).1) (not_lt.mp (hB X hX).2)⟩

#print axioms omega_le_churchKleene
#print axioms churchKleene_mono
#print axioms churchKleene_invariant
#print axioms no_omega1_decreasing_conePreserving
#print axioms regressive_omega1_dichotomy

end Martin
