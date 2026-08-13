/-
The use principle for r.e. operators: membership in `Wˣ` is forced by a finite
prefix of `X`.

`n ∈ Wˣ ⟺ ∃ ℓ, machine e halts on n using only the first ℓ bits of X`
(`OracleCode.mem_reReal_iff_haltsOn_prefix`).  This is the operator-level use
principle, the continuity-in-the-oracle fact underlying the continuous case of
Lachlan's local dichotomy (Lutz Cor. 3.11).  Proved from `evaln`
soundness/completeness against the prefix table `graphOf (bitg X) ℓ`.
-/
import MartinsConjecture.ReOperator
import MartinsConjecture.Evaln
import MartinsConjecture.Locality

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-- Machine `e` halts on input `n` using only the finite oracle prefix `σ`
(a `List ℕ` of `0/1` bits): `n ∈ W^σ`. -/
def haltsOn (σ : List ℕ) (e n : ℕ) : Prop :=
  ∃ s, (evaln s σ (ofNatCode e) n).isSome

/-- The prefix table `toPFun X i = some (bitg X i)` is exactly the bit-graph of
`X`. -/
theorem toPFun_eq_some_bitg (X : ℕ → Bool) (i : ℕ) :
    toPFun X i = Part.some (bitg X i) := rfl

/-- **The use principle for r.e. operators.**  `n ∈ Wˣ` iff machine `e` halts on
`n` under some finite prefix of `X`'s bit-graph.  (`⇒` is completeness of
`evaln`; `⇐` is soundness against the prefix table.) -/
theorem mem_reReal_iff_haltsOn_prefix (e n : ℕ) (X : ℕ → Bool) :
    (eval (toPFun X) (ofNatCode e) n).Dom ↔ ∃ ℓ, haltsOn (graphOf (bitg X) ℓ) e n := by
  constructor
  · intro hd
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk⟩ := evaln_complete (O := toPFun X) (g := bitg X)
      (fun i => toPFun_eq_some_bitg X i) hv
    exact ⟨k, k, by rw [hk]; rfl⟩
  · rintro ⟨ℓ, s, hs⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have hmem := evaln_sound
      (graphOf_sound (fun i => toPFun_eq_some_bitg X i) ℓ) hv
    exact Part.dom_iff_mem.mpr ⟨v, hmem⟩

/-- **Monotonicity of the operator on finite strings**: `n ∈ W^σ` persists when
`σ` is extended (more oracle information only creates halting, never destroys
it). -/
theorem haltsOn_mono {σ σ' : List ℕ} (h : σ <+: σ') {e n : ℕ}
    (hh : haltsOn σ e n) : haltsOn σ' e n := by
  obtain ⟨s, hs⟩ := hh
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨s, by rw [evaln_mono (le_refl s) h hv]; rfl⟩

/-- Reformulation in terms of `reReal`: `Wˣ n = 1` iff a finite prefix forces
halting. -/
theorem reReal_eq_true_iff (e n : ℕ) (X : ℕ → Bool) :
    reReal e X n = true ↔ ∃ ℓ, haltsOn (graphOf (bitg X) ℓ) e n := by
  rw [reReal, decide_eq_true_iff]
  exact mem_reReal_iff_haltsOn_prefix e n X

/-- **r.e. operators are open (continuous) in the oracle.**  The set of oracles
`X` for which `n ∈ Wˣ` is open in Cantor space: membership is forced by a finite
prefix (the use principle), so it is a positive/`Σ₁` condition.  This is the
topological form of the use principle, and the reason "continuity on `deg X`" in
Lachlan's argument can only fail through a *missing* witness. -/
theorem isOpen_reReal (e n : ℕ) :
    IsOpen {X : ℕ → Bool | reReal e X n = true} := by
  have hset : {X : ℕ → Bool | reReal e X n = true}
      = ⋃ v, {X : ℕ → Bool | v ∈ eval (toPFun X) (ofNatCode e) n} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, reReal, decide_eq_true_iff,
      Part.dom_iff_mem]
  rw [hset]
  exact isOpen_iUnion (fun v => Martin.isOpen_mem_eval (ofNatCode e) n v)

end OracleCode

#print axioms OracleCode.mem_reReal_iff_haltsOn_prefix
#print axioms OracleCode.reReal_eq_true_iff
#print axioms OracleCode.isOpen_reReal
