/-
The Posner–Robinson theorem — relativized-jump-inversion form.

The genuine Posner–Robinson theorem states: for every noncomputable `A` there is
`G` with `A ⊕ G ≡ᵀ G′`.  Its proof is a finite-extension (forcing) construction
whose *hard* content is a "read-back" lemma: `A ⊕ G` computes `G′` by replaying
the construction, using `G` as a certificate of convergence witnesses and the
coded bits of `A` as stage delimiters — *without* consulting `0′`.  That crux
genuinely avoids putting `0′` below `A ⊕ G`.

This file proves the closest fully-honest fragment reachable from the existing
Friedberg jump-inversion machinery (`JumpInversion.lean`), by *relativizing
Friedberg inversion to the join `A ⊕ 0′`*:

  set `G := jReal (A ⊕ 0′)`.  Since `A ⊕ 0′ ≥ᵀ 0′`, Friedberg inversion gives
  `G ≤ᵀ A ⊕ 0′` and `G′ ≡ᵀ A ⊕ 0′`.

From this we read off, unconditionally in `A`:

* `posnerRobinson_jump_equiv`  : `G′ ≡ᵀ A ⊕ 0′`         (the master equivalence)
* `posnerRobinson_A_le_jump`   : `A ≤ᵀ G′`               (`A` is coded into `G′`)
* `posnerRobinson_zero_le_jump`: `0′ ≤ᵀ G′`
* `posnerRobinson_G_le`        : `G ≤ᵀ A ⊕ 0′`
* `posnerRobinson_join_le_jump`: `A ⊕ G ≤ᵀ G′`           (the *easy* PR direction)

and the genuine Posner–Robinson equivalence **on the cone above `0′`**:

* `posnerRobinson_of_zero_le`  : if `0′ ≤ᵀ A` then `A ⊕ G ≡ᵀ G′`.

HONEST SCOPE.  This is *not* the full Posner–Robinson theorem for arbitrary
noncomputable `A`.  The relativized construction forces `0′ ≤ᵀ G′` (indeed
`G′ ≡ᵀ A ⊕ 0′`), whereas genuine PR must *avoid* placing `0′` below `G′`.  The
reverse direction `G′ ≤ᵀ A ⊕ G` fails for this `G` unless `0′ ≤ᵀ A ⊕ G`; that
gap — closed by the delimiter/read-back argument, not by relativizing Friedberg
— is exactly the remaining PR content.  See the comment block at the end for a
precise statement of the gap.
-/
import MartinsConjecture.JumpInversion

open scoped Computability
open OracleCode Cantor

namespace OracleCode

attribute [local instance] Classical.propDecidable

/-! ### The Posner–Robinson real (relativized-inversion form)

We apply Friedberg jump inversion to the oracle `A ⊕ 0′`.  Because `A ⊕ 0′`
computes `0′`, the hypothesis of `jump_inversion` is met, and the resulting real
`G := jReal (A ⊕ 0′)` satisfies the three Friedberg claims relative to `A ⊕ 0′`.
-/

/-- The join `A ⊕ 0′` computes `0′` (`0′` sits in the right half of the join). -/
theorem zero_le_join_zero (A : ℕ → Bool) :
    Cantor.jump (fun _ : ℕ => false) ≤ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) :=
  Cantor.right_le_join A (Cantor.jump (fun _ : ℕ => false))

/-- **The Posner–Robinson real** for `A`: Friedberg-invert the join `A ⊕ 0′`.
Concretely `prReal A = jReal (A ⊕ 0′)`, the finite-extension real built relative
to the oracle `A ⊕ 0′` (which computes `0′`, so the extension-halting decisions
are available). -/
noncomputable def prReal (A : ℕ → Bool) : ℕ → Bool :=
  jReal (Cantor.join A (Cantor.jump (fun _ : ℕ => false)))

/-- `G ≤ᵀ A ⊕ 0′` — the construction is recursive in `A ⊕ 0′`. -/
theorem prReal_le (A : ℕ → Bool) :
    prReal A ≤ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) :=
  jReal_le _ (zero_le_join_zero A)

/-- `G′ ≤ᵀ A ⊕ 0′` — the jump of `G` is read off the `(A ⊕ 0′)`-computable stage
decisions. -/
theorem jump_prReal_le (A : ℕ → Bool) :
    Cantor.jump (prReal A) ≤ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) :=
  jump_jReal_le _ (zero_le_join_zero A)

/-- `A ⊕ 0′ ≤ᵀ G′` — the oracle `A ⊕ 0′` is decoded from `G′`. -/
theorem join_le_jump_prReal (A : ℕ → Bool) :
    Cantor.join A (Cantor.jump (fun _ : ℕ => false)) ≤ₜ Cantor.jump (prReal A) :=
  C_le_jump _

/-! ### The master equivalence and its corollaries -/

/-- **The master equivalence**: `G′ ≡ᵀ A ⊕ 0′`.  This is Friedberg inversion for
`A ⊕ 0′`, restated for the Posner–Robinson real. -/
theorem posnerRobinson_jump_equiv (A : ℕ → Bool) :
    Cantor.jump (prReal A) ≡ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) :=
  ⟨jump_prReal_le A, join_le_jump_prReal A⟩

/-- `A ≤ᵀ G′` — `A` is coded into the jump of `G`. -/
theorem posnerRobinson_A_le_jump (A : ℕ → Bool) :
    A ≤ₜ Cantor.jump (prReal A) :=
  (Cantor.left_le_join A (Cantor.jump (fun _ : ℕ => false))).trans (join_le_jump_prReal A)

/-- `0′ ≤ᵀ G′`. -/
theorem posnerRobinson_zero_le_jump (A : ℕ → Bool) :
    Cantor.jump (fun _ : ℕ => false) ≤ₜ Cantor.jump (prReal A) :=
  (zero_le_join_zero A).trans (join_le_jump_prReal A)

/-- `G ≤ᵀ A ⊕ 0′`. -/
theorem posnerRobinson_G_le (A : ℕ → Bool) :
    prReal A ≤ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) :=
  prReal_le A

/-- **The easy PR direction**: `A ⊕ G ≤ᵀ G′`.  Since `A ≤ᵀ G′` (coding) and
`G ≤ᵀ G′` (jumps dominate their base), the join is `≤ᵀ G′`. -/
theorem posnerRobinson_join_le_jump (A : ℕ → Bool) :
    Cantor.join A (prReal A) ≤ₜ Cantor.jump (prReal A) :=
  Cantor.join_le (posnerRobinson_A_le_jump A) (Cantor.le_jump (prReal A))

/-! ### Genuine Posner–Robinson on the cone above `0′` -/

/-- **Posner–Robinson on the cone above `0′`.**  If `0′ ≤ᵀ A` (e.g. `A ≡ᵀ 0′`, or
any `A` computing the halting problem), then the relativized construction *does*
give the full Posner–Robinson equivalence `A ⊕ G ≡ᵀ G′`.

For such `A`, `A ⊕ 0′ ≡ᵀ A`, so `G′ ≡ᵀ A`, and the reverse direction
`G′ ≤ᵀ A ⊕ G` holds because `G′ ≡ᵀ A ≤ᵀ A ⊕ G`. -/
theorem posnerRobinson_of_zero_le (A : ℕ → Bool)
    (hA : Cantor.jump (fun _ : ℕ => false) ≤ₜ A) :
    Cantor.join A (prReal A) ≡ₜ Cantor.jump (prReal A) := by
  refine ⟨posnerRobinson_join_le_jump A, ?_⟩
  -- `G′ ≡ᵀ A ⊕ 0′ ≡ᵀ A ≤ᵀ A ⊕ G`.
  have hjoinA : Cantor.join A (Cantor.jump (fun _ : ℕ => false)) ≤ₜ A :=
    Cantor.join_le (Cantor.le.refl A) hA
  exact (jump_prReal_le A).trans
    (hjoinA.trans (Cantor.left_le_join A (prReal A)))

/-! ### The main Posner–Robinson statement (fragment form)

Packaged existential: for every `A`, there is a real `G` with `G′ ≡ᵀ A ⊕ 0′`,
hence `A ≤ᵀ G′`, `0′ ≤ᵀ G′`, and `A ⊕ G ≤ᵀ G′`; and if `0′ ≤ᵀ A` this upgrades
to the full Posner–Robinson equivalence `A ⊕ G ≡ᵀ G′`. -/
theorem posnerRobinson (A : ℕ → Bool) :
    ∃ G : ℕ → Bool,
      Cantor.jump G ≡ₜ Cantor.join A (Cantor.jump (fun _ : ℕ => false)) ∧
      A ≤ₜ Cantor.jump G ∧
      Cantor.jump (fun _ : ℕ => false) ≤ₜ Cantor.jump G ∧
      Cantor.join A G ≤ₜ Cantor.jump G ∧
      (Cantor.jump (fun _ : ℕ => false) ≤ₜ A →
        Cantor.join A G ≡ₜ Cantor.jump G) :=
  ⟨prReal A, posnerRobinson_jump_equiv A, posnerRobinson_A_le_jump A,
    posnerRobinson_zero_le_jump A, posnerRobinson_join_le_jump A,
    posnerRobinson_of_zero_le A⟩

end OracleCode

/-
REMAINING GAP TO FULL POSNER–ROBINSON.

The full theorem asserts, for every noncomputable `A`, a `G` with
`A ⊕ G ≡ᵀ G′` *and no side effect* `0′ ≤ᵀ G′`.  What is proved here is the
relativized-inversion fragment: `G := jReal (A ⊕ 0′)` satisfies `G′ ≡ᵀ A ⊕ 0′`.
This yields the *easy* direction `A ⊕ G ≤ᵀ G′` unconditionally, and the *full*
equivalence only under `0′ ≤ᵀ A` (`posnerRobinson_of_zero_le`).

For general noncomputable `A` the reverse direction `G′ ≤ᵀ A ⊕ G` fails for this
`G`: since `G′ ≡ᵀ A ⊕ 0′`, it would require `0′ ≤ᵀ A ⊕ G`, which the relativized
construction does not deliver (and which is false whenever `A ⊕ G ≱ᵀ 0′`).  This
is not a bookkeeping gap — it is the genuine content of Posner–Robinson: closing
it requires a *different* construction (build `G` by finite extension using `0′`
only to run the construction, then a read-back lemma showing `A ⊕ G` computes
`G′` via convergence witnesses carried by `G` and stage delimiters supplied by
`A`, never consulting `0′`).  That read-back argument, which is what makes `0′`
avoidable, is not reachable by relativizing Friedberg and is left open here.
-/

#print axioms OracleCode.posnerRobinson_jump_equiv
#print axioms OracleCode.posnerRobinson_A_le_jump
#print axioms OracleCode.posnerRobinson_join_le_jump
#print axioms OracleCode.posnerRobinson_of_zero_le
#print axioms OracleCode.posnerRobinson
