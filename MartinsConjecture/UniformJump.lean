/-
The jump is computably uniformly Turing invariant.

Strengthens `JumpInvariance.lean`: not only does `X ≡ₜ Y` imply
`X′ ≡ₜ Y′`, but index witnesses for the former can be transformed into index
witnesses for the latter by a *computable* function of the indices
(`Martin.computablyUniformlyTuringInvariant_jump`).  This places the jump in
the "uniformly invariant" world of Steel and Slaman–Steel, and is the model
example of the hypothesis of Lachlan's theorem.

New infrastructure:
* `exists_code_of_partrec` — a partial recursive function has a single code
  valid for *every* oracle;
* `idCode`, `curry` — s-m-n style code composition with primitive recursive
  encoding arithmetic (`curryEnc`);
* `trE₂` — the encoding-level oracle-splicing translation, jointly primitive
  recursive in the spliced index and the code (uses
  `encode_ofNatCode : encodeCode (ofNatCode i) = i` to absorb the index).
-/
import MartinsConjecture.JumpInvariance

open scoped Computability
open OracleCode

namespace OracleCode

/-- A partial recursive function has one code that works for every oracle. -/
theorem exists_code_of_partrec {f : ℕ →. ℕ} (h : Nat.Partrec f) :
    ∃ c : OracleCode, ∀ O : ℕ →. ℕ, eval O c = f := by
  induction h with
  | zero => exact ⟨.zero, fun O => rfl⟩
  | succ => exact ⟨.succ, fun O => rfl⟩
  | left => exact ⟨.left, fun O => rfl⟩
  | right => exact ⟨.right, fun O => rfl⟩
  | pair _ _ ihf ihh =>
      obtain ⟨cf, hf⟩ := ihf; obtain ⟨ch, hh⟩ := ihh
      exact ⟨.pair cf ch, fun O => by
        funext n
        rw [eval_pair, hf O, hh O]⟩
  | comp _ _ ihf ihh =>
      obtain ⟨cf, hf⟩ := ihf; obtain ⟨ch, hh⟩ := ihh
      exact ⟨.comp cf ch, fun O => by
        funext n
        rw [eval_comp, hf O, hh O]⟩
  | prec _ _ ihf ihh =>
      obtain ⟨cf, hf⟩ := ihf; obtain ⟨ch, hh⟩ := ihh
      exact ⟨.prec cf ch, fun O => by
        show eval O (.prec cf ch) = _
        rw [show eval O (.prec cf ch)
            = fun p => (Nat.unpair p).2.rec (eval O cf (Nat.unpair p).1)
                (fun y IH => IH >>= fun i =>
                  eval O ch (Nat.pair (Nat.unpair p).1 (Nat.pair y i))) from rfl]
        rw [hf O, hh O]⟩
  | rfind _ ihf =>
      obtain ⟨cf, hf⟩ := ihf
      exact ⟨.rfind cf, fun O => by
        funext a
        rw [eval_rfind, hf O]⟩

/-- The identity, as an oracle code. -/
def idCode : OracleCode := .pair .left .right

theorem eval_idCode (O : ℕ →. ℕ) (n : ℕ) : eval O idCode n = Part.some n := by
  rw [idCode, eval_pair_eq]
  show ((Part.some (Nat.unpair n).1).map Nat.pair).bind
      (fun g => (Part.some (Nat.unpair n).2).map g) = _
  rw [Part.map_some, Part.bind_some, Part.map_some, Nat.pair_unpair]

/-- s-m-n / currying: specialize the first component of the input. -/
def curry (c : OracleCode) (n : ℕ) : OracleCode :=
  .comp c (.pair (const n) idCode)

theorem eval_curry (O : ℕ →. ℕ) (c : OracleCode) (n x : ℕ) :
    eval O (curry c n) x = eval O c (Nat.pair n x) := by
  rw [curry, eval_comp, eval_pair_eq, eval_const, eval_idCode]
  rw [Part.map_some, Part.bind_some, Part.map_some]
  exact Part.bind_some _ _

/-- Encoding arithmetic for `curry`; primitive recursive in both arguments. -/
def curryEnc (e n : ℕ) : ℕ := compEnc e (pairEnc (constEnc n) (encodeCode idCode))

theorem encodeCode_curry (c : OracleCode) (n : ℕ) :
    encodeCode (curry c n) = curryEnc (encodeCode c) n := rfl

theorem curryEnc_prim : Primrec₂ curryEnc :=
  compEnc_prim.comp Primrec.fst
    (pairEnc_prim.comp (constEnc_prim.comp Primrec.snd)
      (Primrec.const (encodeCode idCode)))

/-! ### The splicing translation, jointly primrec in the spliced index -/

/-- `trE₂ i e`: translate code number `e` by splicing in code number `i` for
the oracle. -/
def trE₂ (i : ℕ) : ℕ → ℕ := trE (ofNatCode i)

/-- Parameter-uniform course-of-values step: identical to `trStep` except
that the `oracle` case (code number 4) returns the spliced index itself
(justified by `encode_ofNatCode`). -/
def trStep₂ (p : ℕ × List ℕ) : ℕ :=
  if p.2.length = 4 then p.1 else trStep .zero p.2

theorem trStep_congr {L : List ℕ} (h : L.length ≠ 4) (c₁ c₂ : OracleCode) :
    trStep c₁ L = trStep c₂ L := by
  unfold trStep
  by_cases h1 : L.length < 4
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_neg h, if_neg h]

theorem trStep₂_primrec : Primrec trStep₂ :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 4))
    Primrec.fst ((trStep_primrec .zero).comp Primrec.snd)

theorem trStep₂_spec (i n : ℕ) :
    trStep₂ (i, (List.range n).map (trE₂ i)) = trE₂ i n := by
  have hlen : ((List.range n).map (trE₂ i)).length = n := by simp
  by_cases h4 : n = 4
  · subst h4
    rw [trStep₂, if_pos hlen]
    show i = trE (ofNatCode i) 4
    rw [show trE (ofNatCode i) 4 = encodeCode (trOracle (ofNatCode i) (ofNatCode 4)) from rfl]
    rw [show ofNatCode 4 = OracleCode.oracle by simp [ofNatCode]]
    rw [show trOracle (ofNatCode i) .oracle = ofNatCode i from rfl]
    rw [encode_ofNatCode]
  · rw [trStep₂, if_neg (by rwa [hlen])]
    rw [trStep_congr (by rwa [hlen]) .zero (ofNatCode i)]
    exact trStep_spec (ofNatCode i) n

theorem trE₂_primrec : Primrec₂ trE₂ :=
  Primrec.nat_strong_rec _
    ((Primrec.option_some.comp trStep₂_primrec).to₂ :
      Primrec₂ fun (i : ℕ) (L : List ℕ) => some (trStep₂ (i, L)))
    fun i n => congrArg some (trStep₂_spec i n)

end OracleCode

/-! ### Uniform invariance of the jump -/

namespace Martin

open Cantor

private def Qfun : ℕ → ℕ := fun p =>
  compEnc (trE₂ (Nat.unpair p).1 (Nat.unpair p).2) (constEnc (Nat.unpair p).2)

private theorem Qfun_primrec : Primrec Qfun :=
  compEnc_prim.comp
    (trE₂_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair))
    (constEnc_prim.comp (Primrec.snd.comp Primrec.unpair))

/-- A fixed, oracle-independent code for `Qfun`. -/
private noncomputable def cQ : OracleCode :=
  (exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp Qfun_primrec))).choose

private theorem cQ_spec (O : ℕ →. ℕ) (p : ℕ) : eval O cQ p = Part.some (Qfun p) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp Qfun_primrec))).choose_spec O) p

private theorem eval_comp_oracle_curry (J : ℕ →. ℕ) (c : OracleCode) (i e : ℕ) :
    eval J (.comp .oracle (curry c i)) e = eval J c (Nat.pair i e) >>= J := by
  rw [eval_comp, eval_curry, eval_oracle]

/-- The reduction code: query the jump oracle at the translated-and-diagonalized
code number. -/
private noncomputable def redCode (i : ℕ) : OracleCode :=
  .comp .oracle (curry cQ i)

/-- The heart: if `eval B (ofNatCode i) = A` then `redCode i` computes
`jumpFn A` from the oracle `jumpFn B`. -/
private theorem eval_redCode {A B : ℕ →. ℕ} {i : ℕ}
    (hI : eval B (ofNatCode i) = A) :
    eval (jumpFn B) (redCode i) = jumpFn A := by
  funext e
  show eval (jumpFn B) (.comp .oracle (curry cQ i)) e = jumpFn A e
  refine (eval_comp_oracle_curry _ cQ i e).trans ?_
  rw [cQ_spec (jumpFn B) (Nat.pair i e)]
  rw [show (Part.some (Qfun (Nat.pair i e)) >>= jumpFn B)
      = jumpFn B (Qfun (Nat.pair i e)) from Part.bind_some _ _]
  have hq : Qfun (Nat.pair i e)
      = encodeCode (.comp (trOracle (ofNatCode i) (ofNatCode e)) (const e)) := by
    simp [Qfun, Nat.unpair_pair, trE₂, trE, constEnc, encodeCode_comp]
  rw [hq]
  simp only [jumpFn]
  by_cases hj : jumpP A e
  · rw [if_pos ((jumpP_trOracle hI e).mp hj), if_pos hj]
  · rw [if_neg (fun hc => hj ((jumpP_trOracle hI e).mpr hc)), if_neg hj]

/-- **The jump is computably uniformly Turing invariant**: a computable
function transforms index witnesses for `X ≡ₜ Y` into index witnesses for
`X′ ≡ₜ Y′`.  (Model example of uniform invariance in the sense of Steel and
Slaman–Steel; cf. `Martin.UniformlyTuringInvariant`.) -/
theorem computablyUniformlyTuringInvariant_jump :
    ComputablyUniformlyTuringInvariant Cantor.jump := by
  refine ⟨fun p => (encodeCode (redCode p.1), encodeCode (redCode p.2)), ?_, ?_⟩
  · -- computability of the index transformation
    have h1 : Primrec fun i : ℕ => encodeCode (redCode i) := by
      have : ∀ i, encodeCode (redCode i) = compEnc 4 (curryEnc (encodeCode cQ) i) :=
        fun i => rfl
      exact (compEnc_prim.comp (Primrec.const 4)
        (curryEnc_prim.comp (Primrec.const (encodeCode cQ)) Primrec.id)).of_eq
        fun i => (this i).symm
    exact Primrec.to_comp
      (Primrec.pair (h1.comp Primrec.fst) (h1.comp Primrec.snd))
  · rintro X Y i j ⟨hXY, hYX⟩
    constructor
    · -- `redCode i` computes `(jump Y)` from `(jump X)`
      show eval (toPFun (Cantor.jump X)) (ofNatCode (encodeCode (redCode i)))
        = toPFun (Cantor.jump Y)
      rw [ofNatCode_encodeCode, toPFun_jump, toPFun_jump]
      exact eval_redCode hXY
    · show eval (toPFun (Cantor.jump Y)) (ofNatCode (encodeCode (redCode j)))
        = toPFun (Cantor.jump X)
      rw [ofNatCode_encodeCode, toPFun_jump, toPFun_jump]
      exact eval_redCode hYX

#print axioms computablyUniformlyTuringInvariant_jump

end Martin
