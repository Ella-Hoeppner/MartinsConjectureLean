/-
Gödel numbering for oracle computability.

This file adds a Gödel numbering for Mathlib's `Nat.RecursiveIn`, the inductive
characterization of oracle computability due to Duve–Roth (Mathlib
`Mathlib.Computability.RecursiveIn`). The numbering follows the design of
`Nat.Partrec.Code` (Mathlib `Mathlib.Computability.PartrecCode`), with two
deliberate deviations, documented in `blueprint.md`:

* an extra `oracle` constructor (the point of the exercise);
* a plain `rfind` constructor instead of `rfind'`-with-offset, chosen so that
  `eval` matches the constructors of `Nat.RecursiveIn` literally, making
  `exists_code` a direct structural induction in both directions.  (`rfind'`
  is only needed for a step-indexed universal machine, which we do not build.)

Main definitions and results:

* `OracleCode` : codes for oracle machines.
* `OracleCode.eval O c` : the partial function `ℕ →. ℕ` computed by code `c`
  with oracle `O : ℕ →. ℕ`.
* `OracleCode.exists_code : Nat.RecursiveIn {O} f ↔ ∃ c, eval O c = f`.
* `OracleCode.encodeCode / ofNatCode` : numbering, with round-trip lemmas and
  a `Denumerable` instance.
* `OracleCode.const`, primitive recursiveness of the numbering arithmetic
  (`constEnc`, `pairEnc`, `compEnc`) — the ingredients for building
  *primitive recursive families of codes*, used for `O ≤ᵀ O′` in `Jump.lean`.
-/
import Mathlib.Computability.TuringDegree
import Mathlib.Computability.PartrecCode

open scoped Computability

/-- Codes for oracle machines: `Nat.Partrec.Code` plus an `oracle` constructor,
with plain `rfind` instead of `rfind'` (see module docstring). -/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | oracle : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode
  deriving DecidableEq, Inhabited

namespace OracleCode

/-- Evaluation of an oracle code against oracle `O`.  Each clause is chosen to
match the corresponding constructor of `Nat.RecursiveIn` *syntactically*. -/
def eval (O : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => O
  | .pair cf cg => fun n => (Nat.pair <$> eval O cf n <*> eval O cg n)
  | .comp cf cg => fun n => eval O cg n >>= eval O cf
  | .prec cf cg => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval O cf a) fun y IH => do
        let i ← IH
        eval O cg (Nat.pair a (Nat.pair y i))
  | .rfind cf => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval O cf (Nat.pair a n)

@[simp] theorem eval_oracle (O : ℕ →. ℕ) : eval O .oracle = O := rfl

theorem eval_comp (O : ℕ →. ℕ) (cf cg : OracleCode) (n : ℕ) :
    eval O (.comp cf cg) n = eval O cg n >>= eval O cf := rfl

theorem eval_pair (O : ℕ →. ℕ) (cf cg : OracleCode) (n : ℕ) :
    eval O (.pair cf cg) n = (Nat.pair <$> eval O cf n <*> eval O cg n) := rfl

theorem eval_rfind (O : ℕ →. ℕ) (cf : OracleCode) (a : ℕ) :
    eval O (.rfind cf) a
      = Nat.rfind fun n => (fun m => m = 0) <$> eval O cf (Nat.pair a n) := rfl

/-! #### Membership characterizations of `eval`

`ℕ →. ℕ` (`PFun`) is not reducible, which makes `simp`/`rw` on raw
`>>=`/`<$>`/`<*>` expressions involving `eval` fragile.  The lemmas below
characterize membership in `eval` once and for all, term-level, so that
downstream files never have to rewrite under the monad operations. -/

theorem mem_eval_comp {O : ℕ →. ℕ} {cf cg : OracleCode} {n y : ℕ} :
    y ∈ eval O (.comp cf cg) n ↔ ∃ b ∈ eval O cg n, y ∈ eval O cf b :=
  Part.mem_bind_iff

theorem eval_pair_eq (O : ℕ →. ℕ) (cf cg : OracleCode) (n : ℕ) :
    eval O (.pair cf cg) n
      = ((eval O cf n).map Nat.pair).bind fun g => (eval O cg n).map g := rfl

theorem mem_eval_pair {O : ℕ →. ℕ} {cf cg : OracleCode} {n y : ℕ} :
    y ∈ eval O (.pair cf cg) n
      ↔ ∃ a ∈ eval O cf n, ∃ b ∈ eval O cg n, Nat.pair a b = y := by
  rw [eval_pair_eq]
  constructor
  · intro h
    obtain ⟨g, hg, hy⟩ := Part.mem_bind_iff.mp h
    obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).mp hg
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hy
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Part.mem_bind_iff.mpr ⟨Nat.pair a, (Part.mem_map_iff _).mpr ⟨a, ha, rfl⟩,
      (Part.mem_map_iff _).mpr ⟨b, hb, rfl⟩⟩

theorem true_mem_decideMap {o : Part ℕ} :
    true ∈ (fun m => decide (m = 0)) <$> o ↔ 0 ∈ o := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hdec⟩
    rwa [of_decide_eq_true hdec] at hx
  · intro h0
    exact ⟨0, h0, by simp⟩

theorem false_mem_decideMap {o : Part ℕ} :
    false ∈ (fun m => decide (m = 0)) <$> o ↔ ∃ x ∈ o, x ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨x, hx, hdec⟩
    exact ⟨x, hx, of_decide_eq_false hdec⟩
  · rintro ⟨x, hx, hne⟩
    exact ⟨x, hx, decide_eq_false hne⟩

theorem mem_eval_rfind {O : ℕ →. ℕ} {cf : OracleCode} {a v : ℕ} :
    v ∈ eval O (.rfind cf) a
      ↔ 0 ∈ eval O cf (Nat.pair a v)
          ∧ ∀ m < v, ∃ x ∈ eval O cf (Nat.pair a m), x ≠ 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Nat.mem_rfind.mp h
    exact ⟨true_mem_decideMap.mp h1, fun m hm => false_mem_decideMap.mp (h2 hm)⟩
  · rintro ⟨h1, h2⟩
    exact Nat.mem_rfind.mpr
      ⟨true_mem_decideMap.mpr h1, fun {m} hm => false_mem_decideMap.mpr (h2 m hm)⟩

theorem dom_eval_rfind {O : ℕ →. ℕ} {cf : OracleCode} {a : ℕ} :
    (eval O (.rfind cf) a).Dom
      ↔ ∃ n, 0 ∈ eval O cf (Nat.pair a n)
          ∧ ∀ m < n, (eval O cf (Nat.pair a m)).Dom := by
  constructor
  · intro h
    obtain ⟨n, h1, h2⟩ := Nat.rfind_dom.mp h
    exact ⟨n, true_mem_decideMap.mp h1, fun m hm => h2 hm⟩
  · rintro ⟨n, h1, h2⟩
    exact Nat.rfind_dom.mpr ⟨n, true_mem_decideMap.mpr h1, fun {m} hm => h2 m hm⟩

/-- Soundness: everything computed by a code is recursive in the oracle. -/
theorem eval_recursiveIn (O : ℕ →. ℕ) : ∀ c : OracleCode, Nat.RecursiveIn {O} (eval O c)
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .oracle => .oracle O rfl
  | .pair cf cg => .pair (eval_recursiveIn O cf) (eval_recursiveIn O cg)
  | .comp cf cg => .comp (eval_recursiveIn O cf) (eval_recursiveIn O cg)
  | .prec cf cg => .prec (eval_recursiveIn O cf) (eval_recursiveIn O cg)
  | .rfind cf => .rfind (eval_recursiveIn O cf)

/-- Completeness: everything recursive in the oracle has a code. -/
theorem exists_code_of_recursiveIn {O f : ℕ →. ℕ} (h : Nat.RecursiveIn {O} f) :
    ∃ c : OracleCode, eval O c = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g hg => exact ⟨.oracle, by simpa using (Set.mem_singleton_iff.mp hg).symm⟩
  | pair _ _ ihf ihh =>
      obtain ⟨cf, rfl⟩ := ihf; obtain ⟨ch, rfl⟩ := ihh
      exact ⟨.pair cf ch, rfl⟩
  | comp _ _ ihf ihh =>
      obtain ⟨cf, rfl⟩ := ihf; obtain ⟨ch, rfl⟩ := ihh
      exact ⟨.comp cf ch, rfl⟩
  | prec _ _ ihf ihh =>
      obtain ⟨cf, rfl⟩ := ihf; obtain ⟨ch, rfl⟩ := ihh
      exact ⟨.prec cf ch, rfl⟩
  | rfind _ ihf =>
      obtain ⟨cf, rfl⟩ := ihf
      exact ⟨.rfind cf, rfl⟩

/-- The enumeration theorem for oracle computability:
`f` is recursive in `O` iff `f = eval O c` for some code `c`. -/
theorem exists_code {O f : ℕ →. ℕ} : Nat.RecursiveIn {O} f ↔ ∃ c : OracleCode, eval O c = f :=
  ⟨exists_code_of_recursiveIn, fun ⟨c, hc⟩ => hc ▸ eval_recursiveIn O c⟩

/-! ### Numbering -/

/-- Numeric encoding of oracle codes, following `Nat.Partrec.Code.encodeCode`:
nullary constructors get `0,…,4`; composite constructors are encoded as
`n + 5` where the two low bits of `n` determine the constructor. -/
def encodeCode : OracleCode → ℕ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .oracle => 4
  | .pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | .comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | .prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 5
  | .rfind cf => (2 * (2 * encodeCode cf + 1) + 1) + 5

/-- Total decoding function `ℕ → OracleCode`. -/
def ofNatCode : ℕ → OracleCode
  | 0 => .zero
  | 1 => .succ
  | 2 => .left
  | 3 => .right
  | 4 => .oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      omega
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => .pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => .comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => .prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => .rfind (ofNatCode m)

/-- Decoding is a left inverse of encoding. -/
@[simp] theorem ofNatCode_encodeCode : ∀ c : OracleCode, ofNatCode (encodeCode c) = c := by
  intro c
  induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *]

/-- Encoding is a left inverse of decoding. -/
theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      omega
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

instance instDenumerable : Denumerable OracleCode :=
  Denumerable.mk'
    ⟨encodeCode, ofNatCode, ofNatCode_encodeCode, encode_ofNatCode⟩

/-! ### Code constructions and the primitive recursiveness of their numbering -/

/-- A code computing the constant function with value `n` (for any oracle). -/
def const : ℕ → OracleCode
  | 0 => .zero
  | n + 1 => .comp .succ (const n)

@[simp] theorem eval_const (O : ℕ →. ℕ) : ∀ n x, eval O (const n) x = Part.some n
  | 0, x => rfl
  | n + 1, x => by
      show (eval O (const n) x >>= eval O .succ) = _
      rw [eval_const O n x]
      exact (Part.bind_some n (eval O .succ)).trans rfl

/-- Numeric encoding of `const`. -/
def constEnc : ℕ → ℕ := fun n => encodeCode (const n)

/-- Numeric encoding of the `pair` constructor. -/
def pairEnc (a b : ℕ) : ℕ := 2 * (2 * Nat.pair a b) + 5

/-- Numeric encoding of the `comp` constructor. -/
def compEnc (a b : ℕ) : ℕ := 2 * (2 * Nat.pair a b + 1) + 5

@[simp] theorem encodeCode_pair (cf cg : OracleCode) :
    encodeCode (.pair cf cg) = pairEnc (encodeCode cf) (encodeCode cg) := rfl

@[simp] theorem encodeCode_comp (cf cg : OracleCode) :
    encodeCode (.comp cf cg) = compEnc (encodeCode cf) (encodeCode cg) := rfl

theorem constEnc_eq : ∀ n, constEnc n
    = Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => compEnc 1 ih) n
  | 0 => rfl
  | n + 1 => by
      simp only [constEnc, const, encodeCode_comp]
      exact congrArg (compEnc 1) (constEnc_eq n)

theorem pairEnc_prim : Primrec₂ pairEnc := by
  unfold pairEnc
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec₂.natPair))
    (Primrec.const 5)

theorem compEnc_prim : Primrec₂ compEnc := by
  unfold compEnc
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec₂.natPair)
        (Primrec.const 1)))
    (Primrec.const 5)

theorem constEnc_prim : Primrec constEnc := by
  have h : Primrec fun n : ℕ =>
      Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => compEnc 1 ih) n :=
    Primrec.nat_rec' .id (Primrec.const 0)
      ((compEnc_prim.comp (Primrec.const 1) Primrec.snd).comp Primrec.snd).to₂
  exact h.of_eq fun n => (constEnc_eq n).symm

end OracleCode
