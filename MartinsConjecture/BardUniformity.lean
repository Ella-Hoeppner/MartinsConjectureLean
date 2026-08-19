/-
**Toward Bard's Lemma 3.4** (arXiv:1907.10766): a uniformly-invariant function
has a *computable* uniformity function.  Removing this lemma's hypothesis would
upgrade both Lachlan's theorem and Part I (for uniform functions) from
computable uniformity to bare uniform invariance.

Bard's construction encodes an equivalence-witness pair `(i,j)` into unary
prefixes and processes it with fixed machines, so that applying the (arbitrary)
uniformity `u` to *fixed* index pairs yields fixed `f`-level transforms whose
composition is computable in `(i,j)`.

This file builds the reusable fixed machines — **strip-first-bit**, **prepend-0**,
**prepend-1** — as explicit oracle-generic codes, with their `EquivVia` witnesses
`w ≡ᵀ 0⌢w` and `w ≡ᵀ 1⌢w`.  Feeding these fixed equivalences through any
uniformity `u` gives the fixed `f`-level "shift" transforms `β, γ`
(`beta_transform`, `gamma_transform`) that are the load-bearing pieces of the
computable-uniformity construction. -/
import MartinsConjecture.BardLocal
import MartinsConjecture.UniversalCode

open scoped Computability
open OracleCode Cantor

namespace Martin

attribute [local instance] Classical.propDecidable

/-- Strip the first bit: `shiftReal w n = w (n+1)`. -/
def shiftReal (w : ℕ → Bool) : ℕ → Bool := fun n => w (n + 1)

/-- Prepend bit `b`: `preReal b w 0 = b`, `preReal b w (n+1) = w n`. -/
def preReal (b : Bool) (w : ℕ → Bool) : ℕ → Bool := fun n => if n = 0 then b else w (n - 1)

/-- **Strip machine**: `Φ_s^w = shiftReal w`, i.e. query the oracle at `n+1`. -/
def sCode : OracleCode := .comp .oracle .succ

theorem eval_sCode (w : ℕ → Bool) : eval (toPFun w) sCode = toPFun (shiftReal w) := by
  funext n
  rw [sCode, eval_comp,
    show eval (toPFun w) OracleCode.succ n = Part.some (n + 1) from rfl,
    show (Part.some (n + 1) >>= eval (toPFun w) OracleCode.oracle)
      = eval (toPFun w) OracleCode.oracle (n + 1) from Part.bind_some _ _, eval_oracle,
    toPFun_eq_bitg]
  rfl

/-- **Prepend machine** for bit `b`: `Φ_{preCode b}^w = preReal b w`, built with a
`prec` (`n = 0 ↦ b`, `n+1 ↦ w n`). -/
def preCode (b : Bool) : OracleCode :=
  .comp (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
    (.pair (const 0) idCode)

theorem eval_preCode (b : Bool) (w : ℕ → Bool) :
    eval (toPFun w) (preCode b) = toPFun (preReal b w) := by
  have key : ∀ n, eval (toPFun w)
      (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
      (Nat.pair 0 n) = Part.some (bitg (preReal b w) n) := by
    intro n
    induction n with
    | zero =>
      rw [eval_prec_pair]
      show eval (toPFun w) (const (bitg (fun _ => b) 0)) 0 = Part.some (bitg (preReal b w) 0)
      rw [eval_const]; cases b <;> rfl
    | succ m ih =>
      rw [eval_prec_pair] at ih ⊢
      show ((Nat.rec (motive := fun _ => Part ℕ) (eval (toPFun w) (const (bitg (fun _ => b) 0)) 0)
          (fun y IH => IH >>= fun i =>
            eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair y i))) m)
          >>= fun i => eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair m i)))
        = Part.some (bitg (preReal b w) (m + 1))
      rw [ih,
        show (Part.some (bitg (preReal b w) m) >>= fun i =>
            eval (toPFun w) (.comp .oracle (.comp .left .right)) (Nat.pair 0 (Nat.pair m i)))
          = eval (toPFun w) (.comp .oracle (.comp .left .right))
              (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m))) from Part.bind_some _ _,
        eval_comp,
        show eval (toPFun w) (.comp OracleCode.left OracleCode.right)
            (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m))) = Part.some m from by
          rw [eval_comp,
            show eval (toPFun w) OracleCode.right (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m)))
              = Part.some (Nat.pair m (bitg (preReal b w) m)) from by
                show Part.some (Nat.unpair (Nat.pair 0 (Nat.pair m (bitg (preReal b w) m)))).2 = _
                rw [Nat.unpair_pair],
            show (Part.some (Nat.pair m (bitg (preReal b w) m)) >>= eval (toPFun w) OracleCode.left)
              = eval (toPFun w) OracleCode.left (Nat.pair m (bitg (preReal b w) m)) from Part.bind_some _ _,
            eval_left_val]
          show Part.some (Nat.unpair (Nat.pair m (bitg (preReal b w) m))).1 = Part.some m
          rw [Nat.unpair_pair],
        show (Part.some m >>= eval (toPFun w) OracleCode.oracle)
          = eval (toPFun w) OracleCode.oracle m from Part.bind_some _ _, eval_oracle, toPFun_eq_bitg]
      congr 1
  funext n
  rw [preCode, eval_comp, eval_pair_eq, eval_const, eval_idCode]
  simp only [Part.map_some, Part.bind_some]
  rw [show (Part.some (Nat.pair 0 n) >>= eval (toPFun w)
        (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right))))
      = eval (toPFun w) (.prec (const (bitg (fun _ => b) 0)) (.comp .oracle (.comp .left .right)))
          (Nat.pair 0 n) from Part.bind_some _ _, key n, toPFun_eq_bitg]

/-- Stripping the prepended bit is the identity: `shiftReal (preReal b w) = w`. -/
theorem shiftReal_preReal (b : Bool) (w : ℕ → Bool) : shiftReal (preReal b w) = w := by
  funext n; simp [shiftReal, preReal]

/-- **The prepend/strip equivalence**: `w ≡ᵀ (b⌢w)` via the fixed index pair
`(preCode b, sCode)`, for *every* `w`. -/
theorem equivVia_preReal (b : Bool) (w : ℕ → Bool) :
    EquivVia w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) := by
  constructor
  · rw [ofNatCode_encodeCode, eval_preCode]
  · rw [ofNatCode_encodeCode, eval_sCode, shiftReal_preReal]

/-- **The fixed `f`-level "shift" transform** `β` (for `b = false`) / `γ`
(for `b = true`).  Because `(preCode b, sCode)` witnesses `w ≡ᵀ (b⌢w)` for *every*
`w`, applying *any* uniformity function `u` for `F` yields a single fixed index —
`u(⟨preCode b, sCode⟩).1` — that computes `F(b⌢w)` from `F(w)` uniformly in `w`.
This is the load-bearing step of Bard's computable-uniformity construction. -/
theorem shift_transform {F : (ℕ → Bool) → ℕ → Bool} {u : ℕ × ℕ → ℕ × ℕ}
    (hu : ∀ X Y i j, EquivVia X Y i j → EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2)
    (b : Bool) (w : ℕ → Bool) :
    eval (toPFun (F w))
        (ofNatCode (u (encodeCode (preCode b), encodeCode sCode)).1) = toPFun (F (preReal b w)) :=
  (hu w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) (equivVia_preReal b w)).1

/-- The backward fixed transform `β'`/`γ'`: `u(⟨preCode b, sCode⟩).2` computes
`F(w)` from `F(b⌢w)` uniformly in `w`. -/
theorem unshift_transform {F : (ℕ → Bool) → ℕ → Bool} {u : ℕ × ℕ → ℕ × ℕ}
    (hu : ∀ X Y i j, EquivVia X Y i j → EquivVia (F X) (F Y) (u (i, j)).1 (u (i, j)).2)
    (b : Bool) (w : ℕ → Bool) :
    eval (toPFun (F (preReal b w)))
        (ofNatCode (u (encodeCode (preCode b), encodeCode sCode)).2) = toPFun (F w) :=
  (hu w (preReal b w) (encodeCode (preCode b)) (encodeCode sCode) (equivVia_preReal b w)).2

/-! ### The `e`-fold composition of the monoid

To build `β^e` (apply the fixed transform `β` `e` times) we iterate the computable
composition `trE (ofNatCode g)` — keeping the *accumulator* in `trE`'s second
(primrec-friendly) slot, so the fixed step `g` stays in the first slot. -/

/-- `iterTrE g base e` : the index of "run `Φ_base`, with `Φ_g` applied to the
oracle `e` times first".  `Φ_{iterTrE g base e}^Y = Φ_base^{(Φ_g)^e Y}`. -/
def iterTrE (g base : ℕ) (e : ℕ) : ℕ :=
  Nat.rec base (fun _ prev => trE (ofNatCode g) prev) e

@[simp] theorem iterTrE_zero (g base : ℕ) : iterTrE g base 0 = base := rfl

theorem iterTrE_succ (g base e : ℕ) :
    iterTrE g base (e + 1) = trE (ofNatCode g) (iterTrE g base e) := rfl

/-- **The `e`-fold transform.**  If the fixed index `g` transforms `F w ↦ F (σ w)`
for every `w`, then `iterTrE g ⟨oracle⟩ e` transforms `F w ↦ F (σ^[e] w)` — the
`e`-fold iterate of `σ` — uniformly in `w`. -/
theorem eval_iterTrE {F : (ℕ → Bool) → ℕ → Bool} {g : ℕ} {σ : (ℕ → Bool) → (ℕ → Bool)}
    (hg : ∀ w, eval (toPFun (F w)) (ofNatCode g) = toPFun (F (σ w))) :
    ∀ (e : ℕ) (w : ℕ → Bool),
      eval (toPFun (F w)) (ofNatCode (iterTrE g (encodeCode OracleCode.oracle) e))
        = toPFun (F (σ^[e] w)) := by
  intro e
  induction e with
  | zero =>
    intro w
    rw [iterTrE_zero, Function.iterate_zero, id, ofNatCode_encodeCode, eval_oracle]
  | succ e ih =>
    intro w
    rw [iterTrE_succ, eval_trE_comp (hg w) (iterTrE g (encodeCode OracleCode.oracle) e), ih (σ w),
      Function.iterate_succ_apply]

/-! ### The shift-by-`k` reduction (for running `Φ_i` on the tail inside `d`) -/

/-- `addFn ⟨k,n⟩ = k + n` (oracle-free). -/
def addFn (p : ℕ) : ℕ := (Nat.unpair p).1 + (Nat.unpair p).2

theorem addFn_prim : Nat.Primrec addFn :=
  Primrec.nat_iff.mp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair))

/-- Oracle-free code computing `k + n` from `⟨k,n⟩`. -/
noncomputable def addCode : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec addFn_prim)).choose

theorem addCode_spec (O : ℕ →. ℕ) (p : ℕ) : eval O addCode p = Part.some (addFn p) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec addFn_prim)).choose_spec O) p

/-- Base code for the shift: `Φ^w(⟨k,n⟩) = w(k+n)`. -/
noncomputable def shiftBase : OracleCode := .comp .oracle addCode

/-- **Shift-by-`k` index**: `Φ_{shiftIdx k}^w = fun n => w(k+n) = shift(w) k`-fold.
Primitive recursive in `k` (via s-m-n). -/
noncomputable def shiftIdx (k : ℕ) : ℕ := curryEnc (encodeCode shiftBase) k

theorem eval_shiftIdx (w : ℕ → Bool) (k n : ℕ) :
    eval (toPFun w) (ofNatCode (shiftIdx k)) n = Part.some (bitg w (k + n)) := by
  rw [shiftIdx, ← encodeCode_curry, ofNatCode_encodeCode, eval_curry, shiftBase, eval_comp,
    show (eval (toPFun w) addCode (Nat.pair k n) >>= eval (toPFun w) OracleCode.oracle)
      = eval (toPFun w) OracleCode.oracle (addFn (Nat.pair k n)) from by
      rw [addCode_spec]; exact Part.bind_some _ _,
    eval_oracle, toPFun_eq_bitg, addFn, Nat.unpair_pair]

theorem shiftIdx_prim : Primrec shiftIdx :=
  curryEnc_prim.comp (Primrec.const (encodeCode shiftBase)) Primrec.id

/-- `shiftIdx k` really computes the `k`-shifted oracle as a real. -/
theorem eval_shiftIdx_real (w : ℕ → Bool) (k : ℕ) :
    eval (toPFun w) (ofNatCode (shiftIdx k)) = toPFun (fun n => w (k + n)) := by
  funext n; rw [eval_shiftIdx]; rfl

/-! ### The encoding real `enc m t = 0ᵐ 1 t` and its iterate identities -/

/-- `enc m t = 0ᵐ ⌢ 1 ⌢ t`: `m` zeros, then a `1`, then `t`. -/
def enc (m : ℕ) (t : ℕ → Bool) : ℕ → Bool :=
  fun n => if n < m then false else if n = m then true else t (n - m - 1)

/-- `enc (m+1) t` is `enc m t` with a `0` prepended. -/
theorem preReal_false_enc (m : ℕ) (t : ℕ → Bool) : preReal false (enc m t) = enc (m + 1) t := by
  funext n
  simp only [preReal, enc]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- Prepending `1` then `m` zeros builds `enc m t`: `(prepend-0)^[m] (1⌢t) = 0ᵐ 1 t`. -/
theorem iter_preReal_false_true (m : ℕ) (t : ℕ → Bool) :
    (preReal false)^[m] (preReal true t) = enc m t := by
  induction m with
  | zero => funext n; simp [preReal, enc, Function.iterate_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, preReal_false_enc]

/-- Stripping the first bit of `enc (m+1) t` gives `enc m t`. -/
theorem shiftReal_enc_succ (m : ℕ) (t : ℕ → Bool) : shiftReal (enc (m + 1) t) = enc m t := by
  rw [← preReal_false_enc, shiftReal_preReal]

/-- Stripping `m` zeros off `enc m t` recovers `1⌢t`: `(strip)^[m] (0ᵐ 1 t) = 1 t`. -/
theorem iter_shiftReal_enc (m : ℕ) (t : ℕ → Bool) :
    (shiftReal)^[m] (enc m t) = preReal true t := by
  induction m with
  | zero => funext n; simp [enc, preReal, Function.iterate_zero]
  | succ m ih => rw [Function.iterate_succ_apply, shiftReal_enc_succ, ih]

/-! ### Reading the unary index `m` from the oracle (the `rfind` in `d`) -/

/-- `oneMinusFn v = 1 - v` (oracle-free). -/
def oneMinusFn (v : ℕ) : ℕ := 1 - v

theorem oneMinusFn_prim : Nat.Primrec oneMinusFn :=
  Primrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)

noncomputable def oneMinusCode : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec oneMinusFn_prim)).choose

theorem oneMinusCode_spec (O : ℕ →. ℕ) (v : ℕ) : eval O oneMinusCode v = Part.some (1 - v) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec oneMinusFn_prim)).choose_spec O) v

/-- rfind test: `0` exactly when the oracle's `k`-th bit is `1`. -/
noncomputable def mReadTest : OracleCode := .comp oneMinusCode (.comp .oracle .right)

theorem eval_mReadTest (w : ℕ → Bool) (a k : ℕ) :
    eval (toPFun w) mReadTest (Nat.pair a k) = Part.some (1 - bitg w k) := by
  rw [mReadTest, eval_comp, eval_comp,
    show eval (toPFun w) OracleCode.right (Nat.pair a k) = Part.some k from by
      show Part.some (Nat.unpair (Nat.pair a k)).2 = _; rw [Nat.unpair_pair],
    show (Part.some k >>= eval (toPFun w) OracleCode.oracle) = eval (toPFun w) OracleCode.oracle k
      from Part.bind_some _ _, eval_oracle, toPFun_eq_bitg,
    show (Part.some (bitg w k) >>= eval (toPFun w) oneMinusCode)
      = eval (toPFun w) oneMinusCode (bitg w k) from Part.bind_some _ _, oneMinusCode_spec]

/-- **Reading `m`**: on the oracle `enc m t = 0ᵐ 1 t`, `Φ_{mReadCode}` returns `m`. -/
noncomputable def mReadCode : OracleCode := .rfind mReadTest

theorem eval_mRead (m : ℕ) (t : ℕ → Bool) (a : ℕ) :
    eval (toPFun (enc m t)) mReadCode a = Part.some m := by
  rw [Part.eq_some_iff]
  rw [mReadCode, mem_eval_rfind]
  refine ⟨?_, ?_⟩
  · rw [eval_mReadTest, show bitg (enc m t) m = 1 from by simp [bitg, enc]]
    exact Part.mem_some 0
  · intro k hk
    rw [eval_mReadTest, show bitg (enc m t) k = 0 from by simp [bitg, enc, hk]]
    exact ⟨1, Part.mem_some 1, one_ne_zero⟩

/-! ### The tail-run: `Φ_{sel m}` on `shift(w, m+1)`, via `univCode ∘ shiftIdx` -/

/-- Build the universal-machine query: run `Φ_{sel m}` (composed with the shift by
`m+1`) at position `n - m - 1`. -/
noncomputable def buildQueryFn (sel : ℕ → ℕ) (nm : ℕ) : ℕ :=
  Nat.pair (trE₂ (shiftIdx ((Nat.unpair nm).2 + 1)) (sel (Nat.unpair nm).2))
    ((Nat.unpair nm).1 - (Nat.unpair nm).2 - 1)

theorem buildQueryFn_prim {sel : ℕ → ℕ} (hsel : Primrec sel) : Primrec (buildQueryFn sel) :=
  Primrec₂.natPair.comp
    (trE₂_primrec.comp
      (shiftIdx_prim.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
      (hsel.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1))

noncomputable def buildQueryCode (sel : ℕ → ℕ) (hsel : Primrec sel) : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (buildQueryFn_prim hsel)))).choose

theorem buildQueryCode_spec {sel : ℕ → ℕ} (hsel : Primrec sel) (O : ℕ →. ℕ) (nm : ℕ) :
    eval O (buildQueryCode sel hsel) nm = Part.some (buildQueryFn sel nm) :=
  congrFun ((exists_code_of_partrec
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (buildQueryFn_prim hsel)))).choose_spec O) nm

/-- Run the universal machine on the built query. -/
noncomputable def runCode (sel : ℕ → ℕ) (hsel : Primrec sel) : OracleCode :=
  .comp univCode (buildQueryCode sel hsel)

theorem eval_runCode {sel : ℕ → ℕ} (hsel : Primrec sel) (w : ℕ → Bool) (n m : ℕ) :
    eval (toPFun w) (runCode sel hsel) (Nat.pair n m)
      = eval (toPFun (fun p => w (m + 1 + p))) (ofNatCode (sel m)) (n - m - 1) := by
  rw [runCode, eval_comp,
    show (eval (toPFun w) (buildQueryCode sel hsel) (Nat.pair n m) >>= eval (toPFun w) univCode)
      = eval (toPFun w) univCode (buildQueryFn sel (Nat.pair n m)) from by
        rw [buildQueryCode_spec]; exact Part.bind_some _ _,
    eval_univCode, buildQueryFn, Nat.unpair_pair, Nat.unpair_pair]
  simp only [trE₂, eval_trE_comp (eval_shiftIdx_real w (m + 1)) (sel m)]

/-! ### Assembling `d`: region select + the whole machine -/

/-- Region select: `z = ⟨rr, ⟨n, m⟩⟩ ↦ (0ᵐ 1 r)(n)` given `rr = r(n-m-1)`.
`if m < n then rr else if n = m then 1 else 0`. -/
def combineFn (z : ℕ) : ℕ :=
  if (Nat.unpair (Nat.unpair z).2).2 < (Nat.unpair (Nat.unpair z).2).1 then (Nat.unpair z).1
  else if (Nat.unpair (Nat.unpair z).2).1 = (Nat.unpair (Nat.unpair z).2).2 then 1 else 0

theorem combineFn_prim : Nat.Primrec combineFn := by
  refine Primrec.nat_iff.mp ?_
  have hn : Primrec (fun z => (Nat.unpair (Nat.unpair z).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hm : Primrec (fun z => (Nat.unpair (Nat.unpair z).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hrr : Primrec (fun z => (Nat.unpair z).1) := Primrec.fst.comp Primrec.unpair
  exact Primrec.ite (Primrec.nat_lt.comp hm hn) hrr
    (Primrec.ite (Primrec.eq.comp hn hm) (Primrec.const 1) (Primrec.const 0))

noncomputable def combineCode : OracleCode :=
  (exists_code_of_partrec (Nat.Partrec.of_primrec combineFn_prim)).choose

theorem combineCode_spec (O : ℕ →. ℕ) (z : ℕ) : eval O combineCode z = Part.some (combineFn z) :=
  congrFun ((exists_code_of_partrec (Nat.Partrec.of_primrec combineFn_prim)).choose_spec O) z

/-- **The `d`-machine** for the projection `sel`: on `enc m t = 0ᵐ 1 t` it produces
`enc m (Φ_{sel m}^t) = 0ᵐ 1 (Φ_{sel m}^t)` — read `m`, run `Φ_{sel m}` on the tail,
copy the prefix. -/
noncomputable def dCode (sel : ℕ → ℕ) (hsel : Primrec sel) : OracleCode :=
  .comp (.comp combineCode (.pair (runCode sel hsel) idCode)) (.pair idCode mReadCode)

theorem combineFn_val (rr n m : ℕ) :
    combineFn (Nat.pair rr (Nat.pair n m)) = if m < n then rr else if n = m then 1 else 0 := by
  simp only [combineFn, Nat.unpair_pair]

/-- **`d`-machine correctness**: if `Φ_{sel m}^t = r`, then `Φ_{dCode sel}^{0ᵐ 1 t} = 0ᵐ 1 r`. -/
theorem eval_dCode {sel : ℕ → ℕ} (hsel : Primrec sel) (m : ℕ) (t r : ℕ → Bool)
    (hr : eval (toPFun t) (ofNatCode (sel m)) = toPFun r) :
    eval (toPFun (enc m t)) (dCode sel hsel) = toPFun (enc m r) := by
  have htail : (fun p => enc m t (m + 1 + p)) = t := by
    funext p; simp only [enc]; rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega
  have hrr : ∀ n, eval (toPFun (enc m t)) (runCode sel hsel) (Nat.pair n m)
      = Part.some (bitg r (n - m - 1)) := by
    intro n; rw [eval_runCode, htail, hr, toPFun_eq_bitg]
  funext n
  rw [dCode, eval_comp,
    show eval (toPFun (enc m t)) (.pair idCode mReadCode) n = Part.some (Nat.pair n m) from by
      rw [eval_pair_eq, eval_idCode, eval_mRead]; simp only [Part.map_some, Part.bind_some],
    show (Part.some (Nat.pair n m)
        >>= eval (toPFun (enc m t)) (.comp combineCode (.pair (runCode sel hsel) idCode)))
      = eval (toPFun (enc m t)) (.comp combineCode (.pair (runCode sel hsel) idCode)) (Nat.pair n m)
      from Part.bind_some _ _,
    eval_comp,
    show eval (toPFun (enc m t)) (.pair (runCode sel hsel) idCode) (Nat.pair n m)
        = Part.some (Nat.pair (bitg r (n - m - 1)) (Nat.pair n m)) from by
      rw [eval_pair_eq, eval_idCode, hrr]; simp only [Part.map_some, Part.bind_some],
    show (Part.some (Nat.pair (bitg r (n - m - 1)) (Nat.pair n m)) >>= eval (toPFun (enc m t)) combineCode)
      = eval (toPFun (enc m t)) combineCode (Nat.pair (bitg r (n - m - 1)) (Nat.pair n m))
      from Part.bind_some _ _,
    combineCode_spec, combineFn_val, toPFun_eq_bitg]
  congr 1
  by_cases hmn : m < n
  · rw [if_pos hmn]
    simp only [bitg, enc]; rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hmn]
    by_cases hnm : n = m
    · rw [if_pos hnm]; subst hnm; simp [bitg, enc]
    · rw [if_neg hnm]
      simp only [bitg, enc]; rw [if_pos (by omega)]; rfl

/-- **Chain form of the `e`-fold transform.**  If `g` transforms `F (seq k) ↦
F (seq (k+1))` for each `k < e` along a *specific* sequence of reals, then
`iterTrE g ⟨oracle⟩ e` transforms `F (seq 0) ↦ F (seq e)`.  (Needed for the
decode: the strip transform `β'` only holds on `0`-prefixed reals, which is
exactly the chain `enc m y, enc (m-1) y, …` that arises.) -/
theorem eval_iterTrE_chain {F : (ℕ → Bool) → ℕ → Bool} {g : ℕ} :
    ∀ (e : ℕ) (seq : ℕ → (ℕ → Bool)),
      (∀ k, k < e → eval (toPFun (F (seq k))) (ofNatCode g) = toPFun (F (seq (k + 1)))) →
      eval (toPFun (F (seq 0))) (ofNatCode (iterTrE g (encodeCode OracleCode.oracle) e))
        = toPFun (F (seq e)) := by
  intro e
  induction e with
  | zero => intro seq _; rw [iterTrE_zero, ofNatCode_encodeCode, eval_oracle]
  | succ e ih =>
    intro seq hg
    rw [iterTrE_succ,
      eval_trE_comp (hg 0 (Nat.succ_pos e)) (iterTrE g (encodeCode OracleCode.oracle) e)]
    exact ih (fun k => seq (k + 1)) (fun k hk => hg (k + 1) (by omega))

/-! ### The `δ` transforms (running `Φ_i`/`Φ_j` inside the prefix) -/

/-- First/second projection selectors (which index of `⟨i,j⟩` the `d` machine runs). -/
def fstSel : ℕ → ℕ := fun m => (Nat.unpair m).1
def sndSel : ℕ → ℕ := fun m => (Nat.unpair m).2
theorem fstSel_prim : Primrec fstSel := Primrec.fst.comp Primrec.unpair
theorem sndSel_prim : Primrec sndSel := Primrec.snd.comp Primrec.unpair

/-- The two fixed `d` machines: run `Φ_i` (resp. `Φ_j`) on the tail. -/
noncomputable def dFst : OracleCode := dCode fstSel fstSel_prim
noncomputable def dSnd : OracleCode := dCode sndSel sndSel_prim

/-- The fixed pair `(dFst, dSnd)` witnesses `enc ⟨i,j⟩ x ≡ᵀ enc ⟨i,j⟩ y` given
`x ≡ᵀ y via (i,j)`. -/
theorem equivVia_enc {x y : ℕ → Bool} {i j : ℕ} (hxy : EquivVia x y i j) :
    EquivVia (enc (Nat.pair i j) x) (enc (Nat.pair i j) y)
      (encodeCode dFst) (encodeCode dSnd) := by
  refine ⟨?_, ?_⟩
  · rw [ofNatCode_encodeCode, dFst,
      eval_dCode fstSel_prim (Nat.pair i j) x y
        (by rw [show fstSel (Nat.pair i j) = i from by simp [fstSel]]; exact hxy.1)]
  · rw [ofNatCode_encodeCode, dSnd,
      eval_dCode sndSel_prim (Nat.pair i j) y x
        (by rw [show sndSel (Nat.pair i j) = j from by simp [sndSel]]; exact hxy.2)]

/-! ### Assembling the computable uniformity function `v(i,j)` -/

theorem enc_zero (t : ℕ → Bool) : enc 0 t = preReal true t := by
  funext n; cases n <;> simp [enc, preReal]

/-- The 5-fold left-nested composition of indices (`a` applied first). -/
def comp5 (a b c d e : ℕ) : ℕ := trE₂ (trE₂ (trE₂ (trE₂ a b) c) d) e

/-- Chain the five transforms through `comp5`. -/
theorem eval_comp5_transform {F : (ℕ → Bool) → ℕ → Bool} {a b c d e : ℕ}
    {w0 w1 w2 w3 w4 w5 : ℕ → Bool}
    (ha : eval (toPFun (F w0)) (ofNatCode a) = toPFun (F w1))
    (hb : eval (toPFun (F w1)) (ofNatCode b) = toPFun (F w2))
    (hc : eval (toPFun (F w2)) (ofNatCode c) = toPFun (F w3))
    (hd : eval (toPFun (F w3)) (ofNatCode d) = toPFun (F w4))
    (he : eval (toPFun (F w4)) (ofNatCode e) = toPFun (F w5)) :
    eval (toPFun (F w0)) (ofNatCode (comp5 a b c d e)) = toPFun (F w5) := by
  have h1 : eval (toPFun (F w0)) (ofNatCode (trE₂ a b)) = toPFun (F w2) := by
    rw [trE₂, eval_trE_comp ha b, hb]
  have h2 : eval (toPFun (F w0)) (ofNatCode (trE₂ (trE₂ a b) c)) = toPFun (F w3) := by
    rw [trE₂, eval_trE_comp h1 c, hc]
  have h3 : eval (toPFun (F w0)) (ofNatCode (trE₂ (trE₂ (trE₂ a b) c) d)) = toPFun (F w4) := by
    rw [trE₂, eval_trE_comp h2 d, hd]
  rw [comp5, trE₂, eval_trE_comp h3 e, he]

variable {F : (ℕ → Bool) → ℕ → Bool} {u : ℕ × ℕ → ℕ × ℕ}

/-- The forward index: `f(x) → f(1x) → f(0ᵐ1x) → f(0ᵐ1y) → f(1y) → f(y)`. -/
noncomputable def Pidx (u : ℕ × ℕ → ℕ × ℕ) (i j : ℕ) : ℕ :=
  comp5 (u (encodeCode (preCode true), encodeCode sCode)).1
    (iterTrE (u (encodeCode (preCode false), encodeCode sCode)).1
      (encodeCode OracleCode.oracle) (Nat.pair i j))
    (u (encodeCode dFst, encodeCode dSnd)).1
    (iterTrE (u (encodeCode (preCode false), encodeCode sCode)).2
      (encodeCode OracleCode.oracle) (Nat.pair i j))
    (u (encodeCode (preCode true), encodeCode sCode)).2

/-- The backward index: same, but the `δ`-step runs `Φ_j` instead of `Φ_i`. -/
noncomputable def Qidx (u : ℕ × ℕ → ℕ × ℕ) (i j : ℕ) : ℕ :=
  comp5 (u (encodeCode (preCode true), encodeCode sCode)).1
    (iterTrE (u (encodeCode (preCode false), encodeCode sCode)).1
      (encodeCode OracleCode.oracle) (Nat.pair i j))
    (u (encodeCode dFst, encodeCode dSnd)).2
    (iterTrE (u (encodeCode (preCode false), encodeCode sCode)).2
      (encodeCode OracleCode.oracle) (Nat.pair i j))
    (u (encodeCode (preCode true), encodeCode sCode)).2

/-- The decode chain: `β'` strips one `0` at each step of `enc m Y, enc (m-1) Y, …`. -/
theorem decode_chain
    (hu : ∀ X Y i' j', EquivVia X Y i' j' → EquivVia (F X) (F Y) (u (i', j')).1 (u (i', j')).2)
    (Y : ℕ → Bool) (i j : ℕ) :
    eval (toPFun (F (enc (Nat.pair i j) Y)))
        (ofNatCode (iterTrE (u (encodeCode (preCode false), encodeCode sCode)).2
          (encodeCode OracleCode.oracle) (Nat.pair i j)))
      = toPFun (F (preReal true Y)) := by
  have hchain := eval_iterTrE_chain (F := F) (Nat.pair i j)
    (fun k => enc (Nat.pair i j - k) Y) (fun k hk => by
      have e1 : Nat.pair i j - k = (Nat.pair i j - k - 1) + 1 := by omega
      have e2 : Nat.pair i j - (k + 1) = Nat.pair i j - k - 1 := by omega
      rw [e1, e2, ← preReal_false_enc]
      exact unshift_transform hu false (enc (Nat.pair i j - k - 1) Y))
  rw [Nat.sub_self, enc_zero] at hchain
  simpa using hchain

theorem forward_correct
    (hu : ∀ X Y i' j', EquivVia X Y i' j' → EquivVia (F X) (F Y) (u (i', j')).1 (u (i', j')).2)
    {X Y : ℕ → Bool} {i j : ℕ} (hXY : EquivVia X Y i j) :
    eval (toPFun (F X)) (ofNatCode (Pidx u i j)) = toPFun (F Y) := by
  refine eval_comp5_transform (shift_transform hu true X) ?_
    (hu (enc (Nat.pair i j) X) (enc (Nat.pair i j) Y) (encodeCode dFst) (encodeCode dSnd)
      (equivVia_enc hXY)).1 (decode_chain hu Y i j) (unshift_transform hu true Y)
  have := eval_iterTrE (fun w => shift_transform hu false w) (Nat.pair i j) (preReal true X)
  rwa [iter_preReal_false_true] at this

theorem backward_correct
    (hu : ∀ X Y i' j', EquivVia X Y i' j' → EquivVia (F X) (F Y) (u (i', j')).1 (u (i', j')).2)
    {X Y : ℕ → Bool} {i j : ℕ} (hXY : EquivVia X Y i j) :
    eval (toPFun (F Y)) (ofNatCode (Qidx u i j)) = toPFun (F X) := by
  refine eval_comp5_transform (shift_transform hu true Y) ?_
    (hu (enc (Nat.pair i j) X) (enc (Nat.pair i j) Y) (encodeCode dFst) (encodeCode dSnd)
      (equivVia_enc hXY)).2 (decode_chain hu X i j) (unshift_transform hu true X)
  have := eval_iterTrE (fun w => shift_transform hu false w) (Nat.pair i j) (preReal true Y)
  rwa [iter_preReal_false_true] at this

/-- `iterTrE g base` is primitive recursive in the exponent. -/
theorem iterTrE_prim (g base : ℕ) : Primrec (iterTrE g base) := by
  have h : Primrec (fun e : ℕ =>
      Nat.rec (motive := fun _ => ℕ) base (fun _ prev => trE₂ g prev) e) :=
    Primrec.nat_rec' Primrec.id (Primrec.const base)
      ((trE₂_primrec.comp (Primrec.const g) Primrec.snd).comp Primrec.snd).to₂
  exact h.of_eq fun e => rfl

/-- `Pidx u` is primitive recursive in `(i,j)` — `u` is applied only to *fixed*
index pairs (giving constants), then composed by the primrec `trE₂`/`iterTrE`. -/
theorem Pidx_prim : Primrec (fun p : ℕ × ℕ => Pidx u p.1 p.2) := by
  have hij : Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hβ : Primrec (fun p : ℕ × ℕ =>
      iterTrE (u (encodeCode (preCode false), encodeCode sCode)).1
        (encodeCode OracleCode.oracle) (Nat.pair p.1 p.2)) :=
    (iterTrE_prim _ _).comp hij
  have hβ' : Primrec (fun p : ℕ × ℕ =>
      iterTrE (u (encodeCode (preCode false), encodeCode sCode)).2
        (encodeCode OracleCode.oracle) (Nat.pair p.1 p.2)) :=
    (iterTrE_prim _ _).comp hij
  exact (trE₂_primrec.comp
    (trE₂_primrec.comp
      (trE₂_primrec.comp
        (trE₂_primrec.comp (Primrec.const _) hβ)
        (Primrec.const _))
      hβ')
    (Primrec.const _)).of_eq fun p => rfl

theorem Qidx_prim : Primrec (fun p : ℕ × ℕ => Qidx u p.1 p.2) := by
  have hij : Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hβ : Primrec (fun p : ℕ × ℕ =>
      iterTrE (u (encodeCode (preCode false), encodeCode sCode)).1
        (encodeCode OracleCode.oracle) (Nat.pair p.1 p.2)) :=
    (iterTrE_prim _ _).comp hij
  have hβ' : Primrec (fun p : ℕ × ℕ =>
      iterTrE (u (encodeCode (preCode false), encodeCode sCode)).2
        (encodeCode OracleCode.oracle) (Nat.pair p.1 p.2)) :=
    (iterTrE_prim _ _).comp hij
  exact (trE₂_primrec.comp
    (trE₂_primrec.comp
      (trE₂_primrec.comp
        (trE₂_primrec.comp (Primrec.const _) hβ)
        (Primrec.const _))
      hβ')
    (Primrec.const _)).of_eq fun p => rfl

/-- **Bard's Lemma 3.4** (for Turing-invariant functions): a *uniformly*
Turing-invariant function has a *computable* uniformity function.  Hence
`UniformlyTuringInvariant → ComputablyUniformlyTuringInvariant`.

The computable uniformity `v(i,j) = (Pidx u i j, Qidx u i j)` applies the given
(arbitrary) `u` only to the *fixed* index pairs `⟨prepend, strip⟩` and
`⟨dFst, dSnd⟩`, obtaining fixed `f`-level transforms, and composes them with the
`i,j`-indexed powers via the primitive-recursive `trE₂`/`iterTrE`. -/
theorem uti_computable (h : UniformlyTuringInvariant F) :
    ComputablyUniformlyTuringInvariant F := by
  obtain ⟨u, hu⟩ := h
  refine ⟨fun p => (Pidx u p.1 p.2, Qidx u p.1 p.2),
    (Primrec.pair (Pidx_prim) (Qidx_prim)).to_comp, ?_⟩
  intro X Y i j hXY
  exact ⟨forward_correct hu hXY, backward_correct hu hXY⟩

#print axioms eval_dCode
#print axioms forward_correct
#print axioms uti_computable

end Martin
