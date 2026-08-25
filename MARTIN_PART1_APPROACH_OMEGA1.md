# Attacking the incomparable core: the ω₁ approach, and a unified obstruction

*A genuine attempt to prove the incomparable core (the sole open content of Part 1), the approaches tried,
and a precise, unified reason they fail. Negative but diagnostic. The choice-free substrate is
machine-checked in `MartinsConjecture/MartinOmega1Approach.lean`.*

## 0. Target

`IncomparableConstant`: a Turing-invariant `F` with `F X ⊥ᵀ X` on a cone is constant on a cone. Equivalent
(machine-checked, `incomparableConstant_iff_noIncomparableSelfMap`) to:

> **No invariant `F` is Turing-incomparable to its argument on a cone.**

So we may try to derive a **contradiction** from `F X ⊥ᵀ X` on a cone, rather than build a constant.

## 1. Approach A — the F-driven increasing chain

`F` itself can't be iterated (its orbit leaves the cone once `F X ⊥ X`). Iterate the **graph**
`G X = X ⊕ F X` instead:

- `G` is invariant and **increasing** (`G X ≥ᵀ X`), so its orbit never leaves the cone;
- on the incomparability cone `G X >ᵀ X` **strictly** (`F X ≰ᵀ X`).

So the transfinite orbit `X₀, G X₀, G² X₀, …, X_λ = ⊕_{α<λ} X_α, …` is a strictly `≤ᵀ`-increasing chain of
degrees that **never stabilizes** (stabilizing needs `F X_α ≤ᵀ X_α`, which incomparability forbids). The
**successor dynamics are choice-free and unconditional** — this is `graphOrbit_strictMono`, machine-checked.

**The intended contradiction.** A strictly `≤ᵀ`-increasing chain of length `ω₁` injects `ω₁ ↪ ℝ`
(ω₁ distinct degrees ⇒ ω₁ distinct reals, wellordered by the index). **Under AD this is impossible**
(perfect-set property: no uncountable wellordered set of reals). Contradiction ⇒ the core.

## 2. Why Approach A provably fails (a no-go, not a gap)

The successor step is choice-free, but the **limit** step `X_λ = ⊕_{α<λ} X_α` needs a real enumerating the
countable ordinal `λ`. Carrying this to `ω₁` requires `ω₁`-many ordinal codes — *itself* an injection
`ω₁ ↪ ℝ`. So:

> The object whose existence would refute the hypothesis (an increasing `ω₁`-chain of reals) is the *same*
> object AD forbids. Under AD **no such chain exists at all**, regardless of `F`; so `F` provides nothing to
> contradict, and `F X ⊥ X` is consistent with "orbits reach every *countable* ordinal but not `ω₁`."

This is airtight: the approach is **circular / self-defeating** and cannot prove the core under AD. Dodging
via function-composition (`G^{ω·2} = G^ω∘G^ω`, choice-free) only ascends the Martin order of *functions*,
which is unbounded and yields no contradiction; evaluating at a point returns to reals and reinstates the
limit-code need. Reals-vs-functions is the wall.

## 3. Approach B — Fodor on the Church–Kleene pushforward

A different idea, using the invariant ordinal `c(X) = ω₁ˣ` (relativized Church–Kleene; `churchKleene`,
formalized). Compare `ω₁^{F X}` with `ω₁ˣ`; by cone dichotomy one of `<, =, >` holds on a cone.

In the case `ω₁^{F X} < ω₁ˣ` (F is "ordinal-regressive"), the natural move is: push the cone measure to the
**club filter on ω₁** (Martin/Solovay: `X ↦ ω₁ˣ` pushes the cone measure to club) and apply **Fodor** — a
regressive `g : ω₁ → ω₁` is constant on a stationary set — to conclude `ω₁^{F X} = δ₀` is a **fixed** ordinal
on a cone (a "reduce to a fixed hyperarithmetic level" step, à la Lutz's Σ¹₁-bounding).

## 4. The unified obstruction — Approach B hits the SAME wall

To run Fodor we need a well-defined `g : ω₁ → ω₁`. But `φ(X) = ω₁^{F X}` does **not** factor through
`c(X) = ω₁ˣ`: different `X` with the same `ω₁ˣ` can have different `F X` (F sees the whole degree). To define
`g(κ)` we must **pick** an `X` with `ω₁ˣ = κ` for each `κ < ω₁` — again an injection `ω₁ ↪ ℝ`. AD forbids it.
(This is exactly why the formalized `no_omega1_decreasing_conePreserving` needed a *cone-preservation*
hypothesis: cone-preservation canonically ties `F X` to `X`, avoiding the choice. An incomparable `F`
provides no such tie.)

**So both natural approaches die at the identical step:** converting *per-degree* information about `F` into
*per-ordinal* (ω₁-level) information requires selecting degree-representatives for ω₁-many ordinals — the
injection `ω₁ ↪ ℝ` that AD denies.

## 5. The diagnosis (what a proof must supply)

The available AD tools — cone dichotomy and countable completeness — yield only **countable / {0,1}-valued**
information about `F`. Every attempt to lift this to **ω₁-level** information (a chain of length ω₁, a Fodor
regression, an ordinal rank that bites) requires uniform ω₁-many choices, i.e. `ω₁ ↪ ℝ`, which AD forbids.

The **solved** cases escape precisely because they possess a *Turing code* (regressive/uniform: `F X = Φ_e^X`)
or a code-like uniform structure (Lutz's hyperarithmetic Σ¹₁-bounding): a single real that supplies the
ω₁-level information *uniformly, for all degrees at once, with no per-degree choice*. The open **`Am` region**
(`F X ≰ₐ X`, F escapes every finite jump of `X`) has **no such code**.

> **Unified thesis.** The incomparable core is exactly the problem of obtaining *ω₁-level uniform information*
> about a degree-invariant `F` that has **no Turing code**. AD's `¬(ω₁ ↪ ℝ)` forbids manufacturing it by
> choice; the solved cases manufacture it from a code. So a proof must supply that information **structurally**
> — an ∞-Borel code for `F` (the AD⁺ / Steel-conjecture route) or a canonical inner-model object (Siskind).
> This is why the problem is inner-model-theoretic, and the derivation above shows *concretely why*, from two
> failed elementary approaches that die at the same `ω₁ ↪ ℝ` step.

## 6. Status

Not a solve. A genuine attempt that (i) reframes the core as an impossibility, (ii) contributes the
choice-free graph-orbit device (machine-checked), (iii) rules out the increasing-chain approach as
self-defeating under AD, and (iv) shows the Fodor/ordinal approach fails at the identical `ω₁ ↪ ℝ` step —
yielding a precise, unified reason the core resists elementary determinacy methods and must be attacked with
structural (∞-Borel / inner-model) tools.
