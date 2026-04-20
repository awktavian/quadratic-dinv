# CLAUDE.md — quadratic-dinv

Lean 4 formalization of arXiv:2604.13238 (Yifeng Huang, 2026).
Fork: github.com/awktavian/quadratic-dinv

---

## Build

```bash
lake build QuadraticDinv
```

Toolchain: `leanprover/lean4:v4.28.0` (pinned in `lean-toolchain`).
Mathlib: `v4.28.0` (pinned in `lakefile.toml` — do not upgrade without full rebuild and test).

---

## Zero-Sorry Invariant

**Never introduce `sorry`.** This invariant is absolute.

After any proof modification, verify:
```bash
lake build 2>&1 | grep "declaration uses 'sorry'"
```
This must return empty. `lake build` must exit 0.

Do not use grep/regex to count sorry in source — comments and docstrings cause false positives.
The compiler count is the only authoritative source.

---

## Proof Architecture

| File | Role |
|------|------|
| `QuadraticDinv/problem.lean` | Spec: all definitions + theorem stubs. Treat as read-only interface. |
| `QuadraticDinv/solution.lean` | All proofs. Every sorry stub from problem.lean is closed here. |

When adding a proof: implement in `solution.lean`, do not modify stubs in `problem.lean`
unless the definition itself is incorrect.

---

## Key Mathematical Facts for Proof Strategy

**Partial order direction**: `gapLE a b i j` means `j.1 ≤ i.1 ∧ j.2 ≤ i.2` — i.e., j is
*weakly southwest* of i. The SW corner (1,1) is the unique **maximum** of (G, ⪯), not minimum.
This is opposite to the standard Young diagram convention; keep this in mind for monotonicity
arguments.

**Every nonempty subdiagram contains (1,1)**: since (1,1) is the maximum, upward closure forces
(1,1) into any nonempty upward-closed set. This is used in: the positivity proof for Thm 1.1(ii),
the ‖n‖∞ = n(1,1) identity for n ∈ C_R, and the Cauchy–Schwarz bound in Thm 1.3(ii).

**Kernel K**: `kernelK a b d = 1_{0≤d} − 1_{a≤d} − 1_{b≤d} + 1_{a+b≤d}`. Equivalently:
K(d) = 1 for d ∈ [0,a), K(d) = −1 for d ∈ [b,a+b), K(d) = 0 otherwise.
The quadratic form Q sums K(g(j)−g(i))·nᵢ·nⱼ over all i,j ∈ G.

**dinvCond avoids division**: the slope condition m < a/b < M is implemented as integer
cross-multiplication in `dinvCond`, which avoids rational arithmetic and is decidable.
Since gcd(a,b) = 1, all slope inequalities are strict.

**Polarization**: Q(n) = B(n,n) by definition of B as the polarization of Q.
Therefore Thm 1.1(i) follows from Thm 1.2 plus the identity dinv(D,D) = dinvAsym(D,D)
(symmetry of the dinvCond contribution when D = E).

**Lemma 5.1 construction**: given n ∈ C_R, let c₁ < ... < cₖ be the distinct positive values
of n on G, c₀ = 0. Set Dᵢ = {g ∈ G : n(g) ≥ cᵢ} and λᵢ = cᵢ − cᵢ₋₁ > 0.
Then Dᵢ are subdiagrams (upward closure of a level set of a monotone function),
they are nested Dₖ ⊊ ... ⊊ D₁ ⊆ G, k ≤ |G|, and n = ∑ λᵢ 𝟙_{Dᵢ} by telescoping.

**Thm 1.3(i) proof route**: decompose n = ∑ λᵢ 𝟙_{Dᵢ} and n' = ∑ μⱼ 𝟙_{Eⱼ} via Lemma 5.1,
then B(n,n') = ∑ᵢⱼ λᵢμⱼ B(𝟙_{Dᵢ}, 𝟙_{Eⱼ}) = ∑ᵢⱼ λᵢμⱼ dinv(Dᵢ,Eⱼ) ≥ 0
since all λᵢ, μⱼ > 0 and all dinv ≥ 0.

**Thm 1.3(ii) proof route**: Q(n) = B(n,n) = ∑ᵢⱼ λᵢλⱼ dinv(Dᵢ,Dⱼ) ≥ ∑ᵢ λᵢ² dinv(Dᵢ,Dᵢ)
≥ ∑ᵢ λᵢ² (diagonal term, dinv ≥ 1 since Dᵢ ≠ ∅) ≥ (∑ᵢ λᵢ)²/k ≥ (∑ᵢ λᵢ)²/|G|
= ‖n‖²∞/|G| (because ‖n‖∞ = n(1,1) = ∑ᵢ λᵢ for n ∈ C_R).

---

## Axiom Policy

`#print axioms` on any proved theorem must return only:
- `Classical.choice`
- `propext`
- `Quot.sound`
- `funext`

No project-specific axioms permitted. Decompose into sub-theorems with sorry before
introducing an axiom.

---

## Mathlib Usage

Import via `import Mathlib` (already in problem.lean). Use `open Finset` where needed.
Key Mathlib lemmas likely in scope: `Finset.sum_add_distrib`, `Finset.card_filter`,
`Finset.sup'_mem`, `Finset.sum_le_sum`, `inner_mul_le_norm_mul_iff` (Cauchy–Schwarz).

Do not upgrade Mathlib without: (1) updating `lean-toolchain` to match, (2) full `lake build`,
(3) verifying zero-sorry and axiom counts.
