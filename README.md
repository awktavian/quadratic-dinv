# A Quadratic Form Generalization of Rational Dinv

[![CI](https://github.com/awktavian/quadratic-dinv/actions/workflows/lean.yml/badge.svg)](https://github.com/awktavian/quadratic-dinv/actions/workflows/lean.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](lean-toolchain)
[![sorry: 0](https://img.shields.io/badge/sorry-0-brightgreen.svg)](QuadraticDinv/solution.lean)

**Paper**: [arXiv:2604.13238](https://arxiv.org/abs/2604.13238) — Yifeng Huang (2026)
**Fork**: [github.com/awktavian/quadratic-dinv](https://github.com/awktavian/quadratic-dinv)
(forked from [AxiomMath/quadratic-dinv](https://github.com/AxiomMath/quadratic-dinv))
**Maintainer**: Tim Jacoby, Awkronos Inc. `<tim@awkronos.com>`

---

## Mathematical Background

Fix coprime integers 1 < a < b. The *gap set* G = {(x,y) ∈ ℤ²≥1 : ab − ax − by > 0} is a
finite partially ordered set where i ⪯ j iff j is weakly southwest of i; the unique maximum
is the SW corner (1,1). *Subdiagrams* are upward-closed (Young) subsets of G. The
*dinv* statistic of Gorsky–Mazin counts cells in a subdiagram D satisfying a slope condition
on arm and leg lengths; it appears in the combinatorics of rational Catalan numbers and
Hilbert schemes. Huang (2026) defines a quadratic form Q on ℝ^G via a kernel K derived from
the generators a, b, proves Q(𝟙_D) = dinv(D), and establishes positivity properties for the
associated bilinear form B on the cone C_R of monotone non-negative functions on G.

---

## What This Fork Adds

The upstream repository (AxiomMath) provides Theorem 1.2 autoformalized by AxiomProver.
This fork extends the formalization to the remaining main results of the paper:

| Theorem | Statement | Status | Method |
|---------|-----------|--------|--------|
| Theorem 1.2 | B(𝟙_D, 𝟙_E) = dinv(D, E) | **PROVED** | AxiomProver (upstream) |
| Theorem 1.1 (i) | Q(𝟙_D) = dinv(D) | **PROVED** | Polarization + Thm 1.2 + symmetry |
| Theorem 1.1 (ii) | D ≠ ∅ → Q(𝟙_D) > 0 | **PROVED** | Minimal-g cell gives dinvCond |
| Lemma 5.1 | C_R = cone{𝟙_D : D subdiagram} | **PROVED** | Canonical level-set decomposition |
| Theorem 1.3 (i) | B(n, n') ≥ 0 for n, n' ∈ C_R | **PROVED** | Lemma 5.1 + bilinearity + Thm 1.2 |
| Theorem 1.3 (ii) | Q(n) ≥ ‖n‖²_∞ / |G| for n ∈ C_R | **PROVED** | Cauchy–Schwarz + diagonal bound |

**Zero sorry.** All stubs in `problem.lean` are closed in `solution.lean`.

---

## Axiom Dependencies

All proofs depend only on the standard Lean 4 kernel axioms:
`Classical.choice`, `propext`, `Quot.sound`, `funext`.

No project-specific axioms are declared. Verify with:
```lean
#print axioms bilinForm_eq_crossDinv
#print axioms quadForm_bound
```

---

## Build

```bash
lake build QuadraticDinv
```

Requires Lean 4.28.0 (see `lean-toolchain`) and Mathlib v4.28.0 (pinned in `lakefile.toml`).
First build fetches Mathlib; subsequent builds use the cache.

Verify zero sorry:
```bash
lake build 2>&1 | grep "declaration uses 'sorry'"
# (no output)
```

---

## File Structure

```
quadratic-dinv/
├── QuadraticDinv/
│   ├── problem.lean       # Spec: definitions and theorem stubs (all sorry)
│   └── solution.lean      # Proofs: closes every stub (0 sorry)
├── lakefile.toml          # Lake build config; Mathlib v4.28.0 pinned
├── lean-toolchain         # leanprover/lean4:v4.28.0
├── lake-manifest.json     # Resolved dependency manifest
└── task.md                # Original AxiomMath task description
```

---

## License

MIT — see [LICENSE](LICENSE).
