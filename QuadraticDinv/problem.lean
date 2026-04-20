import Mathlib

/-!
# Rational Dinv: Problem Statements

Formalization of arXiv:2604.13238 (Yifeng Huang, 2026):
"A Quadratic Form Generalization of Rational Dinv."

Fix coprime 1 < a < b. The gap set G = {(x,y) ∈ ℤ²_{≥1} : ab − ax − by > 0} carries a
partial order where i ⪯ j iff j is weakly southwest of i (the SW corner (1,1) is the unique
maximum). Subdiagrams are upward closed subsets in this poset.

Main results formalized:
- Theorem 1.2 (autoformalized by AxiomProver): B(𝟙_D, 𝟙_E) = dinv(D, E)
- Theorem 1.1: Q(𝟙_D) = dinv(D), and Q(𝟙_D) > 0 for D ≠ ∅
- Lemma 5.1: every n ∈ C_R decomposes as ∑ λ_i 𝟙_{D_i} with λ_i > 0, D_i subdiagrams
- Theorem 1.3: B(n,n') ≥ 0 for n,n' ∈ C_R; Q(n) ≥ ‖n‖²_∞ / |G|

Budget note: all sorry stubs are proved in solution.lean; this file is the spec only.
-/

open Finset

namespace RationalDinv

-- Definition: Value function $g : \mathbb{Z}^2 \to \mathbb{Z}$, §1 of the paper.
-- $g(x,y) = ab - ax - by$. Treat the generators a = (−1,0), b = (0,−1); then
-- $g(p) = ab + a \cdot p + b \cdot p$ in the paper's additive notation.
def gVal (a b : ℕ) (p : ℤ × ℤ) : ℤ :=
  (a : ℤ) * (b : ℤ) - (a : ℤ) * p.1 - (b : ℤ) * p.2

-- The gap set $G$ as a predicate on $\mathbb{Z}^2$, equation (1) of the paper:
-- $G = \{(x,y) \in \mathbb{Z}_{\geq 1}^2 : g(x,y) > 0\}$
-- For 1 < a < b coprime, G is finite: g(x,y) > 0 forces x ≤ b−1 and y ≤ a−1.
def GapSet (a b : ℕ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gVal a b p}

-- Finite realization of G as a Finset, contained in {1..b} × {1..a}.
def gapFinset (a b : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))).filter
    fun p => decide (0 < gVal a b p)

-- Correctness: gapFinset represents GapSet
-- [proved in solution.lean: mem_gapFinset_iff]

-- Definition: Partial order on G (§1 of the paper).
-- $i \preceq j$ iff $j - i \in \langle a, b \rangle$ (non-negative integer combination of
-- the generators a=(−1,0) and b=(0,−1)), equivalently $j.1 \leq i.1 \land j.2 \leq i.2$.
-- The SOUTHWEST corner (1,1) is the unique MAXIMUM of this poset.
def gapLE (_ _ : ℕ) (i j : ℤ × ℤ) : Prop := j.1 ≤ i.1 ∧ j.2 ≤ i.2

-- Definition: Subdiagram (Dyck path / Young subdiagram of G).
-- D ⊆ G is a subdiagram iff it is upward closed in (G,⪯):
--   if i ∈ D and j ∈ G with i ⪯ j (i.e., j is weakly SW of i), then j ∈ D.
-- Equivalently: D is a Young subdiagram in the usual sense.
-- Note: since (1,1) is the maximum of (G,⪯), every nonempty subdiagram contains (1,1).
def IsSubdiagram (a b : ℕ) (D : Finset (ℤ × ℤ)) : Prop :=
  D ⊆ gapFinset a b ∧
  ∀ i ∈ D, ∀ j ∈ gapFinset a b, gapLE a b i j → j ∈ D

-- Definition: Arm length of c in D.
-- $\mathrm{arm}_D(c) = \max\{k \geq 0 : (c.1 + k, c.2) \in D\}$
-- This is max{k : c − k·(−1,0) ∈ D} in the paper's notation (generator a = (−1,0)).
-- arm = 0 iff c has no proper eastward neighbor in D.
def armLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
    fun p => (p.1 - c.1).toNat).sup id

-- Definition: Leg length of c in D.
-- $\mathrm{leg}_D(c) = \max\{k \geq 0 : (c.1, c.2 + k) \in D\}$
-- This is max{k : c − k·(0,−1) ∈ D} in the paper's notation (generator b = (0,−1)).
-- leg = 0 iff c has no proper northward neighbor in D.
def legLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2).image
    fun p => (p.2 - c.2).toNat).sup id

-- Correctness: armLength achieves its max
-- [proved in solution.lean: armLength_spec]
-- [proved in solution.lean: legLength_spec]

-- Definition: Mixed cross hook slopes (§2 of the paper).
-- For c ∈ D ∩ E, using arm relative to D and leg relative to E:
-- $m^E_D(c) = \mathrm{leg}_E(c) / (\mathrm{arm}_D(c) + 1)$ (always well-defined)
-- $M^E_D(c) = (\mathrm{leg}_E(c) + 1) / \mathrm{arm}_D(c)$ ($+\infty$ when arm = 0)

-- Small slope: always finite since denominator arm_D(c) + 1 ≥ 1.
noncomputable def smallSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℚ :=
  (legLength E c : ℚ) / ((armLength D c : ℚ) + 1)

-- Large slope: +∞ iff arm_D(c) = 0 (c has no eastward neighbor in D).
noncomputable def largeSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : WithTop ℚ :=
  if armLength D c = 0 then ⊤
  else ((legLength E c + 1 : ℚ) / (armLength D c : ℚ) : ℚ)

-- Definition: The dinv condition (integer cross-multiplication form, avoids division).
-- $m^E_D(c) < a/b < M^E_D(c)$ iff:
--   $b \cdot \mathrm{leg}_E(c) < a \cdot (\mathrm{arm}_D(c) + 1)$  [small slope < a/b]
--   AND ($\mathrm{arm}_D(c) = 0$ OR $a \cdot \mathrm{arm}_D(c) < b \cdot (\mathrm{leg}_E(c)+1)$) [a/b < large slope]
-- Since gcd(a,b)=1, the slopes a/b never equals a rational with smaller denominator, so all
-- slope inequalities can be taken strict.
def dinvCond (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Bool :=
  b * legLength E c < a * (armLength D c + 1) &&
  (armLength D c == 0 || a * armLength D c < b * (legLength E c + 1))

-- Correctness: dinvCond is equivalent to the slope condition
-- [proved in solution.lean: dinvCond_iff_slopes]

-- Asymmetric dinv: $\mathbf{dinv}^E_D = \#\{c \in D \cap E : m^E_D(c) < a/b < M^E_D(c)\}$
def dinvAsym (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℕ :=
  ((D ∩ E).filter fun c => dinvCond a b D E c).card

-- Cross-dinv: $\mathbf{dinv}(D,E) = (\mathbf{dinv}^E_D + \mathbf{dinv}^D_E) / 2 \in \frac{1}{2}\mathbb{Z}_{\geq 0}$
-- Satisfies: dinv(D,D) = dinv(D) (the Gorsky–Mazin statistic), and 0 ≤ dinv(D,E) ≤ |D∩E|.
noncomputable def crossDinv (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℝ :=
  ((dinvAsym a b D E + dinvAsym a b E D : ℕ) : ℝ) / 2

-- Definition: Kernel function $K : \mathbb{Z} \to \{-1, 0, 1\}$, §1 of the paper.
-- $K(d) = 1_{d \geq 0} - 1_{d \geq a} - 1_{d \geq b} + 1_{d \geq a+b}$
-- Equivalently: K(d) = 1 if 0 ≤ d < a, K(d) = -1 if b ≤ d < a+b, K(d) = 0 otherwise.
def kernelK (a b : ℕ) (d : ℤ) : ℤ :=
  (if (0 : ℤ) ≤ d then 1 else 0) -
  (if (a : ℤ) ≤ d then 1 else 0) -
  (if (b : ℤ) ≤ d then 1 else 0) +
  (if ((a : ℤ) + (b : ℤ)) ≤ d then 1 else 0)

-- Quadratic form $Q(\mathbf{n}) = \sum_{i,j \in G} K(g(j) - g(i)) \cdot n_i \cdot n_j$, §1 of paper.
-- The kernel K(g(j)-g(i)) counts arrows i→j with weight +1 and i←j with weight −1.
noncomputable def quadForm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * n i * n j

-- Symmetric bilinear form (polarization of Q):
-- $B(\mathbf{n}, \mathbf{n}') = \frac{1}{2}(Q(\mathbf{n}+\mathbf{n}') - Q(\mathbf{n}) - Q(\mathbf{n}'))$
-- B is the unique symmetric bilinear form with B(n,n) = Q(n).
noncomputable def bilinForm (a b : ℕ) (n n' : ℤ × ℤ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (quadForm a b (n + n') - quadForm a b n - quadForm a b n')

-- Indicator function $\mathbf{1}_D \in \mathbb{R}^G$
noncomputable def indicatorVec (D : Finset (ℤ × ℤ)) : ℤ × ℤ → ℝ :=
  fun p => if p ∈ D then (1 : ℝ) else 0

/-!
## Theorem 1.2 (main engine, autoformalized by AxiomProver)

For any subdiagrams $D, E \subseteq G$:
$$B(\mathbf{1}_D, \mathbf{1}_E) = \mathbf{dinv}(D, E).$$

Proof strategy (solution.lean): Show 2·B'(D,E) = |D| − |N(D,U_E)| via arrow counting,
construct blue/red bijections ΦD,E: N(D,U_E) → D_b ⊔ D_r, then
2B(D,E) = dinv^D_E + dinv^E_D = 2·crossDinv(D,E).
-/
-- [proved in solution.lean: bilinForm_eq_crossDinv]

-- ============================================================
-- Additional definitions for Theorems 1.1 and 1.3
-- ============================================================

-- The cone C_R (§1 of the paper): non-negative functions on G that are
-- weakly DECREASING going northeast (equivalently, weakly increasing going SW).
-- The SW corner (1,1) is the maximum of (G,⪯), so every n ∈ C_R achieves ‖n‖_∞ at (1,1).
def IsCone (a b : ℕ) (n : ℤ × ℤ → ℝ) : Prop :=
  (∀ p ∈ gapFinset a b, (0 : ℝ) ≤ n p) ∧
  (∀ i j, i ∈ gapFinset a b → j ∈ gapFinset a b →
    gapLE a b i j → n j ≥ n i)

-- ℓ∞ norm of n on G: supremum of {n(p) : p ∈ G}, or 0 if G is empty.
-- For n ∈ C_R this equals n_{(1,1)} (the SW corner is the maximum of (G,⪯)).
noncomputable def linfNorm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  if h : (gapFinset a b).Nonempty then (gapFinset a b).sup' h n else 0

/-!
## Theorem 1.1

For any subdiagram D ⊆ G:
  (1) Q(𝟙_D) = dinv(D)      [quadratic form recovers Gorsky–Mazin dinv]
  (2) D ≠ ∅ → Q(𝟙_D) > 0

Proof strategy: (1) Q(𝟙_D) = B(𝟙_D,𝟙_D) (polarization) = crossDinv(D,D) (Thm 1.2)
= dinvAsym(D,D) (symmetry). (2) The element d with minimal g-value satisfies arm_D(d) = 0
and leg_D(d) = 0, so dinvCond holds for d (0 < a/b < ⊤), giving dinvAsym ≥ 1.
-/

-- (1) Q(𝟙_D) = dinvAsym(D,D) = dinv(D) in Gorsky–Mazin notation
-- [proved in solution.lean: quadForm_eq_dinvAsym]

-- (2) If D ≠ ∅ then Q(𝟙_D) > 0
-- [proved in solution.lean: quadForm_pos_of_nonempty]

/-!
## Lemma 5.1 (canonical decomposition of C_R)

Every n ∈ C_R supported on G decomposes as n = ∑ λ_i 𝟙_{D_i} with λ_i > 0,
D_i nonempty subdiagrams, and k ≤ |G|.

Canonical construction: let {c_1 < ... < c_k} be the distinct positive values of n on G,
c_0 = 0. Set D_i = {g ∈ G : n_g ≥ c_i} and λ_i = c_i − c_{i-1} > 0. The D_i are nested:
D_k ⊊ ... ⊊ D_1 ⊆ G (strictly, since c_i are distinct). This gives n = ∑ λ_i 𝟙_{D_i}
via telescoping. Note: every nonempty subdiagram contains (1,1) ∈ G, so ‖n‖_∞ = ∑ λ_i.
-/
-- [proved in solution.lean: cone_generated_by_subdiagrams]

/-!
## Theorem 1.3

For n, n' ∈ C_R:
  (1) B(n, n') ≥ 0   [B is non-negative on C_R × C_R]
  (2) Q(n) ≥ (1/|G|) · ‖n‖²_∞   [effective positive definiteness on C_R]

Note: (1) is STRONGER than positive semidefiniteness (which only requires B(n,n) ≥ 0).
It asserts that the cone C_R lies in the positive half-space of B for every fixed n' ∈ C_R.

Proof of (1): decompose via Lemma 5.1, use bilinearity, apply B(𝟙_D,𝟙_E) = dinv(D,E) ≥ 0.
Proof of (2): Q(n) ≥ ∑ λ_i² (diagonal, dinv ≥ 1) ≥ (∑ λ_i)²/|G| (Cauchy–Schwarz)
              ≥ ‖n‖²_∞ / |G| (since ‖n‖_∞ ≤ ∑ λ_i, or = ∑ λ_i via the SW corner).
-/

-- (1) B(n, n') ≥ 0 for n, n' ∈ C_R
-- [proved in solution.lean: bilinForm_nonneg]

-- Q(n) ≥ 0 on C_R (immediate from B(n,n) = Q(n) and bilinForm_nonneg with n' = n)
-- [proved in solution.lean: quadForm_nonneg]

-- (2) Effective bound: Q(n) ≥ (1/|G|) · ‖n‖²_∞ for n ∈ C_R with G nonempty
-- [proved in solution.lean: quadForm_bound]

end RationalDinv
