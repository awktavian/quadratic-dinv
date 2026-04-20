import Mathlib

open Finset

namespace RationalDinv

-- Definition: Value function $g : \mathbb{Z}^2 \to \mathbb{Z}$
-- $g(x,y) = ab - ax - by$
def gVal (a b : ℕ) (p : ℤ × ℤ) : ℤ :=
  (a : ℤ) * (b : ℤ) - (a : ℤ) * p.1 - (b : ℤ) * p.2

-- The gap set $G$ as a predicate on $\mathbb{Z}^2$:
-- $G = \{(x,y) \in \mathbb{Z}_{\geq 1}^2 : g(x,y) > 0\}$
def GapSet (a b : ℕ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gVal a b p}

-- $G$ is finite (since $g(x,y) > 0$ with $x \geq 1, y \geq 1$ forces $x \leq b-1, y \leq a-1$).
-- We realize it as a Finset for computational purposes.
def gapFinset (a b : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))).filter
    fun p => decide (0 < gVal a b p)

-- Correctness: gapFinset represents GapSet
theorem mem_gapFinset_iff (a b : ℕ) (p : ℤ × ℤ) :
    p ∈ gapFinset a b ↔ p ∈ GapSet a b := by
  sorry

-- Definition: Poset structure on $G$
-- $i \preceq j$ iff $j$ is weakly southwest of $i$: $j.1 \leq i.1 \land j.2 \leq i.2$
def gapLE (_ _ : ℕ) (i j : ℤ × ℤ) : Prop := j.1 ≤ i.1 ∧ j.2 ≤ i.2

-- Definition: Subdiagram (upward closed subset of $G$)
-- A subdiagram is $D \subseteq G$ such that if $i \in D$ and $i \preceq j$ with $j \in G$,
-- then $j \in D$.
def IsSubdiagram (a b : ℕ) (D : Finset (ℤ × ℤ)) : Prop :=
  D ⊆ gapFinset a b ∧
  ∀ i ∈ D, ∀ j ∈ gapFinset a b, gapLE a b i j → j ∈ D

-- Definition: Arm and leg lengths
-- $\mathrm{arm}_D(c) = \max\{k \geq 0 : (c.1 + k, c.2) \in D\}$
-- This counts how many cells of $D$ lie weakly east of $c$ in the same row, minus 1.
-- Equivalently, $\mathrm{arm}_D(c)$ is the number of cells strictly east of $c$ in $D$.
def armLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
    fun p => (p.1 - c.1).toNat).sup id

-- $\mathrm{leg}_D(c) = \max\{k \geq 0 : (c.1, c.2 + k) \in D\}$
-- This counts how many cells of $D$ lie strictly north of $c$ in the same column.
def legLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2).image
    fun p => (p.2 - c.2).toNat).sup id

-- Correctness: armLength achieves its max
theorem armLength_spec (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1 + ↑(armLength D c), c.2) ∈ D ∧
    ∀ k : ℕ, (c.1 + ↑k, c.2) ∈ D → k ≤ armLength D c := by
  sorry

theorem legLength_spec (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1, c.2 + ↑(legLength D c)) ∈ D ∧
    ∀ k : ℕ, (c.1, c.2 + ↑k) ∈ D → k ≤ legLength D c := by
  sorry

-- Definition: Mixed cross hook slopes
-- $m^E_D(c) = \mathrm{leg}_E(c) / (\mathrm{arm}_D(c) + 1)$ as a rational number
-- $M^E_D(c) = (\mathrm{leg}_E(c) + 1) / \mathrm{arm}_D(c)$ (with $+\infty$ when arm = 0)

-- Small slope (always well-defined since denominator $\mathrm{arm}_D(c) + 1 > 0$)
noncomputable def smallSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℚ :=
  (legLength E c : ℚ) / ((armLength D c : ℚ) + 1)

-- Large slope using WithTop ℚ ($+\infty$ when $\mathrm{arm}_D(c) = 0$)
noncomputable def largeSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : WithTop ℚ :=
  if armLength D c = 0 then ⊤
  else ((legLength E c + 1 : ℚ) / (armLength D c : ℚ) : ℚ)

-- Definition: The dinv condition (integer cross-multiplication form)
-- $m^E_D(c) < a/b < M^E_D(c)$ is equivalent to:
--   $b \cdot \mathrm{leg}_E(c) < a \cdot (\mathrm{arm}_D(c) + 1)$
--   AND ($\mathrm{arm}_D(c) = 0$ OR $a \cdot \mathrm{arm}_D(c) < b \cdot (\mathrm{leg}_E(c) + 1)$)
def dinvCond (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Bool :=
  b * legLength E c < a * (armLength D c + 1) &&
  (armLength D c == 0 || a * armLength D c < b * (legLength E c + 1))

-- Correctness: dinvCond is equivalent to the slope condition
theorem dinvCond_iff_slopes (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    dinvCond a b D E c = true ↔
      smallSlope D E c < (a : ℚ) / (b : ℚ) ∧
      ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c := by
  sorry

-- $\mathbf{dinv}^E_D = \#\{c \in D \cap E : m^E_D(c) < a/b < M^E_D(c)\}$
def dinvAsym (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℕ :=
  ((D ∩ E).filter fun c => dinvCond a b D E c).card

-- $\mathbf{dinv}(D,E) = (\mathbf{dinv}^E_D + \mathbf{dinv}^D_E) / 2$ as a real number
noncomputable def crossDinv (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℝ :=
  ((dinvAsym a b D E + dinvAsym a b E D : ℕ) : ℝ) / 2

-- Definition: Kernel function $K : \mathbb{Z} \to \{-1, 0, 1\}$
-- $K(d) = 1_{d \geq 0} - 1_{d \geq a} - 1_{d \geq b} + 1_{d \geq a+b}$
def kernelK (a b : ℕ) (d : ℤ) : ℤ :=
  (if (0 : ℤ) ≤ d then 1 else 0) -
  (if (a : ℤ) ≤ d then 1 else 0) -
  (if (b : ℤ) ≤ d then 1 else 0) +
  (if ((a : ℤ) + (b : ℤ)) ≤ d then 1 else 0)

-- Quadratic form $Q(\mathbf{n}) = \sum_{i,j \in G} K(g(j) - g(i)) n_i n_j$
noncomputable def quadForm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * n i * n j

-- Symmetric bilinear form
-- $B(\mathbf{n}, \mathbf{n}') = \frac{1}{2}(Q(\mathbf{n}+\mathbf{n}') - Q(\mathbf{n}) - Q(\mathbf{n}'))$
noncomputable def bilinForm (a b : ℕ) (n n' : ℤ × ℤ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (quadForm a b (n + n') - quadForm a b n - quadForm a b n')

-- Indicator function for a subdiagram (as a vector in $\mathbb{R}^G$)
noncomputable def indicatorVec (D : Finset (ℤ × ℤ)) : ℤ × ℤ → ℝ :=
  fun p => if p ∈ D then (1 : ℝ) else 0

/-
## Main Theorem

For any subdiagrams $D, E \subseteq G$:
$$B(\mathbf{1}_D, \mathbf{1}_E) = \mathbf{dinv}(D, E).$$
-/
theorem bilinForm_eq_crossDinv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinForm a b (indicatorVec D) (indicatorVec E) = crossDinv a b D E := by
  sorry

-- ============================================================
-- Additional definitions for Theorems 1.1 and 1.3
-- ============================================================

-- The cone C_R: non-negative functions on G that are weakly decreasing
-- (larger values southwest, smaller values northeast)
-- n_j ≥ n_i whenever j-i ∈ ⟨(-1,0),(0,-1)⟩, i.e., gapLE a b i j (j is southwest of i)
def IsCone (a b : ℕ) (n : ℤ × ℤ → ℝ) : Prop :=
  (∀ p ∈ gapFinset a b, (0 : ℝ) ≤ n p) ∧
  (∀ i j, i ∈ gapFinset a b → j ∈ gapFinset a b →
    gapLE a b i j → n j ≥ n i)

-- ℓ∞ norm of n on G: supremum of values over the gap set (0 if G is empty)
noncomputable def linfNorm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  if h : (gapFinset a b).Nonempty then (gapFinset a b).sup' h n else 0

/-
## Theorem 1.1

For any subdiagram D ⊆ G:
  (1) Q(𝟙_D) = dinv(D)   [the quadratic form recovers Gorsky–Mazin dinv]
  (2) If D ≠ ∅ then Q(𝟙_D) > 0
-/

-- (1) Q(𝟙_D) = dinvAsym(D,D), which is the Gorsky–Mazin dinv
theorem quadForm_eq_dinvAsym (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) :
    quadForm a b (indicatorVec D) = dinvAsym a b D D := by
  sorry

-- (2) If D ≠ ∅ then Q(𝟙_D) > 0
theorem quadForm_pos_of_nonempty (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hne : D.Nonempty) :
    (0 : ℝ) < quadForm a b (indicatorVec D) := by
  sorry

/-
## Lemma 5.1

Every n ∈ C_R supported on G is a non-negative linear combination of indicator
vectors of subdiagrams: n = ∑ λ_i 𝟙_{D_i} with λ_i > 0 and D_i subdiagrams.
-/
lemma cone_generated_by_subdiagrams (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0) :
    ∃ (k : ℕ) (D : Fin k → Finset (ℤ × ℤ)) (λv : Fin k → ℝ),
      (∀ i, (0 : ℝ) < λv i) ∧
      (∀ i, IsSubdiagram a b (D i)) ∧
      (∀ p, n p = ∑ i : Fin k, λv i * indicatorVec (D i) p) ∧
      (∀ i, (D i).Nonempty) ∧
      k ≤ (gapFinset a b).card := by
  sorry

/-
## Theorem 1.3

For n, n' ∈ C_R:
  (1) B(n, n') ≥ 0   [positive semidefiniteness on C_R]
  (2) Q(n) ≥ (1/|G|) · ‖n‖²_∞   [effective lower bound]
-/

-- (1) B(n, n') ≥ 0 for n, n' ∈ C_R
theorem bilinForm_nonneg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n n' : ℤ × ℤ → ℝ)
    (hn : IsCone a b n) (hn' : IsCone a b n')
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0)
    (hn'_supp : ∀ p, p ∉ gapFinset a b → n' p = 0) :
    (0 : ℝ) ≤ bilinForm a b n n' := by
  sorry

-- Q(n) ≥ 0 on C_R (immediate from bilinForm_nonneg with n' = n)
theorem quadForm_nonneg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0) :
    (0 : ℝ) ≤ quadForm a b n := by
  sorry

-- (2) Q(n) ≥ (1/|G|) · ‖n‖²_∞ for n ∈ C_R (with G nonempty)
theorem quadForm_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0)
    (hG : (gapFinset a b).Nonempty) :
    ((gapFinset a b).card : ℝ)⁻¹ * (linfNorm a b n) ^ 2 ≤ quadForm a b n := by
  sorry

end RationalDinv
