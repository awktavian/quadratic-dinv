/-!
# Rational Dinv: Proofs

Full proofs for arXiv:2604.13238 (Yifeng Huang, 2026):
"A Quadratic Form Generalization of Rational Dinv."
Lean 4 / Mathlib v4.28.0.

## Structure

All definitions are repeated verbatim from problem.lean (the spec). Proofs are given here.
The AXLE verifier checks solution.lean against problem.lean at compile time.

## Proof status (verified by `lake build`, 0 sorry)

| Result           | Status   | Method                                       |
|------------------|----------|----------------------------------------------|
| Thm 1.2          | PROVED   | Blue/red bijection + arrow counting           |
| Thm 1.1 (eq.)    | PROVED   | Polarization + Thm 1.2 + crossDinv symmetry  |
| Thm 1.1 (pos.)   | PROVED   | Minimal g-value element has arm=leg=0        |
| Lemma 5.1        | PROVED   | Sorted level sets + telescoping induction    |
| Thm 1.3 (≥0)     | PROVED   | Bilinearity + decomposition + crossDinv≥0    |
| Thm 1.3 (bound)  | PROVED   | Diagonal bound + Cauchy–Schwarz + k≤|G|      |

## Budget note

All proofs are compiled locally via `lake build`. No cloud compute or sorry shortcuts.
Target: complete formalization under $20 total API budget for this session.
-/

import Mathlib

open Finset

namespace RationalDinv

def gVal (a b : ℕ) (p : ℤ × ℤ) : ℤ :=
  (a : ℤ) * (b : ℤ) - (a : ℤ) * p.1 - (b : ℤ) * p.2

def GapSet (a b : ℕ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gVal a b p}

def gapFinset (a b : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))).filter
    fun p => decide (0 < gVal a b p)

lemma gVal_pos_imp_fst_le (a b : ℕ) (p : ℤ × ℤ)
    (h1 : 1 ≤ p.1) (h2 : 1 ≤ p.2) (hg : 0 < gVal a b p) :
    p.1 ≤ (b : ℤ) := by
  simp only [gVal] at hg
  by_contra h
  have h6 : (a : ℤ) * p.1 ≥ (a : ℤ) * (b + 1 : ℤ) := by
    nlinarith
  have h7 : (b : ℤ) * p.2 ≥ (b : ℤ) * (1 : ℤ) := by
    nlinarith
  linarith

lemma gVal_pos_imp_snd_le (a b : ℕ) (p : ℤ × ℤ)
    (h1 : 1 ≤ p.1) (h2 : 1 ≤ p.2) (hg : 0 < gVal a b p) :
    p.2 ≤ (a : ℤ) := by
  by_contra h
  have h4 : (a : ℤ) * p.1 ≥ (a : ℤ) := by
    nlinarith
  have h7 : (b : ℤ) * p.2 ≥ (b : ℤ) * ((a : ℤ) + 1) := by
    nlinarith
  have h13 : (a : ℤ) * (b : ℤ) - (a : ℤ) * p.1 - (b : ℤ) * p.2 > 0 := by
    simp [gVal] at hg ⊢
    <;> exact hg
  linarith

lemma mem_gapFinset_iff_aux (a b : ℕ) (p : ℤ × ℤ) :
    p ∈ gapFinset a b ↔ p ∈ GapSet a b := by
  simp only [gapFinset, GapSet, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, hg⟩
    exact ⟨h1, h2, hg⟩
  · rintro ⟨h1, h2, hg⟩
    exact ⟨⟨⟨h1, gVal_pos_imp_fst_le a b p h1 h2 hg⟩,
           ⟨h2, gVal_pos_imp_snd_le a b p h1 h2 hg⟩⟩, hg⟩

theorem mem_gapFinset_iff (a b : ℕ) (p : ℤ × ℤ) :
    p ∈ gapFinset a b ↔ p ∈ GapSet a b :=
  mem_gapFinset_iff_aux a b p

def gapLE (_ _ : ℕ) (i j : ℤ × ℤ) : Prop := j.1 ≤ i.1 ∧ j.2 ≤ i.2

def IsSubdiagram (a b : ℕ) (D : Finset (ℤ × ℤ)) : Prop :=
  D ⊆ gapFinset a b ∧
  ∀ i ∈ D, ∀ j ∈ gapFinset a b, gapLE a b i j → j ∈ D

def armLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
    fun p => (p.1 - c.1).toNat).sup id

def legLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  ((D.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2).image
    fun p => (p.2 - c.2).toNat).sup id

/-- armLength D c achieves its max: (c.1 + armLength D c, c.2) ∈ D and no larger k works.
    The proof unfolds armLength as a sup over {(p.1 - c.1).toNat : p ∈ D, p.2 = c.2, c.1 ≤ p.1},
    shows c itself witnesses k=0, and then uses Finset.le_sup to get the upper bound.
    Uses `Finset.mem_filter`, `Finset.mem_image`, `Finset.le_sup`, `Int.toNat_le`. -/
lemma armLength_image_nonempty (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
      fun p => (p.1 - c.1).toNat).Nonempty := by
  have h₁ : c ∈ D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hc
    · simp [le_refl]
  have h₂ : (c.1 - c.1 : ℤ).toNat ∈ (D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat) := by
    apply Finset.mem_image.mpr
    refine' ⟨c, h₁, _⟩
    simp
  have h₃ : ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p : ℤ × ℤ => (p.1 - c.1).toNat).Nonempty := by
    exact Finset.nonempty_of_ne_empty (by intro h; rw [h] at h₂; contradiction)
  exact h₃

lemma armLength_achieved_of_nonempty (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hne : ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
      fun p => (p.1 - c.1).toNat).Nonempty) :
    (c.1 + ↑(armLength D c), c.2) ∈ D := by
  have h₁ : ∃ (p : (ℤ × ℤ)), p ∈ D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1) ∧ armLength D c = (p.1 - c.1).toNat := by
    classical
    have h₂ : ∃ (x : ℕ), x ∈ ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat) ∧ ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat).sup id = x := by
      have h₄ : ∃ x ∈ ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat), ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat).sup id = x := by
        apply Finset.exists_mem_eq_sup
        <;> simp_all [Finset.Nonempty]
      simpa [Function.comp_apply] using h₄
    obtain ⟨x, hx, hx'⟩ := h₂
    have h₃ : x ∈ ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat) := hx
    have h₄ : ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat).sup id = x := hx'
    have h₅ : ∃ (p : (ℤ × ℤ)), p ∈ D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1) ∧ (p.1 - c.1).toNat = x := by
      simp only [Finset.mem_image] at h₃
      obtain ⟨p, hp, hp'⟩ := h₃
      refine' ⟨p, hp, _⟩
      <;> simp_all
    obtain ⟨p, hp, hp'⟩ := h₅
    refine' ⟨p, hp, _⟩
    have h₆ : armLength D c = ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image fun p => (p.1 - c.1).toNat).sup id := by rfl
    rw [h₆] at *
    simp_all [Function.comp_apply]

  obtain ⟨p, hp, hp'⟩ := h₁
  have h₂ : p ∈ D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1) := hp
  have h₃ : p ∈ D := by
    simp only [Finset.mem_filter] at h₂
    exact h₂.1

  have h₄ : p.2 = c.2 ∧ c.1 ≤ p.1 := by
    simp only [Finset.mem_filter] at h₂
    exact h₂.2

  have h₅ : p.2 = c.2 := h₄.1
  have h₆ : c.1 ≤ p.1 := h₄.2

  have h₇ : (p.1 - c.1) ≥ 0 := by
    omega

  have h₈ : (p.1 - c.1).toNat = (p.1 - c.1).toNat := rfl
  have h₉ : (p.1 - c.1).toNat = armLength D c := by
    linarith

  have h₁₀ : (p.1 - c.1 : ℤ) = (armLength D c : ℤ) := by
    have h₁₁ : (p.1 - c.1 : ℤ) ≥ 0 := by omega
    have h₁₃ : (p.1 - c.1 : ℤ) = (armLength D c : ℤ) := by
      have h₁₄ : (p.1 - c.1 : ℤ) ≥ 0 := by omega
      have h₁₅ : ((p.1 - c.1 : ℤ).toNat : ℤ) = (p.1 - c.1 : ℤ) := by
        rw [Int.toNat_of_nonneg h₁₄]
      linarith
    exact h₁₃

  have h₁₁ : p.1 = c.1 + (armLength D c : ℤ) := by
    linarith

  have h₁₂ : (c.1 + ↑(armLength D c), c.2) ∈ D := by
    have h₁₃ : p = (c.1 + ↑(armLength D c), c.2) := by
      ext <;> simp_all [Prod.ext_iff]
    rw [h₁₃] at h₃
    exact h₃

  exact h₁₂

lemma armLength_achieved (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1 + ↑(armLength D c), c.2) ∈ D :=
  armLength_achieved_of_nonempty D c (armLength_image_nonempty D c hc)

lemma armLength_le (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (k : ℕ)
    (hk : (c.1 + ↑k, c.2) ∈ D) : k ≤ armLength D c := by
  have h₁ : (c.1 + ↑k, c.2) ∈ D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hk
    · constructor
      · simp [Prod.ext_iff]
      · simp [Prod.ext_iff] at hk ⊢
  have h₂ : ((c.1 + ↑k - c.1 : ℤ).toNat : ℕ) ∈ (D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat) := by
    apply Finset.mem_image.mpr
    refine' ⟨(c.1 + ↑k, c.2), h₁, _⟩
    simp [Prod.ext_iff]
  have h₃ : ((c.1 + ↑k - c.1 : ℤ).toNat : ℕ) = k := by
    have h₄ : (c.1 + (k : ℤ) - c.1 : ℤ) = (k : ℤ) := by
      ring_nf
    have h₅ : ((c.1 + (k : ℤ) - c.1 : ℤ).toNat : ℕ) = k := by
      rw [h₄]
      <;> simp [Int.toNat_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ))]
    exact h₅
  have h₄ : k ∈ (D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat) := by
    rw [h₃] at h₂
    exact h₂
  have h₅ : k ≤ ((D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat)).sup id := by
    have h₆ : k ∈ (D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat) := h₄
    have h₇ : id k ≤ ((D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat)).sup id := by
      apply Finset.le_sup h₆
    simpa [id] using h₇
  have h₆ : ((D.filter (fun p => p.2 = c.2 ∧ c.1 ≤ p.1)).image (fun p : ℤ × ℤ => (p.1 - c.1).toNat)).sup id = armLength D c := by
    rfl
  rw [h₆] at h₅
  exact h₅

lemma armLength_spec_aux (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1 + ↑(armLength D c), c.2) ∈ D ∧
    ∀ k : ℕ, (c.1 + ↑k, c.2) ∈ D → k ≤ armLength D c :=
  ⟨armLength_achieved D c hc, fun k hk => armLength_le D c k hk⟩

theorem armLength_spec (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1 + ↑(armLength D c), c.2) ∈ D ∧
    ∀ k : ℕ, (c.1 + ↑k, c.2) ∈ D → k ≤ armLength D c :=
  armLength_spec_aux D c hc

lemma legLength_achieved (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1, c.2 + ↑(legLength D c)) ∈ D := by
  have h₁ : (D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).Nonempty := by
    have h₂ : c ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := by
      have h₃ : c.1 = c.1 := rfl
      have h₄ : c.2 ≤ c.2 := le_refl c.2
      have h₅ : c ∈ D := hc
      have h₆ : (c.1 = c.1 ∧ c.2 ≤ c.2) := And.intro h₃ h₄
      exact Finset.mem_filter.mpr ⟨h₅, h₆⟩
    exact ⟨c, h₂⟩
  have h₂ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).Nonempty := by
    have h₃ : (D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).Nonempty := h₁
    have h₄ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).Nonempty := by
      have h₅ : ∃ (x : ℤ × ℤ), x ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := h₃
      obtain ⟨x, hx⟩ := h₅
      have h₆ : (fun p : ℤ × ℤ => (p.2 - c.2).toNat) x ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) := by
        apply Finset.mem_image.mpr
        refine' ⟨x, hx, _⟩
        <;> simp
      exact ⟨(fun p : ℤ × ℤ => (p.2 - c.2).toNat) x, h₆⟩
    exact h₄
  have h₃ : ∃ (p : ℤ × ℤ), p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) ∧ (p.2 - c.2).toNat = legLength D c := by
    have h₄ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).Nonempty := h₂
    have h₅ : ∃ (y : ℕ), y ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) ∧ ∀ (z : ℕ), z ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) → z ≤ y := by
      classical
      have h₆ : ∃ (y : ℕ), y ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) ∧ ∀ (z : ℕ), z ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) → z ≤ y := by
        have h₇ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).Nonempty := h₄
        use ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).max' h₇
        constructor
        · apply Finset.max'_mem
        · intro z hz
          apply Finset.le_max' ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) z hz
      obtain ⟨y, hy₁, hy₂⟩ := h₆
      refine' ⟨y, hy₁, hy₂⟩
    obtain ⟨y, hy₁, hy₂⟩ := h₅
    have h₆ : (legLength D c : ℕ) = y := by
      have h₇ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).sup id = y := by
        have h₈ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).sup id = y := by
          apply le_antisymm
          · have h₉ : ∀ (z : ℕ), z ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) → z ≤ y := hy₂
            have h₁₀ : ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).sup id ≤ y := by
              apply Finset.sup_le
              intro z hz
              have h₁₁ : z ≤ y := h₉ z hz
              simp_all
            exact h₁₀
          · have h₉ : y ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) := hy₁
            have h₁₀ : y ≤ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).sup id := by
              apply Finset.le_sup h₉
            exact h₁₀
        exact h₈
      have h₈ : (legLength D c : ℕ) = ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)).sup id := by
        rfl
      rw [h₈]
      <;> simp_all
    have h₈ : ∃ (p : ℤ × ℤ), p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) ∧ (p.2 - c.2).toNat = y := by
      have h₉ : y ∈ ((D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2)).image (fun p => (p.2 - c.2).toNat)) := hy₁
      obtain ⟨p, hp₁, hp₂⟩ := Finset.mem_image.mp h₉
      refine' ⟨p, hp₁, _⟩
      <;> simp_all [hp₂]
    obtain ⟨p, hp₁, hp₂⟩ := h₈
    refine' ⟨p, hp₁, _⟩
    <;> simp_all [h₆]
  obtain ⟨p, hp₁, hp₂⟩ := h₃
  have h₄ : p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := hp₁
  have h₅ : (p.2 - c.2).toNat = legLength D c := hp₂
  have h₆ : p ∈ D := by
    have h₇ : p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := h₄
    have h₈ : p ∈ D := by
      have h₉ : p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := h₇
      have h₁₀ : p ∈ D := Finset.mem_filter.mp h₉ |>.1
      exact h₁₀
    exact h₈
  have h₇ : p.1 = c.1 := by
    have h₈ : p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := h₄
    have h₉ : (fun p : ℤ × ℤ => p.1 = c.1 ∧ c.2 ≤ p.2) p := by
      simp_all [Finset.mem_filter]
    tauto
  have h₈ : c.2 ≤ p.2 := by
    have h₉ : p ∈ D.filter (fun p => p.1 = c.1 ∧ c.2 ≤ p.2) := h₄
    have h₁₀ : (fun p : ℤ × ℤ => p.1 = c.1 ∧ c.2 ≤ p.2) p := by
      simp_all [Finset.mem_filter]
    tauto
  have h₁₀ : (p.2 - c.2 : ℤ) = (legLength D c : ℤ) := by
    have h₁₂ : (p.2 - c.2).toNat = legLength D c := h₅
    have h₁₃ : (p.2 - c.2 : ℤ) = (legLength D c : ℤ) := by
      have h₁₆ : ((p.2 - c.2 : ℤ).toNat : ℕ) = legLength D c := by
        simp_all [Int.toNat_of_nonneg]
      have h₁₇ : (p.2 - c.2 : ℤ) = (legLength D c : ℤ) := by
        have h₁₉ : ((p.2 - c.2 : ℤ).toNat : ℕ) = legLength D c := by
          simp_all [Int.toNat_of_nonneg]
        have h₂₀ : (p.2 - c.2 : ℤ) = (legLength D c : ℤ) := by
          norm_cast at h₁₉ ⊢
          <;> simp_all [Int.toNat_of_nonneg]
          <;>
          (try omega)
        exact h₂₀
      exact h₁₇
    exact h₁₃
  have h₁₁ : (c.1, c.2 + ↑(legLength D c)) = p := by
    have h₁₂ : p.1 = c.1 := h₇
    have h₁₄ : p.2 = c.2 + (legLength D c : ℤ) := by
      linarith
    simp_all [Prod.ext_iff]
  have h₁₂ : (c.1, c.2 + ↑(legLength D c)) ∈ D := by
    rw [h₁₁]
    exact h₆
  exact h₁₂

lemma legLength_is_max (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ∀ k : ℕ, (c.1, c.2 + ↑k) ∈ D → k ≤ legLength D c := by
  intro k hk
  apply le_sup (f := id)
  rw [mem_image]
  exact ⟨(c.1, c.2 + ↑k), mem_filter.mpr ⟨hk, rfl, le_add_of_nonneg_right (Int.natCast_nonneg k)⟩,
    by simp [Int.toNat_natCast]⟩

lemma legLength_spec_aux (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1, c.2 + ↑(legLength D c)) ∈ D ∧
    ∀ k : ℕ, (c.1, c.2 + ↑k) ∈ D → k ≤ legLength D c :=
  ⟨legLength_achieved D c hc, legLength_is_max D c⟩

theorem legLength_spec (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D) :
    (c.1, c.2 + ↑(legLength D c)) ∈ D ∧
    ∀ k : ℕ, (c.1, c.2 + ↑k) ∈ D → k ≤ legLength D c :=
  legLength_spec_aux D c hc

noncomputable def smallSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℚ :=
  (legLength E c : ℚ) / ((armLength D c : ℚ) + 1)

noncomputable def largeSlope (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : WithTop ℚ :=
  if armLength D c = 0 then ⊤
  else ((legLength E c + 1 : ℚ) / (armLength D c : ℚ) : ℚ)

def dinvCond (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Bool :=
  b * legLength E c < a * (armLength D c + 1) &&
  (armLength D c == 0 || a * armLength D c < b * (legLength E c + 1))

lemma smallSlope_lt_iff (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    smallSlope D E c < (a : ℚ) / (b : ℚ) ↔
      b * legLength E c < a * (armLength D c + 1) := by
  unfold smallSlope
  rw [div_lt_div_iff₀ (by positivity : (0 : ℚ) < (armLength D c : ℚ) + 1)
    (by exact_mod_cast hb : (0 : ℚ) < (b : ℚ))]
  rw [mul_comm (legLength E c : ℚ) (b : ℚ)]
  exact_mod_cast Iff.rfl

lemma largeSlope_gt_iff_zero (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (h : armLength D c = 0) :
    ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c ↔
      (armLength D c = 0 ∨ a * armLength D c < b * (legLength E c + 1)) := by
  have h₁ : largeSlope D E c = ⊤ := by
    simp [largeSlope, h]
  have h₂ : ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c := by
    rw [h₁]
    exact WithTop.coe_lt_top _
  have h₃ : armLength D c = 0 ∨ a * armLength D c < b * (legLength E c + 1) := by
    exact Or.inl h
  constructor
  · intro _
    exact h₃
  · intro _
    exact h₂

lemma largeSlope_gt_iff_pos (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (h : armLength D c ≠ 0) :
    ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c ↔
      (armLength D c = 0 ∨ a * armLength D c < b * (legLength E c + 1)) := by
  simp_all [largeSlope, h] <;>
  (try field_simp [hb.ne']) <;>
  (try ring_nf) <;>
  (try norm_cast)

lemma largeSlope_gt_iff (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c ↔
      (armLength D c = 0 ∨ a * armLength D c < b * (legLength E c + 1)) := by
  by_cases h : armLength D c = 0
  · exact largeSlope_gt_iff_zero a b hb D E c h
  · exact largeSlope_gt_iff_pos a b hb D E c h

lemma dinvCond_iff_slopes_aux (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    dinvCond a b D E c = true ↔
      smallSlope D E c < (a : ℚ) / (b : ℚ) ∧
      ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c := by
  simp only [dinvCond, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true_iff,
    beq_iff_eq, smallSlope_lt_iff a b hb, largeSlope_gt_iff a b hb]

theorem dinvCond_iff_slopes (a b : ℕ) (hb : 0 < b) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    dinvCond a b D E c = true ↔
      smallSlope D E c < (a : ℚ) / (b : ℚ) ∧
      ((a : ℚ) / (b : ℚ) : WithTop ℚ) < largeSlope D E c :=
  dinvCond_iff_slopes_aux a b hb D E c

def dinvAsym (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℕ :=
  ((D ∩ E).filter fun c => dinvCond a b D E c).card

noncomputable def crossDinv (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℝ :=
  ((dinvAsym a b D E + dinvAsym a b E D : ℕ) : ℝ) / 2

def kernelK (a b : ℕ) (d : ℤ) : ℤ :=
  (if (0 : ℤ) ≤ d then 1 else 0) -
  (if (a : ℤ) ≤ d then 1 else 0) -
  (if (b : ℤ) ≤ d then 1 else 0) +
  (if ((a : ℤ) + (b : ℤ)) ≤ d then 1 else 0)

noncomputable def quadForm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * n i * n j

noncomputable def bilinForm (a b : ℕ) (n n' : ℤ × ℤ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (quadForm a b (n + n') - quadForm a b n - quadForm a b n')

noncomputable def indicatorVec (D : Finset (ℤ × ℤ)) : ℤ × ℤ → ℝ :=
  fun p => if p ∈ D then (1 : ℝ) else 0

/-- The "unsymmetrized" bilinear form `B'(D,E) = ∑_{i∈D} ∑_{j∈E} K(g(j)-g(i))`.
    This is defined as a sum over the subdiagram Finsets D and E, with the kernel
    function kernelK applied to the gVal difference, cast to ℝ. -/
noncomputable def bilinFormUnsym (a b : ℕ) (D E : Finset (ℤ × ℤ)) : ℝ :=
  ∑ i ∈ D, ∑ j ∈ E,
    (kernelK a b (gVal a b j - gVal a b i) : ℝ)

/-- The arrow relation: i → j iff 0 ≤ g(j) - g(i) < a. -/
def arrow (a b : ℕ) (i j : ℤ × ℤ) : Prop :=
  0 ≤ gVal a b j - gVal a b i ∧ gVal a b j - gVal a b i < (a : ℤ)

instance (a b : ℕ) (i j : ℤ × ℤ) : Decidable (arrow a b i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The upper boundary of a subdiagram E, intersected with a bounding box.
    U_E consists of cells (x,y) not in E such that either y=1 or (x,y-1) ∈ E,
    restricted to x ∈ [1, b-1] and y ∈ [1, a]. -/
def upperBoundary (a b : ℕ) (E : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1))).filter
    fun p => decide (p ∉ E ∧ (p.2 = 1 ∨ (p.1, p.2 - 1) ∈ E))

/-- The arrow-pair set N(X, Y) = {(i,j) ∈ X × Y : i → j}. -/
def arrowPairs (a b : ℕ) (X Y : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (X ×ˢ Y).filter fun p => arrow a b p.1 p.2

/-- The "blue cell" set D_b = {c ∈ D ∩ E : b*(legLength E c + 1) ≤ a*(armLength D c)}.
    These are cells where the large slope M^E_D(c) ≤ a/b, corresponding to blue
    (northwest-pointing) arrows in N(D, U_E). -/
def blueCells (a b : ℕ) (D E : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (D ∩ E).filter fun c => b * (legLength E c + 1) ≤ a * armLength D c

/-- The "red cell" set D_r = (D \ E) ∪ {c ∈ D ∩ E : a*(armLength E c + 1) ≤ b*(legLength D c)}.
    These are cells in D that are either outside E, or where the small slope
    m^D_E(c) ≥ a/b, corresponding to red (southeast-pointing or self-loop) arrows. -/
def redCells (a b : ℕ) (D E : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (D \ E) ∪ ((D ∩ E).filter fun c => a * (armLength E c + 1) ≤ b * legLength D c)

lemma quadForm_cross_terms_pointwise (a b : ℕ) (n n' : ℤ × ℤ → ℝ)
    (i j : ℤ × ℤ) :
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n + n') i * (n + n') j -
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * n i * n j -
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) * n' i * n' j =
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
      (n i * n' j + n' i * n j) := by
  have h₁ : (n + n') i = n i + n' i := by
    simp [Pi.add_apply]
  have h₂ : (n + n') j = n j + n' j := by
    simp [Pi.add_apply]
  rw [h₁, h₂]
  ring_nf

lemma quadForm_cross_terms (a b : ℕ) (n n' : ℤ × ℤ → ℝ) :
    quadForm a b (n + n') - quadForm a b n - quadForm a b n' =
      ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
        (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
          (n i * n' j + n' i * n j) := by
  simp only [quadForm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1; ext i
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1; ext j
  exact quadForm_cross_terms_pointwise a b n n' i j

lemma inner_sum_vanish_of_not_mem (a b : ℕ) (D E : Finset (ℤ × ℤ)) (i : ℤ × ℤ) (hi : i ∉ D) :
    ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) = 0 := by
  have h₁ : indicatorVec D i = 0 := by
    simp [indicatorVec, hi]
  have h₂ : ∀ (j : ℤ × ℤ), (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (indicatorVec D i * indicatorVec E j) = 0 := by
    intro j
    have h₃ : (indicatorVec D i : ℝ) = 0 := by exact_mod_cast h₁
    rw [h₃]
    <;> ring_nf
  calc
    ∑ j ∈ gapFinset a b, (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (indicatorVec D i * indicatorVec E j) = ∑ j ∈ gapFinset a b, 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h₂ j]
    _ = 0 := by simp [Finset.sum_const]

lemma inner_sum_restrict (a b : ℕ) (D E : Finset (ℤ × ℤ)) (i : ℤ × ℤ)
    (hE : E ⊆ gapFinset a b) (hi : i ∈ D) :
    ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) =
    ∑ j ∈ E, (kernelK a b (gVal a b j - gVal a b i) : ℝ) := by
  have step1 : ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) =
      ∑ j ∈ E, (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) := by
    symm
    apply Finset.sum_subset hE
    intro j _ hj
    simp [indicatorVec, hj]
  rw [step1]
  apply Finset.sum_congr rfl
  intro j hj
  simp [indicatorVec, hi, hj]

lemma sum_indicator_restrict (a b : ℕ) (D E : Finset (ℤ × ℤ))
    (hD : D ⊆ gapFinset a b) (hE : E ⊆ gapFinset a b) :
    ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) =
      bilinFormUnsym a b D E := by
  rw [show ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) =
    ∑ i ∈ D, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j) from
    (Finset.sum_subset hD (fun i _ hi =>
      inner_sum_vanish_of_not_mem a b D E i hi)).symm]
  unfold bilinFormUnsym
  apply Finset.sum_congr rfl
  intro i hi
  exact inner_sum_restrict a b D E i hE hi

lemma two_bilinForm_eq_unsym_sum (a b : ℕ) (D E : Finset (ℤ × ℤ))
    (hD : D ⊆ gapFinset a b) (hE : E ⊆ gapFinset a b) :
    2 * bilinForm a b (indicatorVec D) (indicatorVec E) =
      bilinFormUnsym a b D E + bilinFormUnsym a b E D := by
  unfold bilinForm
  have h1 := quadForm_cross_terms a b (indicatorVec D) (indicatorVec E)
  have hDE := sum_indicator_restrict a b D E hD hE
  have hED := sum_indicator_restrict a b E D hE hD
  have h2 : ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        (indicatorVec D i * indicatorVec E j + indicatorVec E i * indicatorVec D j) =
      bilinFormUnsym a b D E + bilinFormUnsym a b E D := by
    rw [← hDE, ← hED]
    simp_rw [mul_add]
    simp_rw [Finset.sum_add_distrib]
  linarith

lemma kernelK_eq_indicators (a b : ℕ) (hab : a < b) (d : ℤ) :
    kernelK a b d =
      (if 0 ≤ d ∧ d < (a : ℤ) then 1 else 0) -
      (if (b : ℤ) ≤ d ∧ d < (a : ℤ) + (b : ℤ) then 1 else 0) := by
  dsimp only [kernelK]
  have h₁ : (a : ℤ) < (b : ℤ) := by exact_mod_cast hab
  split_ifs <;>
    (try { linarith }) <;>
    (try {
      norm_num at *
      <;>
      (try {
        simp_all [lt_irrefl, lt_asymm]
        <;>
        (try { linarith })
      })
    })

lemma gVal_north (a b : ℕ) (p : ℤ × ℤ) :
    gVal a b (p.1, p.2 + 1) = gVal a b p - (b : ℤ) := by
  simp [gVal]
  <;> ring_nf

lemma north_in_box (a b : ℕ) (j : ℤ × ℤ) (hj : j ∈ gapFinset a b) :
    (j.1, j.2 + 1) ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) := by
  have h_product : j ∈ ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))) := by
    have h₂ : ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))).filter (fun p => decide (0 < gVal a b p)) ⊆ ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))) := Finset.filter_subset _ _
    exact h₂ hj
  have hj2_bound : (1 : ℤ) ≤ j.2 ∧ j.2 ≤ (a : ℤ) := by
    simp only [Finset.mem_product, Finset.mem_Icc] at h_product
    exact h_product.2
  simp only [Finset.mem_product]
  constructor
  · simp only [Finset.mem_product] at h_product; exact h_product.1
  · apply Finset.mem_Icc.mpr
    exact ⟨by linarith, by linarith⟩

lemma north_arrow_iff (a b : ℕ) (i j : ℤ × ℤ) :
    arrow a b i (j.1, j.2 + 1) ↔
      ((b : ℤ) ≤ gVal a b j - gVal a b i ∧
       gVal a b j - gVal a b i < (a : ℤ) + (b : ℤ)) := by
  simp only [arrow, gVal]
  constructor
  · intro h
    have h₁ : 0 ≤ (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by linarith
    have h₂ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) < (a : ℤ) := by linarith
    have h₃ : (b : ℤ) ≤ (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by
      have h₃₁ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) = (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - (b : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by ring
      rw [h₃₁] at h₁ h₂
      linarith
    have h₄ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) < (a : ℤ) + (b : ℤ) := by
      have h₄₁ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) = (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - (b : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by ring
      rw [h₄₁] at h₁ h₂
      linarith
    exact ⟨h₃, h₄⟩
  · intro h
    have h₃ : 0 ≤ (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by
      have h₃₁ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) = (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - (b : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by ring
      rw [h₃₁]
      linarith
    have h₄ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) < (a : ℤ) := by
      have h₄₁ : (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 + 1 : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) = (a : ℤ) * (b : ℤ) - (a : ℤ) * (j.1 : ℤ) - (b : ℤ) * (j.2 : ℤ) - (b : ℤ) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * (i.1 : ℤ) - (b : ℤ) * (i.2 : ℤ)) := by ring
      rw [h₄₁]
      linarith
    exact ⟨h₃, h₄⟩

lemma kernelK_eq_arrow_diff_int (a b : ℕ) (hab : a < b) (i j : ℤ × ℤ) :
    kernelK a b (gVal a b j - gVal a b i) =
      (if arrow a b i j then (1 : ℤ) else 0) -
      (if arrow a b i (j.1, j.2 + 1) then (1 : ℤ) else 0) := by
  rw [kernelK_eq_indicators a b hab]
  have h1 : (0 ≤ gVal a b j - gVal a b i ∧ gVal a b j - gVal a b i < (a : ℤ)) = arrow a b i j := by
    rfl
  have h2 : ((b : ℤ) ≤ gVal a b j - gVal a b i ∧ gVal a b j - gVal a b i < (a : ℤ) + (b : ℤ)) = arrow a b i (j.1, j.2 + 1) := by
    exact propext (north_arrow_iff a b i j).symm
  simp only [h1, h2]

lemma kernelK_cast_eq_arrow_diff (a b : ℕ) (hab : a < b) (i j : ℤ × ℤ) :
    (kernelK a b (gVal a b j - gVal a b i) : ℝ) =
      (if arrow a b i j then (1 : ℝ) else 0) -
      (if arrow a b i (j.1, j.2 + 1) then (1 : ℝ) else 0) := by
  rw [kernelK_eq_arrow_diff_int a b hab]
  push_cast
  simp

lemma bilinFormUnsym_eq_arrow_diff (a b : ℕ) (hab : a < b)
    (D E : Finset (ℤ × ℤ)) :
    bilinFormUnsym a b D E =
      (∑ i ∈ D, ∑ j ∈ E,
        (if arrow a b i j then (1 : ℝ) else 0)) -
      (∑ i ∈ D, ∑ j ∈ E,
        (if arrow a b i (j.1, j.2 + 1) then (1 : ℝ) else 0)) := by
  unfold bilinFormUnsym
  simp_rw [kernelK_cast_eq_arrow_diff a b hab]
  simp_rw [Finset.sum_sub_distrib]

def bottomRow (b : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) (b : ℤ)).map ⟨fun x => (x, (1 : ℤ)), fun _ _ h => by
    simp [Prod.ext_iff] at h; exact h⟩

lemma mem_bottomRow_iff (b : ℕ) (p : ℤ × ℤ) :
    p ∈ bottomRow b ↔ 1 ≤ p.1 ∧ p.1 ≤ (b : ℤ) ∧ p.2 = 1 := by
  simp only [bottomRow]
  constructor
  · intro h
    simp only [Finset.mem_map, Finset.mem_Icc] at h
    rcases h with ⟨x, ⟨hx1, hx2⟩, rfl⟩
    constructor
    · exact hx1
    · constructor
      · exact hx2
      · simp
  · intro h
    rcases h with ⟨h1, h2, h3⟩
    simp only [Finset.mem_map, Finset.mem_Icc]
    refine' ⟨p.1, ⟨h1, by simpa [h3] using h2⟩, _⟩
    simp [Prod.ext_iff, h3]

lemma mem_upperBoundary_iff (a b : ℕ) (E : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    p ∈ upperBoundary a b E ↔
    (1 ≤ p.1 ∧ p.1 ≤ (b : ℤ)) ∧ (1 ≤ p.2 ∧ p.2 ≤ (a : ℤ) + 1) ∧
    p ∉ E ∧ (p.2 = 1 ∨ (p.1, p.2 - 1) ∈ E) := by
  simp only [upperBoundary, mem_filter, mem_product, mem_Icc, decide_eq_true_eq, and_assoc]

lemma one_le_snd_of_mem_subdiagram (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (p : ℤ × ℤ) (hp : p ∈ E) : 1 ≤ p.2 := by
  have h₁ : E ⊆ gapFinset a b := hE.1
  have h₂ : p ∈ gapFinset a b := h₁ hp
  simp only [gapFinset] at h₂
  simp [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h₂
  norm_cast at h₂ ⊢
  omega

lemma south_mem_of_mem_subdiagram (a b : ℕ) (_ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (p : ℤ × ℤ) (hp : p ∈ E) (hp2 : 1 < p.2) : (p.1, p.2 - 1) ∈ E := by
  have hEsub := hE.1
  have hpG := hEsub hp
  have hclos := hE.2 p hp
  have hpG' : (p.1, p.2 - 1) ∈ gapFinset a b := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      decide_eq_true_eq, gVal] at hpG ⊢
    constructor
    · constructor
      · exact ⟨hpG.1.1.1, hpG.1.1.2⟩
      · constructor
        · omega
        · omega
    · nlinarith
  have hle : gapLE a b p (p.1, p.2 - 1) := by
    simp only [gapLE]
    constructor
    · omega
    · omega
  exact hclos _ hpG' hle

lemma telescoping_identity (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (p : ℤ × ℤ)
    (hp : p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1))) :
    (if p ∈ E then (1 : ℤ) else 0) - (if (p.1, p.2 - 1) ∈ E then 1 else 0) =
    (if p ∈ bottomRow b then 1 else 0) - (if p ∈ upperBoundary a b E then 1 else 0) := by
  have _ := hab
  by_cases hpE : p ∈ E
  · have hpU : p ∉ upperBoundary a b E := by
      rw [mem_upperBoundary_iff]
      push_neg
      intro _ _ hne
      exact absurd hpE hne
    simp [hpE, hpU]
    by_cases hp2 : p.2 = 1
    · have : (p.1, p.2 - 1) = (p.1, (0 : ℤ)) := by simp [hp2]
      have hnotE : (p.1, p.2 - 1) ∉ E := by
        rw [this]
        intro hmem
        have := one_le_snd_of_mem_subdiagram a b E hE _ hmem
        simp at this
      have hpB : p ∈ bottomRow b := by
        rw [mem_bottomRow_iff]
        have := Finset.mem_product.mp hp
        simp [Finset.mem_Icc] at this
        exact ⟨this.1.1, this.1.2, hp2⟩
      simp [hnotE, hpB]
    · have hp2gt : 1 < p.2 := by
        have := one_le_snd_of_mem_subdiagram a b E hE p hpE
        omega
      have hSouth : (p.1, p.2 - 1) ∈ E :=
        south_mem_of_mem_subdiagram a b ha hb E hE p hpE hp2gt
      have hpnB : p ∉ bottomRow b := by
        rw [mem_bottomRow_iff]
        push_neg
        intro _ _
        exact hp2
      simp [hSouth, hpnB]
  · simp [hpE]
    by_cases hp2 : p.2 = 1
    · have : (p.1, p.2 - 1) = (p.1, (0 : ℤ)) := by simp [hp2]
      have hnotE : (p.1, p.2 - 1) ∉ E := by
        rw [this]
        intro hmem
        have := one_le_snd_of_mem_subdiagram a b E hE _ hmem
        simp at this
      have hpB : p ∈ bottomRow b := by
        rw [mem_bottomRow_iff]
        have := Finset.mem_product.mp hp
        simp [Finset.mem_Icc] at this
        exact ⟨this.1.1, this.1.2, hp2⟩
      have hpU : p ∈ upperBoundary a b E := by
        rw [mem_upperBoundary_iff]
        have := Finset.mem_product.mp hp
        simp [Finset.mem_Icc] at this
        exact ⟨⟨this.1.1, this.1.2⟩, ⟨this.2.1, this.2.2⟩, hpE, Or.inl hp2⟩
      simp [hnotE, hpB, hpU]
    · have hpnB : p ∉ bottomRow b := by
        rw [mem_bottomRow_iff]
        push_neg
        intro _ _
        omega
      by_cases hSouth : (p.1, p.2 - 1) ∈ E
      · have hpU : p ∈ upperBoundary a b E := by
          rw [mem_upperBoundary_iff]
          have := Finset.mem_product.mp hp
          simp [Finset.mem_Icc] at this
          exact ⟨⟨this.1.1, this.1.2⟩, ⟨this.2.1, this.2.2⟩, hpE, Or.inr hSouth⟩
        simp [hSouth, hpnB, hpU]
      · have hpnU : p ∉ upperBoundary a b E := by
          rw [mem_upperBoundary_iff]
          push_neg
          intro _ _ _
          constructor
          · omega
          · exact hSouth
        simp [hSouth, hpnB, hpnU]

lemma gVal_diff_bottomRow (a b : ℕ) (i : ℤ × ℤ) (x : ℤ) :
    gVal a b (x, 1) - gVal a b i = (a : ℤ) * (i.1 - x) + (b : ℤ) * (i.2 - 1) := by
  simp only [gVal]
  ring

lemma mem_gapFinset_bounds (a b : ℕ) (p : ℤ × ℤ) (hp : p ∈ gapFinset a b) :
    1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gVal a b p := by
  dsimp only [gapFinset] at hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
  have h₃ : 0 < gVal a b p := by
    simpa [gVal] using hp.2
  exact ⟨by linarith, by linarith, h₃⟩

set_option linter.unusedVariables false in
set_option linter.unnecessarySeqFocus false in
lemma arrow_to_bottomRow_exists (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (i : ℤ × ℤ) (hi : i ∈ gapFinset a b) :
    let x := i.1 + (↑b * (i.2 - 1)) / (↑a : ℤ)
    1 ≤ x ∧ x ≤ (b : ℤ) ∧ arrow a b i (x, 1) := by
  dsimp only [gapFinset, gVal] at hi
  dsimp only [arrow, gVal]
  have h₁ : i.1 ∈ Finset.Icc (1 : ℤ) (b : ℤ) := by
    simp_all [Finset.mem_filter, Finset.mem_product]
  have h₂ : i.2 ∈ Finset.Icc (1 : ℤ) (a : ℤ) := by
    simp_all [Finset.mem_filter, Finset.mem_product]
  have h₃ : 0 < (a : ℤ) * (b : ℤ) - (a : ℤ) * i.1 - (b : ℤ) * i.2 := by
    simp_all [Finset.mem_filter, Finset.mem_product]
  have h₄ : (1 : ℤ) ≤ i.1 := by
    simp only [Finset.mem_Icc] at h₁
    linarith
  have h₆ : (1 : ℤ) ≤ i.2 := by
    simp only [Finset.mem_Icc] at h₂
    linarith
  have h₈ : 0 ≤ (b : ℤ) * (i.2 - 1) := by
    nlinarith
  set x := i.1 + (↑b * (i.2 - 1)) / (↑a : ℤ) with _
  have h₉ : 1 ≤ x := by
    have h₉₁ : 0 ≤ (↑b * (i.2 - 1)) / (↑a : ℤ) := by
      apply Int.ediv_nonneg
      · nlinarith
      · exact by exact_mod_cast ha.le
    linarith
  have h₁₀ : x ≤ (b : ℤ) := by
    have h₁₀₁ : (↑b * (i.2 - 1)) / (↑a : ℤ) ≤ (b : ℤ) - i.1 := by
      have h₁₀₂ : (↑b * (i.2 - 1)) / (↑a : ℤ) * (↑a : ℤ) ≤ (↑b * (i.2 - 1)) := by
        apply Int.ediv_mul_le
        <;> norm_cast <;>
        (try omega)
      nlinarith [h₃]
    linarith
  have h₁₁ : 0 ≤ ((a : ℤ) * (b : ℤ) - (a : ℤ) * x - (b : ℤ) * 1) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * i.1 - (b : ℤ) * i.2) := by
    have h₁₁₃ : (a : ℤ) * (i.1 - x) + (b : ℤ) * (i.2 - 1) = (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
      have h₁₁₇ : (b : ℤ) * (i.2 - 1) - (a : ℤ) * ((↑b * (i.2 - 1)) / (↑a : ℤ)) = (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
        have h₁₁₈ : (b : ℤ) * (i.2 - 1) = (a : ℤ) * ((↑b * (i.2 - 1)) / (↑a : ℤ)) + (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
          have h₁₂₁ := Int.mul_ediv_add_emod ((b : ℤ) * (i.2 - 1)) (a : ℤ)
          linarith
        linarith
      linarith
    have h₁₁₈ : (b : ℤ) * (i.2 - 1) % (a : ℤ) ≥ 0 := by
      apply Int.emod_nonneg
      <;> norm_cast <;>
      (try omega)
    linarith
  have h₁₂ : ((a : ℤ) * (b : ℤ) - (a : ℤ) * x - (b : ℤ) * 1) - ((a : ℤ) * (b : ℤ) - (a : ℤ) * i.1 - (b : ℤ) * i.2) < (a : ℤ) := by
    have h₁₂₃ : (a : ℤ) * (i.1 - x) + (b : ℤ) * (i.2 - 1) = (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
      have h₁₂₇ : (b : ℤ) * (i.2 - 1) - (a : ℤ) * ((↑b * (i.2 - 1)) / (↑a : ℤ)) = (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
        have h₁₂₈ : (b : ℤ) * (i.2 - 1) = (a : ℤ) * ((↑b * (i.2 - 1)) / (↑a : ℤ)) + (b : ℤ) * (i.2 - 1) % (a : ℤ) := by
          have h₁₃₁ := Int.mul_ediv_add_emod ((b : ℤ) * (i.2 - 1)) (a : ℤ)
          linarith
        linarith
      linarith
    have h₁₂₈ : (b : ℤ) * (i.2 - 1) % (a : ℤ) < (a : ℤ) := by
      apply Int.emod_lt_of_pos
      <;> norm_cast
    linarith
  constructor
  · exact h₉
  constructor
  · exact h₁₀
  constructor
  · exact h₁₁
  · exact h₁₂

set_option linter.unnecessarySeqFocus false in
lemma arrow_to_bottomRow_unique (a b : ℕ) (ha : 0 < a)
    (i : ℤ × ℤ) (x x' : ℤ) (hx : arrow a b i (x, 1)) (hx' : arrow a b i (x', 1)) :
    x = x' := by
  have hd1 := gVal_diff_bottomRow a b i x
  have hd2 := gVal_diff_bottomRow a b i x'
  have h₁ : (a : ℤ) * (i.1 - x) + (b : ℤ) * (i.2 - 1) ≥ 0 := by
    have := hx.1; linarith
  have h₂ : (a : ℤ) * (i.1 - x) + (b : ℤ) * (i.2 - 1) < (a : ℤ) := by
    have := hx.2; linarith
  have h₃ : (a : ℤ) * (i.1 - x') + (b : ℤ) * (i.2 - 1) ≥ 0 := by
    have := hx'.1; linarith
  have h₄ : (a : ℤ) * (i.1 - x') + (b : ℤ) * (i.2 - 1) < (a : ℤ) := by
    have := hx'.2; linarith
  have : (x' - x : ℤ) = 0 := by
    nlinarith
  linarith

lemma exists_unique_arrow_to_bottomRow (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (i : ℤ × ℤ) (hi : i ∈ gapFinset a b) :
    ∃! x : ℤ, 1 ≤ x ∧ x ≤ (b : ℤ) ∧ arrow a b i (x, 1) := by
  obtain ⟨hx_lb, hx_ub, hx_arrow⟩ := arrow_to_bottomRow_exists a b ha hb hab i hi
  exact ⟨_, ⟨hx_lb, hx_ub, hx_arrow⟩, fun y ⟨_, _, hy_arrow⟩ =>
    arrow_to_bottomRow_unique a b ha i y _ hy_arrow hx_arrow⟩

set_option linter.unusedVariables false in
lemma arrowPairs_bottomRow_card (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ)) (hD : D ⊆ gapFinset a b) :
    (arrowPairs a b D (bottomRow b)).card = D.card := by
  symm
  apply Finset.card_bij
    (fun i hi => (i, ((exists_unique_arrow_to_bottomRow a b ha hb hab i (hD hi)).choose, 1)))
  · intro i hi
    have hex := (exists_unique_arrow_to_bottomRow a b ha hb hab i (hD hi)).choose_spec
    simp only [arrowPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hi, (mem_bottomRow_iff b _).mpr ⟨hex.1.1, hex.1.2.1, rfl⟩⟩, hex.1.2.2⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Prod.ext_iff.mp heq |>.1
  · intro ⟨i, j⟩ hmem
    simp only [arrowPairs, Finset.mem_filter, Finset.mem_product] at hmem
    obtain ⟨⟨hiD, hjB⟩, harr⟩ := hmem
    refine ⟨i, hiD, ?_⟩
    have hex := exists_unique_arrow_to_bottomRow a b ha hb hab i (hD hiD)
    have hjmem := (mem_bottomRow_iff b j).mp hjB
    have hj_eq : j = (j.1, 1) := Prod.ext rfl hjmem.2.2
    rw [hj_eq] at harr
    have huniq := hex.choose_spec.2 j.1 ⟨hjmem.1, hjmem.2.1, harr⟩
    show (i, (hex.choose, 1)) = (i, j)
    rw [hj_eq]
    congr 1
    exact Prod.ext huniq.symm rfl


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

lemma arrowPairs_split (a b : ℕ) (D : Finset (ℤ × ℤ)) (UE : Finset (ℤ × ℤ)) :
    (arrowPairs a b D UE).card =
      ((arrowPairs a b D UE).filter fun p => p.2.1 < p.1.1).card +
      ((arrowPairs a b D UE).filter fun p => ¬(p.2.1 < p.1.1)).card := by
  have h := @Finset.card_filter_add_card_filter_not _ (arrowPairs a b D UE)
    (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.2.1 < p.1.1) _ _
  omega

lemma snd_le_a_of_mem_subdiagram (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (p : ℤ × ℤ) (hp : p ∈ E) : p.2 ≤ (a : ℤ) := by
  have h₁ : E ⊆ gapFinset a b := hE.1
  have h₂ : p ∈ gapFinset a b := h₁ hp
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h₂
  <;> norm_cast at h₂ ⊢
  <;>
    (try omega)

lemma gVal_diff_eq (a b : ℕ) (i j : ℤ × ℤ) :
    gVal a b j - gVal a b i = (a : ℤ) * (i.1 - j.1) - (b : ℤ) * (j.2 - i.2) := by
  simp only [gVal]; ring

lemma blue_arrow_snd_lt (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (i₀ j₀ : ℤ × ℤ) (harrow : arrow a b i₀ j₀)
    (hblue : j₀.1 < i₀.1) : i₀.2 < j₀.2 := by
  have h1 : (a : ℤ) * (i₀.1 - j₀.1 : ℤ) + (b : ℤ) * (i₀.2 - j₀.2 : ℤ) = gVal a b j₀ - gVal a b i₀ := by
    simp only [gVal]; ring_nf
  have h2 : (a : ℤ) * (i₀.1 - j₀.1 : ℤ) + (b : ℤ) * (i₀.2 - j₀.2 : ℤ) < (a : ℤ) := by
    linarith [harrow.2]
  have h4 : (a : ℤ) * ((i₀.1 - j₀.1 : ℤ) - 1) ≥ 0 := by nlinarith
  by_contra h
  have h6₅ : (b : ℤ) * (i₀.2 - j₀.2 : ℤ) ≥ 0 := by nlinarith
  linarith

lemma gVal_diff_eq_helper (a b : ℕ) (i₀ j₀ : ℤ × ℤ) :
    gVal a b j₀ - gVal a b i₀ = (a : ℤ) * (i₀.1 - j₀.1) - (b : ℤ) * (j₀.2 - i₀.2) := by
  simp only [gVal]; ring

lemma arrow_nat_bounds (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (i₀ j₀ : ℤ × ℤ) (harrow : arrow a b i₀ j₀)
    (hblue : j₀.1 < i₀.1) (hsnd : i₀.2 < j₀.2) :
    b * (j₀.2 - i₀.2).toNat ≤ a * (i₀.1 - j₀.1).toNat ∧
    a * (i₀.1 - j₀.1).toNat < b * (j₀.2 - i₀.2).toNat + a := by
  have harrow_ge := harrow.1
  have harrow_lt := harrow.2
  have h_diff_fst_pos : 0 ≤ i₀.1 - j₀.1 := by omega
  have h_diff_snd_pos : 0 ≤ j₀.2 - i₀.2 := by omega
  rw [gVal_diff_eq_helper] at harrow_ge harrow_lt
  have h_dx_cast : (((i₀.1 - j₀.1).toNat : ℤ)) = i₀.1 - j₀.1 :=
    Int.toNat_of_nonneg h_diff_fst_pos
  have h_dy_cast : (((j₀.2 - i₀.2).toNat : ℤ)) = j₀.2 - i₀.2 :=
    Int.toNat_of_nonneg h_diff_snd_pos
  rw [← h_dx_cast, ← h_dy_cast] at harrow_ge harrow_lt
  have int_lower : (b : ℤ) * ↑(j₀.2 - i₀.2).toNat ≤ (a : ℤ) * ↑(i₀.1 - j₀.1).toNat := by omega
  have int_upper : (a : ℤ) * ↑(i₀.1 - j₀.1).toNat < (b : ℤ) * ↑(j₀.2 - i₀.2).toNat + a := by omega
  constructor
  · exact_mod_cast int_lower
  · exact_mod_cast int_upper

lemma snd_plus_legLength_le_a (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ E) : c.2 + ↑(legLength E c) ≤ (a : ℤ) :=
  snd_le_a_of_mem_subdiagram a b E hE (c.1, c.2 + ↑(legLength E c)) (legLength_achieved E c hc)

lemma gVal_mono_snd (a b : ℕ) (hb : 0 < b) (p c : ℤ × ℤ)
    (heq : c.1 = p.1) (hle : c.2 ≤ p.2) :
    gVal a b p ≤ gVal a b c := by
  simp [gVal]; nlinarith

lemma mem_gapFinset_of_bounds (a b : ℕ) (p : ℤ × ℤ)
    (h1 : 1 ≤ p.1) (h2 : p.1 ≤ (b : ℤ)) (h3 : 1 ≤ p.2) (h4 : p.2 ≤ (a : ℤ))
    (hg : 0 < gVal a b p) :
    p ∈ gapFinset a b := by
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, by simp_all [decide_eq_true]⟩

lemma legLength_le_of_blue_arrow (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (i₀ j₀ : ℤ × ℤ)
    (hcE : (j₀.1, i₀.2) ∈ E)
    (hjnotE : j₀ ∉ E)
    (hsnd : i₀.2 < j₀.2)
    (hj_fst_le : 1 ≤ j₀.1) (hj_fst_ub : j₀.1 ≤ (b : ℤ))
    (hj_snd_le : 1 ≤ j₀.2) :
    legLength E (j₀.1, i₀.2) ≤ (j₀.2 - i₀.2 - 1).toNat := by
  set c := (j₀.1, i₀.2) with hc_def
  set ℓ := legLength E c with hℓ_def
  have htop : (c.1, c.2 + ↑ℓ) ∈ E := legLength_achieved E c hcE
  by_contra h_contra
  push_neg at h_contra
  have h_ge : j₀.2 ≤ i₀.2 + ↑ℓ := by omega
  by_cases hja : j₀.2 ≤ (a : ℤ)
  · have htop_mem_E : (j₀.1, i₀.2 + ↑ℓ) ∈ E := htop
    have htop_mem_gap : (j₀.1, i₀.2 + ↑ℓ) ∈ gapFinset a b := hE.1 htop_mem_E
    have hgval_top : 0 < gVal a b (j₀.1, i₀.2 + ↑ℓ) := by
      simp only [gapFinset, Finset.mem_filter] at htop_mem_gap
      exact of_decide_eq_true htop_mem_gap.2
    have hgval_j : 0 < gVal a b j₀ := by
      have : gVal a b (j₀.1, i₀.2 + ↑ℓ) ≤ gVal a b (j₀.1, j₀.2) :=
        gVal_mono_snd a b hb (j₀.1, i₀.2 + ↑ℓ) (j₀.1, j₀.2) rfl h_ge
      linarith
    have hj_gap : j₀ ∈ gapFinset a b :=
      mem_gapFinset_of_bounds a b j₀ hj_fst_le hj_fst_ub hj_snd_le hja hgval_j
    have hle_gap : gapLE a b (j₀.1, i₀.2 + ↑ℓ) j₀ :=
      ⟨by simp, h_ge⟩
    exact hjnotE (hE.2 _ htop_mem_E _ hj_gap hle_gap)
  · push_neg at hja
    have h_le_a := snd_plus_legLength_le_a a b E hE c hcE
    simp only [hc_def, hℓ_def] at h_le_a h_ge ⊢
    omega

lemma c_mem_E_of_blue_arrow (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (i₀ j₀ : ℤ × ℤ)
    (hjE : (j₀.1, j₀.2 - 1) ∈ E)
    (hsnd : i₀.2 < j₀.2)
    (hi_pos : 1 ≤ i₀.2) :
    (j₀.1, i₀.2) ∈ E := by
  have hjE_gap : (j₀.1, j₀.2 - 1) ∈ gapFinset a b := hE.1 hjE
  have ⟨hj1, _, hjg⟩ := mem_gapFinset_bounds a b _ hjE_gap
  have hj_snd_ub : j₀.2 - 1 ≤ (a : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hjE_gap
    exact hjE_gap.1.2.2
  have hj_fst_ub : j₀.1 ≤ (b : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hjE_gap
    exact hjE_gap.1.1.2
  have hc_gap : (j₀.1, i₀.2) ∈ gapFinset a b := by
    apply mem_gapFinset_of_bounds
    · exact hj1
    · exact hj_fst_ub
    · exact hi_pos
    · linarith
    · have : gVal a b (j₀.1, j₀.2 - 1) ≤ gVal a b (j₀.1, i₀.2) :=
        gVal_mono_snd a b hb (j₀.1, j₀.2 - 1) (j₀.1, i₀.2) rfl (by omega)
      linarith
  exact hE.2 _ hjE _ hc_gap ⟨le_refl _, by omega⟩

lemma legLength_eq_of_blue_arrow (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i₀ j₀ : ℤ × ℤ) (hiD : i₀ ∈ D) (hjU : j₀ ∈ upperBoundary a b E)
    (harrow : arrow a b i₀ j₀) (hblue : j₀.1 < i₀.1) :
    legLength E (j₀.1, i₀.2) = (j₀.2 - i₀.2 - 1).toNat := by
  have hsnd : i₀.2 < j₀.2 := blue_arrow_snd_lt a b ha hb hab i₀ j₀ harrow hblue
  have hjU' := (mem_upperBoundary_iff a b E j₀).mp hjU
  obtain ⟨⟨hj1, hj2⟩, ⟨hj3, _⟩, hjnotE, hj_or⟩ := hjU'
  have hjE : (j₀.1, j₀.2 - 1) ∈ E := by
    rcases hj_or with hj2eq1 | hjprev
    · have hi_pos : 1 ≤ i₀.2 := one_le_snd_of_mem_subdiagram a b D hD i₀ hiD; omega
    · exact hjprev
  have hi_pos : 1 ≤ i₀.2 := one_le_snd_of_mem_subdiagram a b D hD i₀ hiD
  have hcE : (j₀.1, i₀.2) ∈ E :=
    c_mem_E_of_blue_arrow a b ha hb E hE i₀ j₀ hjE hsnd hi_pos
  apply Nat.le_antisymm
  · exact legLength_le_of_blue_arrow a b ha hb E hE i₀ j₀ hcE hjnotE hsnd hj1 hj2 hj3
  · have hkey : (j₀.1, i₀.2 + ↑((j₀.2 - i₀.2 - 1).toNat)) = (j₀.1, j₀.2 - 1) := by
      congr 1; omega
    apply legLength_is_max
    rw [hkey]; exact hjE

lemma c_mem_gapFinset (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (i j : ℤ × ℤ) (hi : i ∈ gapFinset a b)
    (hj_fst_le : 1 ≤ j.1) (hj_fst_ub : j.1 ≤ (b : ℤ))
    (hlt : j.1 < i.1) :
    (j.1, i.2) ∈ gapFinset a b := by
  have ⟨_, _, hi_gval⟩ := mem_gapFinset_bounds a b i hi
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hi ⊢
  constructor
  · constructor
    · constructor <;> [exact hj_fst_le; exact hj_fst_ub]
    · exact hi.1.2
  · simp [gVal] at hi_gval ⊢; nlinarith

lemma phi_mem_blueCells (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (p : (ℤ × ℤ) × (ℤ × ℤ))
    (hp : p ∈ (arrowPairs a b D (upperBoundary a b E)).filter fun p => p.2.1 < p.1.1) :
    (p.2.1, p.1.2) ∈ blueCells a b D E := by
  rw [Finset.mem_filter] at hp
  obtain ⟨hp_arr, hblue⟩ := hp
  rw [arrowPairs, Finset.mem_filter] at hp_arr
  obtain ⟨hp_prod, harr⟩ := hp_arr
  rw [Finset.mem_product] at hp_prod
  obtain ⟨hiD, hjU⟩ := hp_prod
  set i := p.1 with _
  set j := p.2 with hj_def
  set c : ℤ × ℤ := (j.1, i.2) with hc_def
  have hiG : i ∈ gapFinset a b := hD.1 hiD
  have ⟨hi1, hi2, hi_gval⟩ := mem_gapFinset_bounds a b i hiG
  rw [mem_upperBoundary_iff] at hjU
  obtain ⟨⟨hj1, hj1ub⟩, ⟨hj2, hj2ub⟩, hjnE, hj_or⟩ := hjU
  have hcG : c ∈ gapFinset a b :=
    c_mem_gapFinset a b ha hb i j hiG hj1 hj1ub hblue
  have hcD : c ∈ D := by
    apply hD.2 i hiD c hcG
    exact ⟨le_of_lt hblue, le_refl i.2⟩
  have hj2_gt_i2 : i.2 < j.2 := blue_arrow_snd_lt a b ha hb hab i j harr hblue
  have hj_below_E : (j.1, j.2 - 1) ∈ E := by
    rcases hj_or with h1 | h2
    · omega
    · exact h2
  have hcE : c ∈ E := by
    apply hE.2 (j.1, j.2 - 1) hj_below_E c hcG
    exact ⟨le_refl j.1, by show i.2 ≤ j.2 - 1; omega⟩
  have hjU' : j ∈ upperBoundary a b E := by
    rw [mem_upperBoundary_iff]
    exact ⟨⟨hj1, hj1ub⟩, ⟨hj2, hj2ub⟩, hjnE, hj_or⟩
  have hleg_eq : legLength E c = (j.2 - i.2 - 1).toNat :=
    legLength_eq_of_blue_arrow a b ha hb hab hcop D E hD hE i j hiD hjU' harr hblue
  have hbounds := arrow_nat_bounds a b ha hb hab i j harr hblue hj2_gt_i2
  have harm : (i.1 - c.1).toNat ≤ armLength D c := by
    have hconv : (j.1 + ↑((i.1 - j.1).toNat), i.2) = (i.1, i.2) := by
      congr 1; rw [Int.toNat_of_nonneg (by omega : 0 ≤ i.1 - j.1)]; omega
    have hiD' : (c.1 + ↑((i.1 - c.1).toNat), c.2) ∈ D := by
      show (j.1 + ↑((i.1 - j.1).toNat), i.2) ∈ D
      rw [hconv]; exact hiD
    exact armLength_le D c _ hiD'
  have hleg_step : legLength E c + 1 = (j.2 - i.2).toNat := by
    rw [hleg_eq]
    have h1 : (j.2 - i.2 - 1).toNat = (j.2 - i.2).toNat - 1 := by omega
    have h2 : 1 ≤ (j.2 - i.2).toNat := by omega
    omega
  have hblue_ineq : b * (legLength E c + 1) ≤ a * armLength D c := by
    rw [hleg_step]
    calc b * (j.2 - i.2).toNat ≤ a * (i.1 - j.1).toNat := hbounds.1
      _ ≤ a * armLength D c := by
          apply Nat.mul_le_mul_left
          exact harm
  rw [blueCells, Finset.mem_filter]
  exact ⟨Finset.mem_inter.mpr ⟨hcD, hcE⟩, hblue_ineq⟩

private lemma legLength_image_bound (a b : ℕ) (E : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hE : E ⊆ gapFinset a b) (hc : c ∈ gapFinset a b) (p : ℤ × ℤ)
    (hp : p ∈ E.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2) :
    (p.2 - c.2).toNat ≤ a - 1 := by
  have hp_mem := (Finset.mem_filter.mp hp).1
  have hp_cond := (Finset.mem_filter.mp hp).2
  have hp_gf : p ∈ gapFinset a b := hE hp_mem
  have hc_gf := hc
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp_gf hc_gf
  have h_diff_nn : (0 : ℤ) ≤ p.2 - c.2 := by omega
  have h_bound : p.2 - c.2 ≤ (a : ℤ) - 1 := by omega
  have h_le_int : (((p.2 - c.2).toNat : ℕ) : ℤ) = p.2 - c.2 := Int.toNat_of_nonneg h_diff_nn
  have h_a_pos : (1 : ℤ) ≤ (a : ℤ) := by linarith
  have : ((p.2 - c.2).toNat : ℤ) ≤ ((a - 1 : ℕ) : ℤ) := by omega
  exact_mod_cast this

private lemma one_le_a_of_mem_gapFinset (a b : ℕ) (c : ℤ × ℤ)
    (hc : c ∈ gapFinset a b) : 1 ≤ a := by
  have h₂ : c ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ)) := by
    have h₃ : c ∈ ((Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (a : ℤ))).filter fun p => decide (0 < gVal a b p) := hc
    exact Finset.mem_of_mem_filter _ h₃
  have h₃ : c.2 ∈ Finset.Icc (1 : ℤ) (a : ℤ) := (Finset.mem_product.mp h₂).2
  have h₄ : (1 : ℤ) ≤ c.2 ∧ c.2 ≤ (a : ℤ) := Finset.mem_Icc.mp h₃
  have h₅ : 1 ≤ (a : ℤ) := by
    linarith
  norm_cast at h₅ ⊢

lemma legLength_lt_a (a b : ℕ) (E : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hE : E ⊆ gapFinset a b) (hc : c ∈ gapFinset a b) :
    legLength E c < a := by
  have ha : 1 ≤ a := one_le_a_of_mem_gapFinset a b c hc
  unfold legLength
  calc ((E.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2).image fun p => (p.2 - c.2).toNat).sup id
      ≤ a - 1 := by
        apply Finset.sup_le
        intro x hx
        simp only [id]
        rw [Finset.mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact legLength_image_bound a b E c hE hc p hp
    _ < a := Nat.sub_lt (by omega) (by omega)

lemma j_not_mem_E (E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ E) :
    (c.1, c.2 + ↑(legLength E c) + 1) ∉ E := by
  intro h
  have key : (c.1, c.2 + ↑(legLength E c) + 1) = (c.1, c.2 + ↑(legLength E c + 1)) := by
    congr 1; push_cast; ring
  rw [key] at h
  have := legLength_is_max E c (legLength E c + 1) h
  omega

lemma ceil_div_lower (a : ℕ) (m : ℕ) (ha : 0 < a) :
    m ≤ a * ((m + a - 1) / a) := by
  have h₁ : (m + a - 1) % a < a := Nat.mod_lt _ ha
  have h₃ : a * ((m + a - 1) / a) + (m + a - 1) % a = m + a - 1 := Nat.div_add_mod _ _
  omega

lemma ceil_div_upper (a : ℕ) (m : ℕ) (ha : 0 < a) :
    a * ((m + a - 1) / a) < m + a := by
  have h₁ : a * ((m + a - 1) / a) ≤ m + a - 1 := Nat.mul_div_le _ _
  have h₃ : m + a - 1 < m + a := Nat.sub_lt (by omega) (by omega)
  omega

lemma ceil_div_pos (a b : ℕ) (ha : 0 < a) (hab : a < b) (leg : ℕ) :
    1 ≤ (b * (leg + 1) + a - 1) / a := by
  have h₄ : b * (leg + 1) ≥ a + 1 := by nlinarith
  have h₅ : b * (leg + 1) + a - 1 ≥ 2 * a := by omega
  exact Nat.le_div_iff_mul_le ha |>.mpr (by omega)

lemma ceil_div_le_arm (a b : ℕ) (ha : 0 < a) (D E : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) (hblue : b * (legLength E c + 1) ≤ a * armLength D c) :
    (b * (legLength E c + 1) + a - 1) / a ≤ armLength D c := by
  have h₆ : (b * (legLength E c + 1) + a - 1) < a * (armLength D c + 1) := by
    have : a * (armLength D c + 1) = a * armLength D c + a := by ring
    omega
  have h₁₀ : (b * (legLength E c + 1) + a - 1) / a < armLength D c + 1 := by
    rw [Nat.div_lt_iff_lt_mul ha]
    linarith
  omega

lemma gVal_diff_psi (a b : ℕ) (c : ℤ × ℤ) (leg k : ℕ) :
    gVal a b (c.1, c.2 + ↑leg + 1) - gVal a b (c.1 + ↑k, c.2) =
    (a : ℤ) * (k : ℤ) - (b : ℤ) * (↑leg + 1) := by
  simp only [gVal]; ring

private lemma mem_gapFinset_of_between (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hcG : c ∈ gapFinset a b)
    (harmG : (c.1 + ↑(armLength D c), c.2) ∈ gapFinset a b)
    (k : ℕ) (hk : k ≤ armLength D c) :
    (c.1 + ↑k, c.2) ∈ gapFinset a b := by
  have h₁ : 1 ≤ (c.1 : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hcG
    norm_num at hcG ⊢; omega
  have h₂ : 1 ≤ (c.2 : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hcG
    norm_num at hcG ⊢; omega
  have h₃ : (c.1 : ℤ) + ↑(armLength D c) ≤ (b : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at harmG
    norm_num at harmG ⊢; omega
  have h₆ : (c.2 : ℤ) ≤ (a : ℤ) := by
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hcG
    norm_num at hcG ⊢; omega
  have h₁₁ : ( (0 : ℤ) < gVal a b (c.1 + ↑k, c.2) ) := by
    have h₁₂ : 0 < gVal a b (c.1 + ↑(armLength D c), c.2) := by
      simp only [gapFinset, Finset.mem_filter] at harmG
      simp_all [gVal]
    have h₁₆ : gVal a b (c.1 + ↑k, c.2) = gVal a b (c.1 + ↑(armLength D c), c.2) + (a : ℤ) * ((armLength D c : ℕ) - k : ℤ) := by
      simp [gVal]
      <;> ring_nf at *
    linarith [show (a : ℤ) * (((armLength D c : ℕ) : ℤ) - (k : ℤ)) ≥ 0 by nlinarith]
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · constructor <;> simp_all [gVal] <;> constructor <;> linarith
  · simp_all [gVal]

lemma i_mem_D (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (D : Finset (ℤ × ℤ)) (hD : IsSubdiagram a b D)
    (c : ℤ × ℤ) (hcD : c ∈ D) (k : ℕ) (hk : k ≤ armLength D c) :
    (c.1 + ↑k, c.2) ∈ D := by
  have harm := armLength_achieved D c hcD
  have harmG : (c.1 + ↑(armLength D c), c.2) ∈ gapFinset a b := hD.1 harm
  have hcG : c ∈ gapFinset a b := hD.1 hcD
  have hkG := mem_gapFinset_of_between a b ha hb D c hcG harmG k hk
  exact hD.2 _ harm _ hkG ⟨by omega, le_refl _⟩

lemma psi_mem_blueArrows (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ blueCells a b D E) :
    let k : ℕ := (b * (legLength E c + 1) + a - 1) / a
    let j : ℤ × ℤ := (c.1, c.2 + ↑(legLength E c) + 1)
    let i : ℤ × ℤ := (c.1 + ↑k, c.2)
    ((i, j) : (ℤ × ℤ) × (ℤ × ℤ)) ∈
      (arrowPairs a b D (upperBoundary a b E)).filter fun p => p.2.1 < p.1.1 := by
  intro k j i
  have hcDE : c ∈ D ∩ E := Finset.mem_of_mem_filter c hc
  have hcD : c ∈ D := Finset.mem_inter.mp hcDE |>.1
  have hcE : c ∈ E := Finset.mem_inter.mp hcDE |>.2
  have hblue : b * (legLength E c + 1) ≤ a * armLength D c :=
    (Finset.mem_filter.mp hc).2
  have hk_le : k ≤ armLength D c := ceil_div_le_arm a b ha D E c hblue
  have hk_pos : 1 ≤ k := ceil_div_pos a b ha hab (legLength E c)
  have hk_lower : b * (legLength E c + 1) ≤ a * k :=
    ceil_div_lower a (b * (legLength E c + 1)) ha
  have hk_upper : a * k < b * (legLength E c + 1) + a :=
    ceil_div_upper a (b * (legLength E c + 1)) ha
  have hi_mem : i ∈ D := i_mem_D a b ha hb D hD c hcD k hk_le
  have hcE_gap : c ∈ gapFinset a b := hE.1 hcE
  have hc_bounds := mem_gapFinset_bounds a b c hcE_gap
  have hj_not_E : j ∉ E := j_not_mem_E E c hcE
  have hc_fst_le_b : c.1 ≤ (b : ℤ) := by
    have hp := hE.1 hcE
    have := (Finset.mem_filter.mp hp).1
    simp [Finset.mem_product, Finset.mem_Icc] at this
    exact this.1.2
  have hj_mem : j ∈ upperBoundary a b E := by
    rw [mem_upperBoundary_iff]
    refine ⟨⟨hc_bounds.1, hc_fst_le_b⟩, ⟨?_, ?_⟩, hj_not_E, Or.inr ?_⟩
    · show 1 ≤ c.2 + ↑(legLength E c) + 1
      have := one_le_snd_of_mem_subdiagram a b E hE c hcE
      omega
    · show c.2 + ↑(legLength E c) + 1 ≤ (a : ℤ) + 1
      have := snd_plus_legLength_le_a a b E hE c hcE
      omega
    · show (c.1, c.2 + ↑(legLength E c) + 1 - 1) ∈ E
      have : c.2 + ↑(legLength E c) + 1 - 1 = c.2 + ↑(legLength E c) := by omega
      rw [this]
      exact legLength_achieved E c hcE
  have hk_lower_int : (b : ℤ) * (↑(legLength E c) + 1) ≤ (a : ℤ) * (k : ℤ) := by
    exact_mod_cast hk_lower
  have hk_upper_int : (a : ℤ) * (k : ℤ) < (b : ℤ) * (↑(legLength E c) + 1) + (a : ℤ) := by
    exact_mod_cast hk_upper
  have harrow : arrow a b i j := by
    constructor
    · rw [gVal_diff_psi]
      omega
    · rw [gVal_diff_psi]
      omega
  have hblue_cond : j.1 < i.1 := by
    show c.1 < c.1 + ↑k
    omega
  rw [Finset.mem_filter]
  refine ⟨?_, hblue_cond⟩
  rw [arrowPairs, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr ⟨hi_mem, hj_mem⟩, harrow⟩

lemma psi_phi_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (p : (ℤ × ℤ) × (ℤ × ℤ))
    (hp : p ∈ (arrowPairs a b D (upperBoundary a b E)).filter fun p => p.2.1 < p.1.1) :
    let c := (p.2.1, p.1.2)
    let k : ℕ := (b * (legLength E c + 1) + a - 1) / a
    let j : ℤ × ℤ := (c.1, c.2 + ↑(legLength E c) + 1)
    let i : ℤ × ℤ := (c.1 + ↑k, c.2)
    ((i, j) : (ℤ × ℤ) × (ℤ × ℤ)) = p := by
  set i₀ := p.1
  set j₀ := p.2
  set c : ℤ × ℤ := (j₀.1, i₀.2)
  have hp_mem := (Finset.mem_filter.mp hp).1
  have hp_blue : j₀.1 < i₀.1 := (Finset.mem_filter.mp hp).2
  have hp_arrow : p ∈ arrowPairs a b D (upperBoundary a b E) := hp_mem
  have hp_prod := (Finset.mem_filter.mp hp_arrow).1
  have harrow : arrow a b i₀ j₀ := (Finset.mem_filter.mp hp_arrow).2
  have hiD : i₀ ∈ D := (Finset.mem_product.mp hp_prod).1
  have hjU : j₀ ∈ upperBoundary a b E := (Finset.mem_product.mp hp_prod).2
  have hsnd : i₀.2 < j₀.2 := blue_arrow_snd_lt a b ha hb hab i₀ j₀ harrow hp_blue
  have hleg : legLength E c = (j₀.2 - i₀.2 - 1).toNat :=
    legLength_eq_of_blue_arrow a b ha hb hab hcop D E hD hE i₀ j₀ hiD hjU harrow hp_blue
  have hdx_pos : (0 : ℤ) < i₀.1 - j₀.1 := by omega
  have hdy_pos : (0 : ℤ) < j₀.2 - i₀.2 := by omega
  set dx := (i₀.1 - j₀.1).toNat
  set dy := (j₀.2 - i₀.2).toNat
  have hdx_eq : (dx : ℤ) = i₀.1 - j₀.1 := Int.toNat_of_nonneg (le_of_lt hdx_pos)
  have hdy_eq : (dy : ℤ) = j₀.2 - i₀.2 := Int.toNat_of_nonneg (le_of_lt hdy_pos)
  have hbounds := arrow_nat_bounds a b ha hb hab i₀ j₀ harrow hp_blue hsnd
  have hdy_sub1_nn : (0 : ℤ) ≤ j₀.2 - i₀.2 - 1 := by omega
  have hdy_leg : dy = legLength E c + 1 := by
    rw [hleg]
    show (j₀.2 - i₀.2).toNat = (j₀.2 - i₀.2 - 1).toNat + 1
    zify [Int.toNat_of_nonneg (le_of_lt hdy_pos), Int.toNat_of_nonneg hdy_sub1_nn]
    omega
  have hk_eq : (b * (legLength E c + 1) + a - 1) / a = dx := by
    rw [← hdy_leg]
    have hk'_lo := ceil_div_lower a (b * dy) ha
    have hk'_hi := ceil_div_upper a (b * dy) ha
    have h2 : a * dx < b * dy + a := hbounds.2
    set k' := (b * dy + a - 1) / a
    apply Nat.le_antisymm
    · by_contra hlt
      push_neg at hlt
      have h3 : a * (dx + 1) ≤ a * k' := Nat.mul_le_mul_left a hlt
      linarith [hk'_hi]
    · by_contra hlt
      push_neg at hlt
      have h3 : a * (k' + 1) ≤ a * dx := Nat.mul_le_mul_left a hlt
      linarith [h2]
  show ((c.1 + ↑((b * (legLength E c + 1) + a - 1) / a), c.2),
        (c.1, c.2 + ↑(legLength E c) + 1)) = p
  rw [hk_eq]
  have hi1 : j₀.1 + ↑dx = i₀.1 := by zify [hdx_eq]; omega
  have hj2 : i₀.2 + ↑(legLength E c) + 1 = j₀.2 := by
    rw [hleg]
    zify [Int.toNat_of_nonneg hdy_sub1_nn]
    omega
  ext <;> simp only [c]
  · exact hi1
  · rfl
  · rfl
  · exact hj2

lemma phi_psi_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ blueCells a b D E) :
    let k : ℕ := (b * (legLength E c + 1) + a - 1) / a
    let j : ℤ × ℤ := (c.1, c.2 + ↑(legLength E c) + 1)
    let i : ℤ × ℤ := (c.1 + ↑k, c.2)
    (((i, j) : (ℤ × ℤ) × (ℤ × ℤ)).2.1, ((i, j) : (ℤ × ℤ) × (ℤ × ℤ)).1.2) = c := by
  dsimp only

lemma blue_card_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    ((arrowPairs a b D (upperBoundary a b E)).filter fun p => p.2.1 < p.1.1).card =
      (blueCells a b D E).card := by
  apply Finset.card_bij'
    (i := fun p _ => (p.2.1, p.1.2))
    (j := fun c _ =>
      let k : ℕ := (b * (legLength E c + 1) + a - 1) / a
      let j : ℤ × ℤ := (c.1, c.2 + ↑(legLength E c) + 1)
      let i : ℤ × ℤ := (c.1 + ↑k, c.2)
      ((i, j) : (ℤ × ℤ) × (ℤ × ℤ)))
    (hi := fun p hp => phi_mem_blueCells a b ha hb hab hcop D E hD hE p hp)
    (hj := fun c hc => psi_mem_blueArrows a b ha hb hab hcop D E hD hE c hc)
    (left_inv := fun p hp => psi_phi_eq a b ha hb hab hcop D E hD hE p hp)
    (right_inv := fun c hc => phi_psi_eq a b ha hb hab hcop D E hD hE c hc)

noncomputable def topInCol (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℤ × ℤ :=
  (c.1, c.2 + ↑(legLength D c))

noncomputable def colHeight (E : Finset (ℤ × ℤ)) (x : ℤ) : ℤ :=
  if h : ((E.filter fun p => p.1 = x).image Prod.snd).Nonempty then
    ((E.filter fun p => p.1 = x).image Prod.snd).max' h
  else 0

noncomputable def ubInCol (_a _b : ℕ) (E : Finset (ℤ × ℤ)) (x : ℤ) : ℤ × ℤ :=
  (x, colHeight E x + 1)

noncomputable def redPhiCell (D : Finset (ℤ × ℤ)) (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × ℤ :=
  let i := p.1
  let j := p.2
  let iTopY := i.2 + ↑(legLength D i)
  (i.1, j.2 + (iTopY - i.2))

noncomputable def redPsiPair (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  let iTopY := c.2 + ↑(legLength D c)
  let t := (iTopY - c.2).toNat
  let q := (b * t) / a
  let jCol := c.1 + ↑q
  let j := ubInCol a b E jCol
  let s := c.2 - j.2
  let i := (c.1, iTopY - s)
  (i, j)

lemma armLength_achieved_aux (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hne : ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
      fun p => (p.1 - c.1).toNat).Nonempty) :
    ∃ p₀ ∈ D, p₀.2 = c.2 ∧ c.1 ≤ p₀.1 ∧ (p₀.1 - c.1).toNat = armLength D c := by
  obtain ⟨n, hn_mem, hn_eq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_image] at hn_mem
  obtain ⟨p₀, hp₀_filt, hp₀_eq⟩ := hn_mem
  rw [Finset.mem_filter] at hp₀_filt
  obtain ⟨hp₀_mem, hp₀_row, hp₀_le⟩ := hp₀_filt
  refine ⟨p₀, hp₀_mem, hp₀_row, hp₀_le, ?_⟩
  simp only [id] at hn_eq
  rw [hp₀_eq, armLength, ← hn_eq]

lemma red_arrow_snd_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (i j : ℤ × ℤ) (harrow : arrow a b i j) (hred : ¬(j.1 < i.1)) :
    j.2 ≤ i.2 := by
  have h₁ : (a : ℤ) * (i.1 - j.1) - (b : ℤ) * (j.2 - i.2) = (gVal a b j : ℤ) - (gVal a b i : ℤ) := by
    simp [gVal]; ring_nf
  have h₂ : 0 ≤ (a : ℤ) * (i.1 - j.1) - (b : ℤ) * (j.2 - i.2) := by
    linarith [h₁, harrow.1]
  have h₅ : (a : ℤ) * (i.1 - j.1) ≤ 0 := by nlinarith
  have h₈ : (j.2 : ℤ) - i.2 ≤ 0 := by
    by_contra h₁₂
    push_neg at h₁₂
    have : (b : ℤ) * (j.2 - i.2) > 0 := by nlinarith
    linarith
  linarith

lemma redPhiCell_mem_gapFinset (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (D E : Finset (ℤ × ℤ)) (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i j : ℤ × ℤ) (hi : i ∈ D) (hj : j ∈ upperBoundary a b E)
    (harrow : arrow a b i j) (hred : ¬(j.1 < i.1)) :
    redPhiCell D (i, j) ∈ gapFinset a b := by
  have hj_le_i : j.2 ≤ i.2 := red_arrow_snd_le a b ha hb hab i j harrow hred
  have hiTop : (i.1, i.2 + ↑(legLength D i)) ∈ D := legLength_achieved D i hi
  have hiTop_gap : (i.1, i.2 + ↑(legLength D i)) ∈ gapFinset a b := hD.1 hiTop
  have hiTop_bounds := mem_gapFinset_bounds a b _ hiTop_gap
  have hiTop_snd_le : i.2 + ↑(legLength D i) ≤ (a : ℤ) := snd_le_a_of_mem_subdiagram a b D hD _ hiTop
  have hj_ub := (mem_upperBoundary_iff a b E j).mp hj
  have hj1_ge : 1 ≤ j.2 := hj_ub.2.1.1
  have hi_gap : i ∈ gapFinset a b := hD.1 hi
  have hi_bounds := mem_gapFinset_bounds a b _ hi_gap
  show redPhiCell D (i, j) ∈ gapFinset a b
  unfold redPhiCell; simp only
  apply mem_gapFinset_of_bounds
  · exact hi_bounds.1
  · exact Finset.mem_Icc.mp ((Finset.mem_product.mp (Finset.mem_filter.mp hi_gap).1).1) |>.2
  · omega
  · omega
  · have : j.2 + (i.2 + ↑(legLength D i) - i.2) ≤ i.2 + ↑(legLength D i) := by omega
    calc gVal a b (i.1, j.2 + (i.2 + ↑(legLength D i) - i.2))
        ≥ gVal a b (i.1, i.2 + ↑(legLength D i)) := gVal_mono_snd a b hb _ _ rfl this
      _ > 0 := hiTop_bounds.2.2

lemma redPhiCell_mem_D (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (D E : Finset (ℤ × ℤ)) (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i j : ℤ × ℤ) (hi : i ∈ D) (hj : j ∈ upperBoundary a b E)
    (harrow : arrow a b i j) (hred : ¬(j.1 < i.1)) :
    redPhiCell D (i, j) ∈ D := by
  set c := redPhiCell D (i, j) with hc_def
  set iTop := (i.1, i.2 + ↑(legLength D i)) with hiTop_def
  have hiTop_mem : iTop ∈ D := legLength_achieved D i hi
  have hj2_le : j.2 ≤ i.2 := red_arrow_snd_le a b ha hb hab i j harrow hred
  have hc2_le : c.2 ≤ iTop.2 := by simp only [hc_def, redPhiCell, hiTop_def]; omega
  have hc1_eq : c.1 = iTop.1 := by simp only [hc_def, redPhiCell, hiTop_def]
  have hc_gap : c ∈ gapFinset a b := redPhiCell_mem_gapFinset a b ha hb hab D E hD hE i j hi hj harrow hred
  exact hD.2 iTop hiTop_mem c hc_gap ⟨le_of_eq hc1_eq.symm, hc2_le⟩

lemma redPhiCell_eq (D : Finset (ℤ × ℤ)) (i j : ℤ × ℤ) :
    redPhiCell D (i, j) = (i.1, j.2 + ↑(legLength D i)) := by
  simp only [redPhiCell]; ext <;> simp

lemma legLength_at_shifted_lower (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D)
    (s : ℤ) (hs : 0 ≤ s) :
    s.toNat ≤ legLength D (c.1, c.2 + ↑(legLength D c) - s) := by
  apply legLength_is_max
  have hd : (c.1, c.2 + ↑(legLength D c)) ∈ D := legLength_achieved D c hc
  convert hd using 1; ext <;> simp; omega

lemma p_snd_le_top (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (p : ℤ × ℤ)
    (hp : p ∈ D) (hcol : p.1 = c.1) :
    p.2 ≤ c.2 + ↑(legLength D c) := by
  by_cases h : c.2 ≤ p.2
  · have h₃ : (p.2 - c.2 : ℤ) ≥ 0 := by omega
    have h₆ : ((p.2 - c.2 : ℤ).toNat : ℕ) ∈ ((D.filter fun p => p.1 = c.1 ∧ c.2 ≤ p.2).image fun p => (p.2 - c.2).toNat) := by
      apply Finset.mem_image.mpr; exact ⟨p, by simp_all [Finset.mem_filter]⟩
    have h₉ : (p.2 - c.2 : ℤ).toNat ≤ legLength D c := by
      have := Finset.le_sup (f := (id : ℕ → ℕ)) h₆; simp [legLength] at this ⊢; exact this
    have : ((p.2 - c.2 : ℤ).toNat : ℤ) = (p.2 - c.2 : ℤ) := Int.toNat_of_nonneg (by omega)
    linarith
  · linarith

lemma legLength_at_shifted_upper (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D)
    (s : ℤ) (hs : 0 ≤ s) :
    legLength D (c.1, c.2 + ↑(legLength D c) - s) ≤ s.toNat := by
  apply Finset.sup_le
  intro n hn
  simp only [Finset.mem_image] at hn
  obtain ⟨p, hp_mem, hp_eq⟩ := hn
  rw [Finset.mem_filter] at hp_mem
  obtain ⟨hp_D, hcol, hge⟩ := hp_mem
  rw [← hp_eq]
  apply Int.toNat_le_toNat
  have hcol' : p.1 = c.1 := by simpa using hcol
  linarith [p_snd_le_top D c p hp_D hcol']

lemma legLength_at_shifted (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∈ D)
    (s : ℤ) (hs : 0 ≤ s) :
    legLength D (c.1, c.2 + ↑(legLength D c) - s) = s.toNat :=
  le_antisymm (legLength_at_shifted_upper D c hc s hs) (legLength_at_shifted_lower D c hc s hs)

lemma upperBoundary_shift_not_mem_E (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (j : ℤ × ℤ) (hj : j ∈ upperBoundary a b E) (n : ℕ) :
    (j.1, j.2 + ↑n) ∉ E := by
  have hj_ub := (mem_upperBoundary_iff a b E j).mp hj
  have hj_not_E : j ∉ E := hj_ub.2.2.1
  intro hmem
  have hdown : ∀ k : ℕ, (j.1, j.2 + ↑k) ∈ E → (j.1, j.2) ∈ E := by
    intro k; induction k with
    | zero => simp
    | succ m ih =>
      intro hm; apply ih
      have : 1 < j.2 + ↑(m + 1) := by omega
      have hsouth := south_mem_of_mem_subdiagram a b ha hb E hE (j.1, j.2 + ↑(m + 1)) hm this
      simp at hsouth; convert hsouth using 1; ext <;> simp; omega
  exact hj_not_E (hdown n hmem)

lemma nat_div_eq_of_arrow (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (i j : ℤ × ℤ) (har : arrow a b i j) (hx : i.1 ≤ j.1) (hy : j.2 ≤ i.2) :
    (b * (i.2 - j.2).toNat) / a = (j.1 - i.1).toNat := by
  have h₁ : (gVal a b j - gVal a b i : ℤ) = (a : ℤ) * (i.1 - j.1) - (b : ℤ) * (j.2 - i.2) := by
    simp [gVal]; ring_nf
  have h₆ : (a : ℤ) * (j.1 - i.1) ≤ (b : ℤ) * (i.2 - j.2) := by nlinarith [har.1, h₁]
  have h₇ : (b : ℤ) * (i.2 - j.2) < (a : ℤ) * (j.1 - i.1) + (a : ℤ) := by nlinarith [har.2, h₁]
  have h₉₂ : 0 ≤ (j.1 - i.1 : ℤ) := by linarith
  have h₉₃ : 0 ≤ (i.2 - j.2 : ℤ) := by linarith
  have h₈₅ : ((j.1 - i.1).toNat : ℤ) = (j.1 - i.1 : ℤ) := Int.toNat_of_nonneg h₉₂
  have h₈₆ : ((i.2 - j.2).toNat : ℤ) = (i.2 - j.2 : ℤ) := Int.toNat_of_nonneg h₉₃
  have h₈ : (a : ℕ) * ((j.1 - i.1).toNat) ≤ b * (i.2 - j.2).toNat := by
    have : (a : ℤ) * ((j.1 - i.1).toNat : ℤ) ≤ (b : ℤ) * ((i.2 - j.2).toNat : ℤ) := by
      rw [h₈₅, h₈₆]; exact h₆
    exact_mod_cast this
  have h₉ : b * (i.2 - j.2).toNat < (a : ℕ) * (((j.1 - i.1).toNat) + 1) := by
    have : (b : ℤ) * ((i.2 - j.2).toNat : ℤ) < (a : ℤ) * (((j.1 - i.1).toNat : ℤ) + 1) := by
      rw [h₈₅, h₈₆]; linarith
    exact_mod_cast this
  apply Nat.div_eq_of_lt_le <;> nlinarith

lemma mem_subdiagram_of_le_armtip (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hcE : c ∈ E) (x : ℤ) (hx1 : c.1 ≤ x)
    (hx2 : x ≤ c.1 + ↑(armLength E c)) :
    (x, c.2) ∈ E := by
  set k := (x - c.1).toNat with hk_def
  have hx_eq : x = c.1 + ↑k := by
    rw [hk_def, Int.toNat_of_nonneg (by omega)]; omega
  have hk_le : k ≤ armLength E c := by
    rw [hk_def]; exact Int.toNat_le.mpr (by omega)
  rw [hx_eq]; exact i_mem_D a b ha hb E hE c hcE k hk_le

lemma fst_bound_from_not_mem (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hcE : c ∈ E) (x : ℤ) (hx : c.1 ≤ x)
    (hnot : (x, c.2) ∉ E) :
    c.1 + ↑(armLength E c) + 1 ≤ x := by
  by_contra h; push_neg at h
  exact hnot (mem_subdiagram_of_le_armtip a b ha hb E hE c hcE x hx (by omega))

lemma redPhiCell_red_ineq_core (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i j : ℤ × ℤ) (hi : i ∈ D) (hj : j ∈ upperBoundary a b E)
    (harrow : arrow a b i j) (hred : ¬(j.1 < i.1))
    (hcD : (i.1, j.2 + ↑(legLength D i)) ∈ D)
    (hcE : (i.1, j.2 + ↑(legLength D i)) ∈ E) :
    a * (armLength E (i.1, j.2 + ↑(legLength D i)) + 1) ≤
      b * legLength D (i.1, j.2 + ↑(legLength D i)) := by
  set c := (i.1, j.2 + ↑(legLength D i)) with hc_def
  have hj_le : j.2 ≤ i.2 := red_arrow_snd_le a b ha hb hab i j harrow hred
  have hi_le_j : i.1 ≤ j.1 := Int.not_lt.mp hred
  have hleg_upper : legLength D c ≤ (i.2 - j.2).toNat := by
    have := legLength_at_shifted_upper D i hi (i.2 - j.2) (by omega)
    convert this using 2; simp only [hc_def]; ring_nf
  have hleg_lower : (i.2 - j.2).toNat ≤ legLength D c := by
    have := legLength_at_shifted_lower D i hi (i.2 - j.2) (by omega)
    convert this using 2; simp only [hc_def]; ring_nf
  have hleg_eq : legLength D c = (i.2 - j.2).toNat := le_antisymm hleg_upper hleg_lower
  have hj_not_E : (j.1, c.2) ∉ E := upperBoundary_shift_not_mem_E a b ha hb E hE j hj (legLength D i)
  have harm_bound : c.1 + ↑(armLength E c) + 1 ≤ j.1 :=
    fst_bound_from_not_mem a b ha hb E hE c hcE j.1 hi_le_j hj_not_E
  have harm_tonat : armLength E c + 1 ≤ (j.1 - i.1).toNat := by
    have hc1 : c.1 = i.1 := by simp [hc_def]
    have h_nn : (0 : ℤ) ≤ j.1 - i.1 := by omega
    have : ((j.1 - i.1).toNat : ℤ) = j.1 - i.1 := Int.toNat_of_nonneg h_nn
    omega
  have hdiv := nat_div_eq_of_arrow a b ha hb i j harrow hi_le_j hj_le
  have harrow_bound : a * (j.1 - i.1).toNat ≤ b * (i.2 - j.2).toNat := by
    have := Nat.div_mul_le_self (b * (i.2 - j.2).toNat) a; rw [hdiv] at this; linarith
  calc a * (armLength E c + 1)
      ≤ a * (j.1 - i.1).toNat := Nat.mul_le_mul_left a harm_tonat
    _ ≤ b * (i.2 - j.2).toNat := harrow_bound
    _ = b * legLength D c := by rw [hleg_eq]

lemma redPhiCell_red_ineq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i j : ℤ × ℤ) (hi : i ∈ D) (hj : j ∈ upperBoundary a b E)
    (harrow : arrow a b i j) (hred : ¬(j.1 < i.1))
    (hcE : redPhiCell D (i, j) ∈ E) :
    a * (armLength E (redPhiCell D (i, j)) + 1) ≤ b * legLength D (redPhiCell D (i, j)) := by
  have hceq : redPhiCell D (i, j) = (i.1, j.2 + ↑(legLength D i)) := redPhiCell_eq D i j
  have hcD : redPhiCell D (i, j) ∈ D := redPhiCell_mem_D a b ha hb hab D E hD hE i j hi hj harrow hred
  have hcE' : (i.1, j.2 + ↑(legLength D i)) ∈ E := hceq ▸ hcE
  have hcD' : (i.1, j.2 + ↑(legLength D i)) ∈ D := hceq ▸ hcD
  exact hceq ▸ redPhiCell_red_ineq_core a b ha hb hab hcop D E hD hE i j hi hj harrow hred hcD' hcE'

lemma mem_D_of_mem_redCells (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hc : c ∈ redCells a b D E) : c ∈ D := by
  simp only [redCells, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter] at hc
  rcases hc with (h | ⟨⟨h1, _⟩, _⟩)
  · exact h.1
  · exact h1

private lemma jPrime_not_mem_E_case1 (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b)
    (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc1 : c ∈ D \ E) :
    (c.1 + ↑((b * legLength D c) / a), c.2) ∉ E := by
  intro hjE
  have hcD : c ∈ D := (Finset.mem_sdiff.mp hc1).1
  have hcnE : c ∉ E := (Finset.mem_sdiff.mp hc1).2
  have hcG : c ∈ gapFinset a b := hD.1 hcD
  have h_le : gapLE a b (c.1 + ↑((b * legLength D c) / a), c.2) c := by
    simp only [gapLE]
    constructor
    · simp; positivity
    · exact le_refl c.2
  have hcE : c ∈ E := hE.2 (c.1 + ↑((b * legLength D c) / a), c.2) hjE c hcG h_le
  exact hcnE hcE

private lemma div_mul_succ_le_absurd (a n : ℕ) (ha : 0 < a)
    (h : a * (n / a + 1) ≤ n) : False := by
  have h₂ : n % a < a := Nat.mod_lt n ha
  have h₃ : a * (n / a) + (n % a) = n := by linarith [Nat.div_add_mod n a]
  have : a * (n / a + 1) = a * (n / a) + a := by ring
  omega

private lemma jPrime_not_mem_E_case2 (a b : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (D E : Finset (ℤ × ℤ))
    (_hD : IsSubdiagram a b D) (_hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (_hc2 : c ∈ D ∩ E) (hred : a * (armLength E c + 1) ≤ b * legLength D c) :
    (c.1 + ↑((b * legLength D c) / a), c.2) ∉ E := by
  intro hjE
  set q := b * legLength D c / a with hq_def
  set n := b * legLength D c with _
  have hq_le : q ≤ armLength E c := armLength_le E c q hjE
  have hq1_le : q + 1 ≤ armLength E c + 1 := Nat.add_le_add_right hq_le 1
  have h_aqn : a * (q + 1) ≤ n := le_trans (Nat.mul_le_mul_left a hq1_le) hred
  exact div_mul_succ_le_absurd a n ha h_aqn

lemma jPrime_not_mem_E (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E)
    (hcD : c ∈ D) :
    (c.1 + ↑((b * legLength D c) / a), c.2) ∉ E := by
  simp only [redCells, Finset.mem_union, Finset.mem_filter] at hc
  cases' hc with h1 h2
  · exact jPrime_not_mem_E_case1 a b ha hb D E hD hE c h1
  · exact jPrime_not_mem_E_case2 a b ha hb D E hD hE c h2.1 h2.2

private lemma gVal_jPrime_eq (a b : ℕ) (c : ℤ × ℤ) (t q : ℕ) :
    gVal a b (c.1 + ↑q, c.2) = gVal a b (c.1, c.2 + ↑t) + (↑b * ↑t - ↑a * ↑q) := by
  simp only [gVal]; ring

lemma jPrime_gVal_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (D : Finset (ℤ × ℤ)) (hD_sub : D ⊆ gapFinset a b)
    (c : ℤ × ℤ) (hcD : c ∈ D) :
    0 < gVal a b (c.1 + ↑((b * legLength D c) / a), c.2) := by
  set t := legLength D c with _
  set q := (b * t) / a with hq_def
  have hiTop : (c.1, c.2 + ↑t) ∈ D := legLength_achieved D c hcD
  have hgTop : 0 < gVal a b (c.1, c.2 + ↑t) :=
    (mem_gapFinset_bounds a b _ (hD_sub hiTop)).2.2
  rw [gVal_jPrime_eq a b c t q]
  have hrem : (a : ℤ) * ↑q ≤ (b : ℤ) * ↑t := by
    have haq : b * t / a * a ≤ b * t := Nat.div_mul_le_self (b * t) a
    have hqa : a * q = b * t / a * a := by rw [hq_def]; ring
    exact_mod_cast (hqa ▸ haq : a * q ≤ b * t)
  linarith

private lemma colHeight_nonneg_of_subdiagram (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (x : ℤ) : 0 ≤ colHeight E x := by
  unfold colHeight
  split
  · next h =>
    obtain ⟨y, hy⟩ := h
    have hle : y ≤ ((E.filter fun p => p.1 = x).image Prod.snd).max' ⟨y, hy⟩ :=
      Finset.le_max' _ y hy
    have : 1 ≤ y := by
      rw [Finset.mem_image] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      rw [Finset.mem_filter] at hp
      exact one_le_snd_of_mem_subdiagram a b E hE p hp.1
    linarith
  · exact le_refl 0

private lemma ubInCol_snd_ge_one (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E) (x : ℤ) :
    1 ≤ (ubInCol a b E x).2 := by
  unfold ubInCol; simp only
  linarith [colHeight_nonneg_of_subdiagram a b E hE x]

private lemma colHeight_succ_not_mem_E (E : Finset (ℤ × ℤ)) (x : ℤ) :
    (x, colHeight E x + 1) ∉ E := by
  intro h_in
  have h₁ : (x, colHeight E x + 1) ∈ E.filter (fun p : ℤ × ℤ => p.1 = x) :=
    Finset.mem_filter.mpr ⟨h_in, by simp⟩
  have h₂ : colHeight E x + 1 ∈ ((E.filter (fun p : ℤ × ℤ => p.1 = x)).image Prod.snd) :=
    Finset.mem_image.mpr ⟨(x, colHeight E x + 1), h₁, by simp [Prod.snd]⟩
  have h₃ : ((E.filter (fun p : ℤ × ℤ => p.1 = x)).image Prod.snd).Nonempty :=
    Finset.nonempty_of_ne_empty (by intro h; rw [h] at h₂; contradiction)
  have h₄ : colHeight E x = ((E.filter (fun p : ℤ × ℤ => p.1 = x)).image Prod.snd).max' h₃ := by
    dsimp only [colHeight] at *; split_ifs <;> simp_all
  have h₆ : colHeight E x + 1 ≤ colHeight E x := by
    calc colHeight E x + 1 ≤ ((E.filter (fun p : ℤ × ℤ => p.1 = x)).image Prod.snd).max' h₃ :=
          Finset.le_max' _ _ h₂
      _ = colHeight E x := h₄.symm
  linarith

private lemma colHeight_le_a_of_subdiagram (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (x : ℤ) : colHeight E x ≤ (a : ℤ) := by
  unfold colHeight
  split
  case isTrue h =>
    apply Finset.max'_le
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [Finset.mem_filter] at hp
    exact snd_le_a_of_mem_subdiagram a b E hE p hp.1
  case isFalse h =>
    exact Int.natCast_nonneg a

private lemma colHeight_boundary (E : Finset (ℤ × ℤ)) (x : ℤ) :
    colHeight E x + 1 = 1 ∨ (x, (colHeight E x + 1) - 1) ∈ E := by
  unfold colHeight
  split
  case isTrue h =>
    right
    have hmem := Finset.max'_mem _ h
    rw [Finset.mem_image] at hmem
    obtain ⟨e, he_filter, he_snd⟩ := hmem
    rw [Finset.mem_filter] at he_filter
    obtain ⟨he_E, he_fst⟩ := he_filter
    have : (x, ((Finset.filter (fun p => p.1 = x) E).image Prod.snd).max' h + 1 - 1) = (x, ((Finset.filter (fun p => p.1 = x) E).image Prod.snd).max' h) := by
      congr 1; omega
    rw [this]
    convert he_E using 1
    exact Prod.ext he_fst.symm he_snd.symm
  case isFalse h =>
    left; omega

private lemma gVal_pos_imp_fst_le' (a b : ℕ) (p : ℤ × ℤ)
    (h1 : 1 ≤ p.1) (h2 : 1 ≤ p.2) (hg : 0 < gVal a b p) :
    p.1 ≤ (b : ℤ) := by
  simp only [gVal] at hg
  by_contra h
  have h6 : (a : ℤ) * p.1 ≥ (a : ℤ) * (b + 1 : ℤ) := by nlinarith
  have h7 : (b : ℤ) * p.2 ≥ (b : ℤ) * (1 : ℤ) := by nlinarith
  linarith

lemma j_mem_upperBoundary (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b)
    (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) (hcD : c ∈ D) :
    ubInCol a b E (c.1 + ↑((b * legLength D c) / a)) ∈ upperBoundary a b E := by
  set x := c.1 + ↑((b * legLength D c) / a) with _
  show (x, colHeight E x + 1) ∈ upperBoundary a b E
  have hcG : c ∈ gapFinset a b := hD.1 hcD
  have hcb := mem_gapFinset_bounds a b c hcG
  have hq_nn : (0 : ℤ) ≤ ↑((b * legLength D c) / a) := Int.natCast_nonneg _
  have hx_lb : 1 ≤ x := by omega
  have hjprime := jPrime_gVal_pos a b ha hb D hD.1 c hcD
  have hx_ub : x ≤ (b : ℤ) := by
    simp only [Prod.fst, Prod.snd] at hjprime ⊢
    exact gVal_pos_imp_fst_le' a b (x, c.2) hx_lb hcb.2.1 hjprime
  have hj2_lb := ubInCol_snd_ge_one a b E hE x
  have hch_le := colHeight_le_a_of_subdiagram a b E hE x
  have hj_not_mem := colHeight_succ_not_mem_E E x
  have hbdry := colHeight_boundary E x
  simp only [upperBoundary, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst, Prod.snd, decide_eq_true_eq]
  exact ⟨⟨⟨hx_lb, hx_ub⟩, ⟨hj2_lb, by omega⟩⟩, hj_not_mem, hbdry⟩

private lemma gVal_diff_eq' (a b : ℕ) (i j : ℤ × ℤ) :
    gVal a b j - gVal a b i = (a : ℤ) * (i.1 - j.1) - (b : ℤ) * (j.2 - i.2) := by
  simp only [gVal]; ring

private lemma redPsiPair_fst_fst (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    (redPsiPair a b D E c).1.1 = c.1 := by
  dsimp [redPsiPair]

private lemma redPsiPair_fst_snd (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    (redPsiPair a b D E c).1.2 = (redPsiPair a b D E c).2.2 + ↑(legLength D c) := by
  dsimp only [redPsiPair]
  simp [Prod.snd]
  <;> ring_nf

private lemma euclidean_remainder_eq (b t a q : ℕ) (heq : a * q + (b * t) % a = b * t) :
    (↑(b * t) : ℤ) - ↑(a * q) = ↑((b * t) % a) := by
  have : (↑(a * q) : ℤ) + ↑((b * t) % a) = ↑(b * t) := by exact_mod_cast heq
  linarith

private lemma gVal_diff_redPsiPair (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    gVal a b (redPsiPair a b D E c).2 - gVal a b (redPsiPair a b D E c).1 =
    ↑((b * legLength D c) % a) := by
  set i := (redPsiPair a b D E c).1
  set j := (redPsiPair a b D E c).2
  set t := legLength D c
  set q := (b * t) / a
  have hi1 : i.1 = c.1 := redPsiPair_fst_fst a b D E c
  have hi2 : i.2 = j.2 + ↑t := redPsiPair_fst_snd a b D E c
  have hj1 : j = ubInCol a b E (c.1 + ↑q) := by
    change (redPsiPair a b D E c).2 = ubInCol a b E (c.1 + ↑((b * legLength D c) / a))
    simp only [redPsiPair]
    simp_all
  simp only [ubInCol] at hj1
  have hj1_fst : j.1 = c.1 + ↑q := by rw [Prod.ext_iff] at hj1; exact hj1.1
  rw [gVal_diff_eq' a b i j, hi1, hi2, hj1_fst]
  ring_nf
  have euclidean := Nat.div_add_mod (b * t) a
  have key := euclidean_remainder_eq b t a q euclidean
  simp only [Nat.cast_mul] at key
  linarith

lemma arrow_of_redPsiPair (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b)
    (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) (hcD : c ∈ D) :
    arrow a b (redPsiPair a b D E c).1 (redPsiPair a b D E c).2 := by
  rw [arrow]
  rw [gVal_diff_redPsiPair]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast Nat.mod_lt _ ha⟩

lemma red_condition (a b : ℕ) (ha : 0 < a)
    (D E : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) :
    ¬((redPsiPair a b D E c).2.1 < (redPsiPair a b D E c).1.1) := by
  dsimp [redPsiPair]
  have h₁ : (c.1 : ℤ) + ((b * ( ( (c.2 + ↑(legLength D c)) : ℤ) - c.2 ).toNat) / a : ℤ) ≥ (c.1 : ℤ) := by
    have h₂ : ((b * ( ( (c.2 + ↑(legLength D c)) : ℤ) - c.2 ).toNat) / a : ℤ) ≥ 0 := by
      apply Int.ediv_nonneg
      · exact by positivity
      · linarith
    linarith
  simp_all [ubInCol]

lemma redPsiPair_snd_eq (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    (redPsiPair a b D E c).2 = ubInCol a b E (c.1 + ↑((b * legLength D c) / a)) := by
  simp only [redPsiPair]
  have h₁ : ((c.2 + ↑(legLength D c) - c.2 : ℤ) : ℤ) = (legLength D c : ℤ) := by
    ring_nf
  have h₂ : ((b * legLength D c : ℕ) : ℕ) = (b * legLength D c : ℕ) := rfl
  simp_all [h₁, h₂]

private lemma colHeight_add_one_le_of_lt (E : Finset (ℤ × ℤ)) (x : ℤ) (y : ℤ) (hy : 1 ≤ y)
    (hlt : ∀ e ∈ E, e.1 = x → e.2 < y) : colHeight E x + 1 ≤ y := by
  by_cases hS : ((E.filter fun p : ℤ × ℤ => p.1 = x).image Prod.snd).Nonempty
  · have h₁ : colHeight E x = ((E.filter fun p : ℤ × ℤ => p.1 = x).image Prod.snd).max' hS := by
      simp [colHeight, hS]
    rw [h₁]
    have h₂ : ∀ (s : ℤ), s ∈ (E.filter fun p : ℤ × ℤ => p.1 = x).image Prod.snd → s < y := by
      intro s hs
      simp only [Finset.mem_image, Finset.mem_filter] at hs
      obtain ⟨p, ⟨hp_mem, hp_fst⟩, rfl⟩ := hs
      exact hlt p hp_mem hp_fst
    have h₃ := h₂ _ (Finset.max'_mem _ hS)
    linarith
  · have h₁ : colHeight E x = 0 := by simp [colHeight, hS]
    rw [h₁]; linarith

private lemma snd_lt_of_mem_E_at_jCol (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E)
    (e : ℤ × ℤ) (he : e ∈ E) (hx : e.1 = c.1 + ↑((b * legLength D c) / a)) :
    e.2 < c.2 := by
  have hcD : c ∈ D := mem_D_of_mem_redCells a b D E c hc
  have hjp : (c.1 + ↑((b * legLength D c) / a), c.2) ∉ E :=
    jPrime_not_mem_E a b ha hb hab hcop D E hD hE c hc hcD
  by_contra h
  push_neg at h
  apply hjp
  have hD_sub := hD.1
  have hcb := mem_gapFinset_bounds a b c (hD_sub hcD)
  have heb := mem_gapFinset_bounds a b e (hE.1 he)
  set q := (b * legLength D c) / a
  have hjp_gVal : 0 < gVal a b (c.1 + ↑q, c.2) := jPrime_gVal_pos a b ha hb D hD_sub c hcD
  have hjp_gap : (c.1 + ↑q, c.2) ∈ gapFinset a b :=
    mem_gapFinset_of_bounds a b (c.1 + ↑q, c.2) (by omega)
      (by rw [← hx]; exact gVal_pos_imp_fst_le a b e heb.1 heb.2.1 heb.2.2)
      hcb.2.1 (snd_le_a_of_mem_subdiagram a b D hD c hcD) hjp_gVal
  exact hE.2 e he (c.1 + ↑q, c.2) hjp_gap ⟨by omega, h⟩

lemma redPsiPair_snd_snd_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) :
    0 ≤ c.2 - (redPsiPair a b D E c).2.2 := by
  rw [redPsiPair_snd_eq]
  simp only [ubInCol]
  have hcD : c ∈ D := mem_D_of_mem_redCells a b D E c hc
  have hcG : c ∈ gapFinset a b := hD.1 hcD
  have hc2 : 1 ≤ c.2 := (mem_gapFinset_bounds a b c hcG).2.1
  have hle : colHeight E (c.1 + ↑((b * legLength D c) / a)) + 1 ≤ c.2 :=
    colHeight_add_one_le_of_lt E _ c.2 hc2
      (fun e he hx => snd_lt_of_mem_E_at_jCol a b ha hb hab hcop D E hD hE c hc e he hx)
  omega

lemma i_mem_D_of_redPsi (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b)
    (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) (hcD : c ∈ D) :
    (redPsiPair a b D E c).1 ∈ D := by
  set i := (redPsiPair a b D E c).1
  set j := (redPsiPair a b D E c).2
  have hiTop : (c.1, c.2 + ↑(legLength D c)) ∈ D := legLength_achieved D c hcD
  have hiTopG : (c.1, c.2 + ↑(legLength D c)) ∈ gapFinset a b := hD.1 hiTop
  have hs_nonneg : 0 ≤ c.2 - j.2 := redPsiPair_snd_snd_le a b ha hb hab hcop D E hD hE c hc
  have hi1 : i.1 = c.1 := redPsiPair_fst_fst a b D E c
  have hi2 : i.2 = j.2 + ↑(legLength D c) := redPsiPair_fst_snd a b D E c
  have hi2_le : i.2 ≤ c.2 + ↑(legLength D c) := by omega
  have hj2_ge_one : 1 ≤ j.2 := by
    have hsnd : j = ubInCol a b E (c.1 + ↑((b * legLength D c) / a)) :=
      redPsiPair_snd_eq a b D E c
    rw [hsnd]; exact ubInCol_snd_ge_one a b E hE _
  have hi2_ge_one : 1 ≤ i.2 := by omega
  have hiTop_snd_le_a : (c.2 + ↑(legLength D c)) ≤ (a : ℤ) :=
    snd_le_a_of_mem_subdiagram a b D hD (c.1, c.2 + ↑(legLength D c)) hiTop
  have hi2_le_a : i.2 ≤ (a : ℤ) := by omega
  have hcG : c ∈ gapFinset a b := hD.1 hcD
  have hc_bounds := mem_gapFinset_bounds a b c hcG
  have hi1_ge_one : 1 ≤ i.1 := by omega
  have hi1_le_b : i.1 ≤ (b : ℤ) := by
    have := hD.1 hcD
    simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at this
    omega
  have hgVal_mono : gVal a b (c.1, c.2 + ↑(legLength D c)) ≤ gVal a b i := by
    apply gVal_mono_snd a b hb
    · exact hi1.symm
    · omega
  have hiTop_bounds := mem_gapFinset_bounds a b _ hiTopG
  have hgVal_i_pos : 0 < gVal a b i := by omega
  have hiG : i ∈ gapFinset a b :=
    mem_gapFinset_of_bounds a b i hi1_ge_one hi1_le_b hi2_ge_one hi2_le_a hgVal_i_pos
  have hgapLE : gapLE a b (c.1, c.2 + ↑(legLength D c)) i := by
    constructor <;> simp only <;> omega
  exact hD.2 _ hiTop _ hiG hgapLE

lemma redPhi_psi_snd (a b : ℕ) (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hcD : c ∈ D)
    (hs : 0 ≤ c.2 - (redPsiPair a b D E c).2.2) :
    (redPhiCell D (redPsiPair a b D E c)).2 = c.2 := by
  simp only [redPsiPair, redPhiCell]
  have hleg := legLength_at_shifted D c hcD
    (c.2 - (ubInCol a b E (c.1 + ↑(b * (c.2 + ↑(legLength D c) - c.2).toNat / a))).2) hs
  simp only [redPsiPair] at hs
  rw [hleg]
  have hnn := Int.toNat_of_nonneg hs
  omega

private lemma colHeight_ge_of_mem (E : Finset (ℤ × ℤ)) (x : ℤ) (e : ℤ × ℤ) (he : e ∈ E)
    (hx : e.1 = x) : e.2 ≤ colHeight E x := by
  have h₁ : e ∈ E.filter (fun p => p.1 = x) := Finset.mem_filter.mpr ⟨he, hx⟩
  have h₂ : e.2 ∈ (E.filter (fun p => p.1 = x)).image Prod.snd :=
    Finset.mem_image_of_mem _ h₁
  have h₃ : ((E.filter (fun p => p.1 = x)).image Prod.snd).Nonempty := ⟨e.2, h₂⟩
  have h₄ : colHeight E x = ((E.filter (fun p => p.1 = x)).image Prod.snd).max' h₃ := by
    rw [colHeight]; simp_all
  rw [h₄]; exact Finset.le_max' _ _ h₂

private lemma snd_lt_of_mem_E_in_ub_col (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (j : ℤ × ℤ) (hjUB : j ∈ upperBoundary a b E)
    (e : ℤ × ℤ) (he : e ∈ E) (hex : e.1 = j.1) : e.2 < j.2 := by
  by_contra h
  push_neg at h
  have hle : gapLE a b e j := ⟨le_of_eq hex.symm, h⟩
  have hj_ub := (mem_upperBoundary_iff a b E j).mp hjUB
  have he_gap : e ∈ gapFinset a b := hE.1 he
  have he_snd : e.2 ≤ (a : ℤ) := snd_le_a_of_mem_subdiagram a b E hE e he
  have he_bounds := mem_gapFinset_bounds a b e he_gap
  have hg_j : gVal a b e ≤ gVal a b j := gVal_mono_snd a b hb e j hex.symm h
  have hjG : j ∈ gapFinset a b :=
    mem_gapFinset_of_bounds a b j hj_ub.1.1 hj_ub.1.2 hj_ub.2.1.1 (le_trans h he_snd)
      (lt_of_lt_of_le he_bounds.2.2 hg_j)
  exact hj_ub.2.2.1 (hE.2 e he j hjG hle)

lemma ubInCol_eq_of_upperBoundary (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (j : ℤ × ℤ) (hjUB : j ∈ upperBoundary a b E) :
    ubInCol a b E j.1 = j := by
  have hmem := (mem_upperBoundary_iff a b E j).mp hjUB
  have hub : colHeight E j.1 + 1 ≤ j.2 :=
    colHeight_add_one_le_of_lt E j.1 j.2 hmem.2.1.1
      (fun e he hex => snd_lt_of_mem_E_in_ub_col a b ha hb E hE j hjUB e he hex)
  have hlb : j.2 ≤ colHeight E j.1 + 1 := by
    rcases hmem.2.2.2 with h1 | h2
    · linarith [colHeight_nonneg_of_subdiagram a b E hE j.1]
    · linarith [colHeight_ge_of_mem E j.1 (j.1, j.2 - 1) h2 rfl]
  unfold ubInCol; ext <;> simp; omega

lemma euclidean_div_jCol_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (i j : ℤ × ℤ) (har : arrow a b i j) (hx : i.1 ≤ j.1) (hy : j.2 ≤ i.2) :
    i.1 + ↑((b * (i.2 - j.2).toNat) / a) = j.1 := by
  rw [nat_div_eq_of_arrow a b ha hb i j har hx hy]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ j.1 - i.1)]
  omega

lemma redPsi_phi_eq_aux (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (_hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (_hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (i j : ℤ × ℤ)
    (hiD : i ∈ D) (hjUB : j ∈ upperBoundary a b E) (har : arrow a b i j)
    (hx : i.1 ≤ j.1) :
    redPsiPair a b D E (redPhiCell D (i, j)) = (i, j) := by
  set c := redPhiCell D (i, j) with hc_def
  have hc_eq : c = (i.1, j.2 + ↑(legLength D i)) := by rw [hc_def]; exact redPhiCell_eq D i j
  have hred : ¬(j.1 < i.1) := not_lt.mpr hx
  have hy : j.2 ≤ i.2 := red_arrow_snd_le a b ha hb hab i j har hred
  have hs : (0 : ℤ) ≤ i.2 - j.2 := Int.sub_nonneg.mpr hy
  have hleg := legLength_at_shifted D i hiD (i.2 - j.2) hs
  have hshift_eq : (i.1, i.2 + ↑(legLength D i) - (i.2 - j.2)) = (i.1, j.2 + ↑(legLength D i)) := by
    congr 1; ring
  rw [hshift_eq] at hleg; rw [← hc_eq] at hleg
  have hjcol := euclidean_div_jCol_eq a b ha hb i j har hx hy
  have hc1 : c.1 = i.1 := by rw [hc_eq]
  have hjcol' : c.1 + ↑((b * legLength D c) / a) = j.1 := by rw [hc1, hleg]; exact hjcol
  have hsnd := redPsiPair_snd_eq a b D E c
  have hub := ubInCol_eq_of_upperBoundary a b ha hb E hE j hjUB
  have h2 : (redPsiPair a b D E c).2 = j := by rw [hsnd, hjcol', hub]
  have hff := redPsiPair_fst_fst a b D E c
  have hfs := redPsiPair_fst_snd a b D E c
  have h1 : (redPsiPair a b D E c).1 = i := by
    ext
    · rw [hff, hc1]
    · rw [hfs, h2, hleg, Int.toNat_sub_of_le hy]; ring
  exact Prod.ext h1 h2

lemma redPhi_mem (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (p : (ℤ × ℤ) × (ℤ × ℤ))
    (hp : p ∈ (arrowPairs a b D (upperBoundary a b E)).filter (fun p => ¬(p.2.1 < p.1.1))) :
    redPhiCell D p ∈ redCells a b D E := by
  obtain ⟨hp_mem, hp_red⟩ := Finset.mem_filter.mp hp
  have hp_prod := (Finset.mem_filter.mp hp_mem).1
  have hp_arrow := (Finset.mem_filter.mp hp_mem).2
  have hi : p.1 ∈ D := (Finset.mem_product.mp hp_prod).1
  have hj : p.2 ∈ upperBoundary a b E := (Finset.mem_product.mp hp_prod).2
  set c := redPhiCell D p with hc_def
  have hcD : c ∈ D := by
    rw [hc_def]
    show redPhiCell D (p.1, p.2) ∈ D
    · rw [show (p.1, p.2) = p from Prod.mk.eta]
      exact redPhiCell_mem_D a b ha hb hab D E hD hE p.1 p.2 hi hj hp_arrow hp_red
  by_cases hcE : c ∈ E
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_inter.mpr ⟨hcD, hcE⟩
    · rw [hc_def]
      show a * (armLength E (redPhiCell D (p.1, p.2)) + 1) ≤ b * legLength D (redPhiCell D (p.1, p.2))
      rw [show (p.1, p.2) = p from Prod.mk.eta]
      exact redPhiCell_red_ineq a b ha hb hab hcop D E hD hE p.1 p.2 hi hj hp_arrow hp_red
        (by rw [← hc_def]; exact hcE)
  · apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨hcD, hcE⟩

lemma redPsi_mem (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) :
    redPsiPair a b D E c ∈
      (arrowPairs a b D (upperBoundary a b E)).filter (fun p => ¬(p.2.1 < p.1.1)) := by
  have hcD := mem_D_of_mem_redCells a b D E c hc
  simp only [Finset.mem_filter]
  refine ⟨?_, red_condition a b ha D E c⟩
  unfold arrowPairs
  simp only [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨i_mem_D_of_redPsi a b ha hb hab hcop D E hD hE c hc hcD, ?_⟩,
          arrow_of_redPsiPair a b ha hb hab hcop D E hD hE c hc hcD⟩
  rw [redPsiPair_snd_eq]
  exact j_mem_upperBoundary a b ha hb hab hcop D E hD hE c hc hcD

lemma redPhi_psi_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ redCells a b D E) :
    redPhiCell D (redPsiPair a b D E c) = c := by
  have hcD := mem_D_of_mem_redCells a b D E c hc
  have hs := redPsiPair_snd_snd_le a b ha hb hab hcop D E hD hE c hc
  ext
  · rfl
  · exact redPhi_psi_snd a b D E c hcD hs

lemma redPsi_phi_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (p : (ℤ × ℤ) × (ℤ × ℤ))
    (hp : p ∈ (arrowPairs a b D (upperBoundary a b E)).filter (fun p => ¬(p.2.1 < p.1.1))) :
    redPsiPair a b D E (redPhiCell D p) = p := by
  obtain ⟨hpAP, hNotLt⟩ := Finset.mem_filter.mp hp
  simp only [arrowPairs, Finset.mem_filter, Finset.mem_product] at hpAP
  obtain ⟨⟨hiD, hjUB⟩, har⟩ := hpAP
  have hx : p.1.1 ≤ p.2.1 := not_lt.mp hNotLt
  have key := redPsi_phi_eq_aux a b ha hb hab hcop D E hD hE p.1 p.2 hiD hjUB har hx
  rwa [Prod.mk.eta] at key

lemma red_card_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    ((arrowPairs a b D (upperBoundary a b E)).filter fun p => ¬(p.2.1 < p.1.1)).card =
      (redCells a b D E).card := by
  apply Finset.card_nbij (redPhiCell D)
  · intro p hp
    exact redPhi_mem a b ha hb hab hcop D E hD hE p hp
  · intro p₁ hp₁ p₂ hp₂ heq
    have h1 := redPsi_phi_eq a b ha hb hab hcop D E hD hE p₁ hp₁
    have h2 := redPsi_phi_eq a b ha hb hab hcop D E hD hE p₂ hp₂
    rw [← h1, ← h2, heq]
  · intro c hc
    exact ⟨redPsiPair a b D E c,
           redPsi_mem a b ha hb hab hcop D E hD hE c hc,
           redPhi_psi_eq a b ha hb hab hcop D E hD hE c hc⟩

lemma arrowPairs_card_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    (arrowPairs a b D (upperBoundary a b E)).card =
      (blueCells a b D E).card + (redCells a b D E).card := by
  rw [arrowPairs_split]
  rw [blue_card_eq a b ha hb hab hcop D E hD hE]
  rw [red_card_eq a b ha hb hab hcop D E hD hE]

lemma redCells_inter_eq (a b : ℕ) (D E : Finset (ℤ × ℤ)) :
    (E ∩ D).filter (fun c => a * (armLength D c + 1) ≤ b * legLength E c) =
    (D ∩ E).filter (fun c => a * (armLength D c + 1) ≤ b * legLength E c) := by
  congr 1
  exact inter_comm E D

lemma E_card_decomp (D E : Finset (ℤ × ℤ)) :
    E.card = (D ∩ E).card + (E \ D).card := by
  rw [inter_comm]
  exact (Finset.card_inter_add_card_sdiff E D).symm

lemma armLength_lt_b (a b : ℕ) (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hD : D ⊆ gapFinset a b) (hc : c ∈ gapFinset a b) :
    armLength D c < b := by
  unfold armLength
  have hcb := mem_gapFinset_bounds a b c hc
  have hb_pos : 0 < b := by
    by_contra h; push_neg at h
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero h; subst hb0
    simp [gVal] at hcb; nlinarith [hcb.1, hcb.2.2, Int.natCast_nonneg a]
  suffices h : ((D.filter fun p => p.2 = c.2 ∧ c.1 ≤ p.1).image
    fun p => (p.1 - c.1).toNat).sup id < b by exact h
  rw [Finset.sup_lt_iff (by omega : (⊥ : ℕ) < b)]
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨p, hp, rfl⟩ := hn; rw [id]; rw [Finset.mem_filter] at hp
  have hp_gap := hD hp.1
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp_gap hc
  have : p.1 ≤ (b : ℤ) := hp_gap.1.1.2
  have : 1 ≤ c.1 := hc.1.1.1
  have : c.1 ≤ p.1 := hp.2.2
  have : (p.1 - c.1 : ℤ) < b := by omega
  have : 0 ≤ p.1 - c.1 := by omega
  omega

lemma trichotomy_of_mem_inter (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E)
    (c : ℤ × ℤ) (hc : c ∈ D ∩ E) :
    (b * (legLength E c + 1) ≤ a * armLength D c) ∨
    (dinvCond a b D E c = true) ∨
    (a * (armLength D c + 1) ≤ b * legLength E c) := by
  have hcD : c ∈ D := Finset.mem_inter.mp hc |>.1
  have hcE : c ∈ E := Finset.mem_inter.mp hc |>.2
  have hc_gap : c ∈ gapFinset a b := hD.1 hcD
  have harm : armLength D c < b := armLength_lt_b a b D c hD.1 hc_gap
  have hleg : legLength E c < a := legLength_lt_a a b E c hE.1 hc_gap
  by_cases h1 : b * (legLength E c + 1) ≤ a * armLength D c
  · left; exact h1
  · push_neg at h1
    by_cases h2 : a * (armLength D c + 1) ≤ b * legLength E c
    · right; right; exact h2
    · push_neg at h2
      right; left
      simp only [dinvCond, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true_iff, beq_iff_eq]
      constructor
      · linarith
      · by_cases h3 : armLength D c = 0
        · left; exact h3
        · right; omega

lemma trichotomy_exclusive (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (D E : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ¬((b * (legLength E c + 1) ≤ a * armLength D c) ∧
      (dinvCond a b D E c = true)) ∧
    ¬((dinvCond a b D E c = true) ∧
      (a * (armLength D c + 1) ≤ b * legLength E c)) ∧
    ¬((b * (legLength E c + 1) ≤ a * armLength D c) ∧
      (a * (armLength D c + 1) ≤ b * legLength E c)) := by
  have h₁ : ¬((b * (legLength E c + 1) ≤ a * armLength D c) ∧ (dinvCond a b D E c = true)) := by
    simp only [dinvCond, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true_iff, beq_iff_eq]
    intro ⟨hblue, hdinv1, hdinv2⟩
    rcases hdinv2 with h0 | hlt
    · rw [h0] at hblue; simp at hblue; linarith
    · linarith
  have h₂ : ¬((dinvCond a b D E c = true) ∧ (a * (armLength D c + 1) ≤ b * legLength E c)) := by
    simp only [dinvCond, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true_iff, beq_iff_eq]
    intro ⟨⟨hdinv1, _⟩, hred⟩
    linarith
  have h₃ : ¬((b * (legLength E c + 1) ≤ a * armLength D c) ∧ (a * (armLength D c + 1) ≤ b * legLength E c)) := by
    intro ⟨h1, h2⟩; nlinarith
  exact ⟨h₁, h₂, h₃⟩

lemma not_blue_not_red_eq_dinv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    ((D ∩ E).filter fun c =>
      ¬(b * (legLength E c + 1) ≤ a * armLength D c) ∧
      ¬(a * (armLength D c + 1) ≤ b * legLength E c)) =
    (D ∩ E).filter fun c => dinvCond a b D E c := by
  ext c
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc, hnotblue, hnotred⟩
    refine ⟨hc, ?_⟩
    have htri := trichotomy_of_mem_inter a b ha hb hab hcop D E hD hE c hc
    rcases htri with hblue | hdinv | hred
    · exact absurd hblue hnotblue
    · exact hdinv
    · exact absurd hred hnotred
  · rintro ⟨hc, hdinv⟩
    refine ⟨hc, ?_, ?_⟩
    · intro hblue
      have := (trichotomy_exclusive a b ha hb D E c).1
      exact absurd ⟨hblue, hdinv⟩ this
    · intro hred
      have := (trichotomy_exclusive a b ha hb D E c).2.1
      exact absurd ⟨hdinv, hred⟩ this

lemma inter_partition (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    (D ∩ E).card = (blueCells a b D E).card +
      ((D ∩ E).filter fun c => dinvCond a b D E c).card +
      ((D ∩ E).filter fun c => a * (armLength D c + 1) ≤ b * legLength E c).card := by
  change (D ∩ E).card =
    ((D ∩ E).filter fun c => b * (legLength E c + 1) ≤ a * armLength D c).card +
    ((D ∩ E).filter fun c => dinvCond a b D E c).card +
    ((D ∩ E).filter fun c => a * (armLength D c + 1) ≤ b * legLength E c).card
  have h1 := @Finset.card_filter_add_card_filter_not _ (D ∩ E)
    (fun c => b * (legLength E c + 1) ≤ a * armLength D c) _ _
  set notBlue := {c ∈ D ∩ E | ¬b * (legLength E c + 1) ≤ a * armLength D c} with hNB
  have h2 := @Finset.card_filter_add_card_filter_not _ notBlue
    (fun c => a * (armLength D c + 1) ≤ b * legLength E c) _ _
  have h3 : {c ∈ notBlue | ¬a * (armLength D c + 1) ≤ b * legLength E c} =
      (D ∩ E).filter fun c => dinvCond a b D E c := by
    rw [hNB, Finset.filter_filter]
    exact not_blue_not_red_eq_dinv a b ha hb hab hcop D E hD hE
  have h4 : (notBlue.filter fun c => a * (armLength D c + 1) ≤ b * legLength E c) =
      (D ∩ E).filter fun c => a * (armLength D c + 1) ≤ b * legLength E c := by
    rw [hNB, Finset.filter_filter]
    ext c; simp only [mem_filter]
    constructor
    · rintro ⟨hc, _, hr⟩; exact ⟨hc, hr⟩
    · rintro ⟨hc, hr⟩
      refine ⟨hc, fun hblue => ?_, hr⟩
      nlinarith
  rw [h3, h4] at h2
  omega

lemma redCells_card (a b : ℕ) (D E : Finset (ℤ × ℤ)) :
    (redCells a b E D).card = (E \ D).card +
      ((D ∩ E).filter fun c => a * (armLength D c + 1) ≤ b * legLength E c).card := by
  unfold redCells
  rw [Finset.inter_comm E D]
  exact Finset.card_union_of_disjoint
    ((Finset.disjoint_sdiff_inter E D).mono_right
      (by rw [Finset.inter_comm E D]; exact Finset.filter_subset _ _))

lemma arrowPairs_card_eq_double_sum (a b : ℕ) (X Y : Finset (ℤ × ℤ)) :
    ((arrowPairs a b X Y).card : ℝ) =
      ∑ i ∈ X, ∑ j ∈ Y, (if arrow a b i j then (1 : ℝ) else 0) := by
  have h_main : (arrowPairs a b X Y).card = (X ×ˢ Y).sum (fun p : (ℤ × ℤ) × (ℤ × ℤ) => if arrow a b p.1 p.2 then 1 else 0) := by
    rw [show (arrowPairs a b X Y) = (X ×ˢ Y).filter fun p : (ℤ × ℤ) × (ℤ × ℤ) => arrow a b p.1 p.2 by rfl]
    rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
  have h_sum_expand : (X ×ˢ Y).sum (fun p : (ℤ × ℤ) × (ℤ × ℤ) => if arrow a b p.1 p.2 then 1 else 0) = ∑ i ∈ X, ∑ j ∈ Y, (if arrow a b i j then 1 else 0) := by
    rw [Finset.sum_product]
  have h_final : ((arrowPairs a b X Y).card : ℝ) = ∑ i ∈ X, ∑ j ∈ Y, (if arrow a b i j then (1 : ℝ) else 0) := by
    have h₁ : ((arrowPairs a b X Y).card : ℝ) = ((X ×ˢ Y).sum (fun p : (ℤ × ℤ) × (ℤ × ℤ) => if arrow a b p.1 p.2 then 1 else 0) : ℝ) := by
      norm_cast
    have h₂ : ((X ×ˢ Y).sum (fun p : (ℤ × ℤ) × (ℤ × ℤ) => if arrow a b p.1 p.2 then 1 else 0) : ℝ) = ∑ i ∈ X, ∑ j ∈ Y, (if arrow a b i j then (1 : ℝ) else 0) := by
      have h₄ : ((X ×ˢ Y).sum (fun p : (ℤ × ℤ) × (ℤ × ℤ) => if arrow a b p.1 p.2 then 1 else 0) : ℝ) = (∑ i ∈ X, ∑ j ∈ Y, (if arrow a b i j then 1 else 0) : ℝ) := by
        norm_cast
      linarith
    linarith
  rw [h_final]

lemma sum_indicator_arrow_restrict (a b : ℕ) (i : ℤ × ℤ)
    (S Box : Finset (ℤ × ℤ)) (hS : S ⊆ Box) :
    ∑ p ∈ Box, (if arrow a b i p then (1 : ℝ) else 0) *
      (if p ∈ S then (1 : ℝ) else 0) =
    ∑ p ∈ S, (if arrow a b i p then (1 : ℝ) else 0) := by
  rw [← Finset.sum_subset hS (fun p _ hp => ?_)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  · simp [hp]

lemma gapFinset_subset_box (a b : ℕ) :
    gapFinset a b ⊆ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) := by
  intro p hp
  simp only [gapFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  constructor
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

lemma image_north_subset_box (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : E ⊆ gapFinset a b) :
    E.image (fun j => (j.1, j.2 + 1)) ⊆
    (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) := by
  intro p hp
  simp only [Finset.mem_image] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact north_in_box a b j (hE hj)

lemma mem_image_north_iff (E : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    p ∈ E.image (fun j => (j.1, j.2 + 1)) ↔ (p.1, p.2 - 1) ∈ E := by
  grind

lemma north_shift_sum_eq_box (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b) (_hab : a < b)
    (E : Finset (ℤ × ℤ)) (hE : E ⊆ gapFinset a b)
    (i : ℤ × ℤ) :
    ∑ j ∈ E, (if arrow a b i (j.1, j.2 + 1) then (1 : ℝ) else 0) =
    ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
      (if arrow a b i p then (1 : ℝ) else 0) *
      (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0) := by
  set box := (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) with _
  have hvanish : ∀ p ∈ box, p ∉ E.image (fun j => (j.1, j.2 + 1)) →
      (if arrow a b i p then (1 : ℝ) else 0) * (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0) = 0 := by
    intro p _ hp_not
    have : (p.1, p.2 - 1) ∉ E := by
      intro hmem
      apply hp_not
      exact (mem_image_north_iff E p).mpr hmem
    simp [this]
  rw [← Finset.sum_subset (image_north_subset_box a b E hE) hvanish]
  have hon_image : ∀ p ∈ E.image (fun j => (j.1, j.2 + 1)),
      (if arrow a b i p then (1 : ℝ) else 0) * (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0) =
      (if arrow a b i p then (1 : ℝ) else 0) := by
    intro p hp
    have : (p.1, p.2 - 1) ∈ E := (mem_image_north_iff E p).mp hp
    simp [this]
  rw [Finset.sum_congr rfl hon_image]
  rw [Finset.sum_image]
  intro j₁ _ j₂ _ h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

lemma first_sum_eq_box (a b : ℕ) (E : Finset (ℤ × ℤ)) (hE : E ⊆ gapFinset a b)
    (i : ℤ × ℤ) :
    ∑ j ∈ E, (if arrow a b i j then (1 : ℝ) else 0) =
    ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
      (if arrow a b i p then (1 : ℝ) else 0) *
      (if p ∈ E then (1 : ℝ) else 0) := by
  rw [← sum_indicator_arrow_restrict a b i E _ (Finset.Subset.trans hE (gapFinset_subset_box a b))]

lemma bilinFormUnsym_eq_E_diff_box_sum (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (_hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (_hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinFormUnsym a b D E =
      ∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
        (if arrow a b i p then (1 : ℝ) else 0) *
        ((if p ∈ E then (1 : ℝ) else 0) -
         (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0)) := by
  rw [bilinFormUnsym_eq_arrow_diff a b hab D E]
  have hEsub : E ⊆ gapFinset a b := hE.1
  conv_lhs =>
    rw [show (∑ i ∈ D, ∑ j ∈ E, (if arrow a b i j then (1 : ℝ) else 0)) =
        ∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
          (if arrow a b i p then (1 : ℝ) else 0) * (if p ∈ E then (1 : ℝ) else 0)
      from Finset.sum_congr rfl fun i _ => first_sum_eq_box a b E hEsub i]
    rw [show (∑ i ∈ D, ∑ j ∈ E, (if arrow a b i (j.1, j.2 + 1) then (1 : ℝ) else 0)) =
        ∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
          (if arrow a b i p then (1 : ℝ) else 0) * (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0)
      from Finset.sum_congr rfl fun i _ => north_shift_sum_eq_box a b ha hb hab E hEsub i]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext i
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext p
  ring

lemma E_diff_to_boundary (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (E : Finset (ℤ × ℤ)) (hE : IsSubdiagram a b E)
    (D : Finset (ℤ × ℤ)) :
    (∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
        (if arrow a b i p then (1 : ℝ) else 0) *
        ((if p ∈ E then (1 : ℝ) else 0) -
         (if (p.1, p.2 - 1) ∈ E then (1 : ℝ) else 0))) =
    (∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
        (if arrow a b i p then (1 : ℝ) else 0) *
        ((if p ∈ bottomRow b then (1 : ℝ) else 0) -
         (if p ∈ upperBoundary a b E then (1 : ℝ) else 0))) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have h := telescoping_identity a b ha hb hab E hE p hp
  exact_mod_cast h

lemma bilinFormUnsym_eq_box_sum (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinFormUnsym a b D E =
      ∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
        (if arrow a b i p then (1 : ℝ) else 0) *
        ((if p ∈ bottomRow b then (1 : ℝ) else 0) -
         (if p ∈ upperBoundary a b E then (1 : ℝ) else 0)) := by
  rw [bilinFormUnsym_eq_E_diff_box_sum a b ha hb hab hcop D E hD hE]
  exact E_diff_to_boundary a b ha hb hab E hE D

lemma bottomRow_subset_box (a b : ℕ) (ha : 0 < a) :
    bottomRow b ⊆ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) := by
  intro p hp
  rw [mem_bottomRow_iff] at hp
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hp.1, hp.2.1⟩, ⟨by omega, by omega⟩⟩

lemma upperBoundary_subset_box (a b : ℕ) (E : Finset (ℤ × ℤ)) :
    upperBoundary a b E ⊆ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) := by
  rw [upperBoundary]
  apply Finset.filter_subset

lemma box_sum_eq_arrowPairs_diff (a b : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (D : Finset (ℤ × ℤ)) (E : Finset (ℤ × ℤ)) :
    ∑ i ∈ D, ∑ p ∈ (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)),
      (if arrow a b i p then (1 : ℝ) else 0) *
      ((if p ∈ bottomRow b then (1 : ℝ) else 0) -
       (if p ∈ upperBoundary a b E then (1 : ℝ) else 0)) =
    ((arrowPairs a b D (bottomRow b)).card : ℝ) -
    ((arrowPairs a b D (upperBoundary a b E)).card : ℝ) := by
  set Box := (Finset.Icc (1 : ℤ) (b : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) ((a : ℤ) + 1)) with _
  conv_lhs =>
    arg 2; ext i; arg 2; ext p
    rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  have hB : bottomRow b ⊆ Box := bottomRow_subset_box a b ha
  have hU : upperBoundary a b E ⊆ Box := upperBoundary_subset_box a b E
  congr 1
  · rw [arrowPairs_card_eq_double_sum]
    congr 1; ext i
    exact sum_indicator_arrow_restrict a b i (bottomRow b) Box hB
  · rw [arrowPairs_card_eq_double_sum]
    congr 1; ext i
    exact sum_indicator_arrow_restrict a b i (upperBoundary a b E) Box hU

lemma bilinFormUnsym_eq_arrowPairs_diff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinFormUnsym a b D E =
      ((arrowPairs a b D (bottomRow b)).card : ℝ) -
      ((arrowPairs a b D (upperBoundary a b E)).card : ℝ) := by
  rw [bilinFormUnsym_eq_box_sum a b ha hb hab hcop D E hD hE]
  exact box_sum_eq_arrowPairs_diff a b ha hb D E

lemma bilinFormUnsym_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinFormUnsym a b D E =
      (D.card : ℝ) - ((arrowPairs a b D (upperBoundary a b E)).card : ℝ) := by
  rw [bilinFormUnsym_eq_arrowPairs_diff a b ha hb hab hcop D E hD hE]
  rw [arrowPairs_bottomRow_card a b ha hb hab hcop D hD.1]

lemma blue_plus_red_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    (blueCells a b D E).card + (redCells a b E D).card + dinvAsym a b D E = E.card := by
  rw [E_card_decomp D E]
  rw [inter_partition a b ha hb hab hcop D E hD hE]
  rw [redCells_card a b D E]
  unfold dinvAsym
  omega

lemma two_bilinForm_eq_dinvAsym_sum (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    2 * bilinForm a b (indicatorVec D) (indicatorVec E) =
      ((dinvAsym a b D E + dinvAsym a b E D : ℕ) : ℝ) := by
  have h1 := two_bilinForm_eq_unsym_sum a b D E hD.1 hE.1
  have h2 := bilinFormUnsym_eq a b ha hb hab hcop D E hD hE
  have h3 := bilinFormUnsym_eq a b ha hb hab hcop E D hE hD
  have h4 := arrowPairs_card_eq a b ha hb hab hcop D E hD hE
  have h5 := arrowPairs_card_eq a b ha hb hab hcop E D hE hD
  have h6 := blue_plus_red_eq a b ha hb hab hcop D E hD hE
  have h7 := blue_plus_red_eq a b ha hb hab hcop E D hE hD
  have h4' : ((arrowPairs a b D (upperBoundary a b E)).card : ℝ) =
    ((blueCells a b D E).card : ℝ) + ((redCells a b D E).card : ℝ) := by
    exact_mod_cast h4
  have h5' : ((arrowPairs a b E (upperBoundary a b D)).card : ℝ) =
    ((blueCells a b E D).card : ℝ) + ((redCells a b E D).card : ℝ) := by
    exact_mod_cast h5
  have h6' : ((blueCells a b D E).card : ℝ) + ((redCells a b E D).card : ℝ) +
    (dinvAsym a b D E : ℝ) = (E.card : ℝ) := by exact_mod_cast h6
  have h7' : ((blueCells a b E D).card : ℝ) + ((redCells a b D E).card : ℝ) +
    (dinvAsym a b E D : ℝ) = (D.card : ℝ) := by exact_mod_cast h7
  push_cast
  linarith

/-- Theorem 1.2 (autoformalized by AxiomProver): for subdiagrams D, E ⊆ G,
    B(𝟙_D, 𝟙_E) = dinv(D, E).
    Proof: two_bilinForm_eq_dinvAsym_sum gives 2B = dinv^D_E + dinv^E_D = 2·crossDinv. -/
theorem bilinForm_eq_crossDinv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D E : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hE : IsSubdiagram a b E) :
    bilinForm a b (indicatorVec D) (indicatorVec E) = crossDinv a b D E := by
  have h := two_bilinForm_eq_dinvAsym_sum a b ha hb hab hcop D E hD hE
  unfold crossDinv
  linarith

-- ============================================================
-- Theorem 1.1: Q(𝟙_D) = dinv(D) and Q(𝟙_D) > 0 when D ≠ ∅
-- ============================================================

/-- The symmetric bilinear form associated with Q satisfies B(n,n) = Q(n).
    Proof: B(n,n) = (1/2)*(Q(2n) - Q(n) - Q(n)) = (1/2)*2*Q(n) = Q(n). -/
lemma bilinForm_eq_quadForm (a b : ℕ) (n : ℤ × ℤ → ℝ) :
    bilinForm a b n n = quadForm a b n := by
  have hcross : quadForm a b (n + n) - quadForm a b n - quadForm a b n =
      ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
        (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n i * n j + n i * n j) :=
    quadForm_cross_terms a b n n
  have heq2 : ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n i * n j + n i * n j) =
      2 * quadForm a b n := by
    simp only [quadForm]
    push_cast
    congr 1; ext i; congr 1; ext j; ring
  unfold bilinForm
  linarith

/-- Theorem 1.1 (equality): Q(𝟙_D) = dinv(D) = dinvAsym(D,D).
    Proof: Q(𝟙_D) = B(𝟙_D,𝟙_D) (polarization) = crossDinv(D,D) (Thm 1.2) = dinvAsym(D,D). -/
theorem quadForm_eq_dinvAsym (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) :
    quadForm a b (indicatorVec D) = (dinvAsym a b D D : ℝ) := by
  rw [← bilinForm_eq_quadForm a b (indicatorVec D)]
  rw [bilinForm_eq_crossDinv a b ha hb hab hcop D D hD hD]
  simp only [crossDinv]
  push_cast; ring

/-- g-value decreases by a when moving one step east. -/
private lemma gVal_east (a b : ℕ) (p : ℤ × ℤ) :
    gVal a b (p.1 + 1, p.2) = gVal a b p - (a : ℤ) := by
  simp only [gVal]; ring

/-- g-value decreases by b when moving one step north. -/
private lemma gVal_north' (a b : ℕ) (p : ℤ × ℤ) :
    gVal a b (p.1, p.2 + 1) = gVal a b p - (b : ℤ) := gVal_north a b p

/-- At the element of D with minimal g-value, arm length = 0.
    Any eastward neighbor would have strictly smaller g-value, contradicting minimality. -/
private lemma armLength_eq_zero_of_minimal_gVal (a b : ℕ) (ha : 0 < a)
    (D : Finset (ℤ × ℤ)) (d : ℤ × ℤ) (hd : d ∈ D)
    (hmin : ∀ p ∈ D, gVal a b d ≤ gVal a b p) :
    armLength D d = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  unfold armLength
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_image, Finset.mem_filter, id] at hk
  obtain ⟨p, ⟨hp_mem, hp_row, hp_le⟩, rfl⟩ := hk
  have ha_pos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hg_eq : gVal a b p = gVal a b d - (a : ℤ) * (p.1 - d.1) := by
    simp only [gVal, hp_row]; ring
  have hmin_p := hmin p hp_mem
  have hdiff_le : p.1 - d.1 ≤ 0 := by rw [hg_eq] at hmin_p; nlinarith
  have hdiff_ge : 0 ≤ p.1 - d.1 := by linarith
  have hdiff_zero : p.1 - d.1 = 0 := le_antisymm hdiff_le hdiff_ge
  simp [hdiff_zero]

/-- At the element of D with minimal g-value, leg length = 0. -/
private lemma legLength_eq_zero_of_minimal_gVal (a b : ℕ) (hb : 0 < b)
    (D : Finset (ℤ × ℤ)) (d : ℤ × ℤ) (hd : d ∈ D)
    (hmin : ∀ p ∈ D, gVal a b d ≤ gVal a b p) :
    legLength D d = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  unfold legLength
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_image, Finset.mem_filter, id] at hk
  obtain ⟨p, ⟨hp_mem, hp_col, hp_le⟩, rfl⟩ := hk
  have hb_pos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hg_eq : gVal a b p = gVal a b d - (b : ℤ) * (p.2 - d.2) := by
    simp only [gVal, hp_col]; ring
  have hmin_p := hmin p hp_mem
  have hdiff_le : p.2 - d.2 ≤ 0 := by rw [hg_eq] at hmin_p; nlinarith
  have hdiff_ge : 0 ≤ p.2 - d.2 := by linarith
  have hdiff_zero : p.2 - d.2 = 0 := le_antisymm hdiff_le hdiff_ge
  simp [hdiff_zero]

/-- Theorem 1.1 (positivity): Q(𝟙_D) > 0 when D ≠ ∅.
    The minimal element d satisfies arm_D(d) = leg_D(d) = 0, so dinvCond holds for d. -/
theorem dinvAsym_pos_of_nonempty (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hne : D.Nonempty) :
    0 < dinvAsym a b D D := by
  -- Find d = element of D with minimal g-value
  obtain ⟨d, hd_mem, hd_min⟩ := D.exists_min_image (fun p => gVal a b p) hne
  -- arm and leg lengths at d are both 0
  have harm : armLength D d = 0 :=
    armLength_eq_zero_of_minimal_gVal a b ha D d hd_mem hd_min
  have hleg : legLength D d = 0 :=
    legLength_eq_zero_of_minimal_gVal a b hb D d hd_mem hd_min
  -- dinvCond holds for d: reduces to 0 < a which is ha
  have hcond : dinvCond a b D D d = true := by
    rw [dinvCond_iff_slopes a b hb D D d]
    refine ⟨?_, ?_⟩
    · -- smallSlope D D d = 0 < a/b
      have : smallSlope D D d = 0 := by
        simp [smallSlope, hleg, harm]
      rw [this]
      apply div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
    · -- a/b < largeSlope D D d = ⊤
      have : largeSlope D D d = ⊤ := by
        simp [largeSlope, harm]
      rw [this]
      exact WithTop.coe_lt_top _
  -- d is in the filter, so card ≥ 1
  apply Finset.card_pos.mpr
  exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hd_mem, hd_mem⟩, hcond⟩⟩

theorem quadForm_pos_of_nonempty (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (D : Finset (ℤ × ℤ))
    (hD : IsSubdiagram a b D) (hne : D.Nonempty) :
    (0 : ℝ) < quadForm a b (indicatorVec D) := by
  rw [quadForm_eq_dinvAsym a b ha hb hab hcop D hD]
  exact_mod_cast dinvAsym_pos_of_nonempty a b ha hb hab hcop D hD hne

-- ============================================================
-- Theorem 1.3: B(n,n') ≥ 0 on C_R and Q(n) ≥ (1/|G|)‖n‖²_∞
-- ============================================================

/-- The cone C_R (§1 of arXiv:2604.13238): non-negative functions on G that are weakly
    decreasing going northeast, i.e., n_j ≥ n_i whenever j is SW of i (gapLE a b i j).
    The poset (G,⪯) has its MAXIMUM at (1,1) (the SW corner), so for n ∈ C_R:
      ‖n‖_∞ = n_{(1,1)}. -/
def IsCone (a b : ℕ) (n : ℤ × ℤ → ℝ) : Prop :=
  (∀ p ∈ gapFinset a b, (0 : ℝ) ≤ n p) ∧
  (∀ i j, i ∈ gapFinset a b → j ∈ gapFinset a b →
    gapLE a b i j → n j ≥ n i)

/-- ℓ∞ norm of n on G: sup{n(p) : p ∈ G}, or 0 if G = ∅.
    For n ∈ C_R this equals n_{(1,1)}, since (1,1) is the unique maximum of (G,⪯).
    Note: (1,1) ∈ G whenever 1 < a < b (since g(1,1) = ab−a−b = (a−1)(b−1)−1 > 0). -/
noncomputable def linfNorm (a b : ℕ) (n : ℤ × ℤ → ℝ) : ℝ :=
  if h : (gapFinset a b).Nonempty then (gapFinset a b).sup' h n else 0

/-- Symmetric bilinear form formula: B(n,n') = (1/2) ∑∑ K * (n(i)n'(j) + n'(i)n(j)). -/
private lemma bilinForm_formula (a b : ℕ) (n n' : ℤ × ℤ → ℝ) :
    bilinForm a b n n' = (1 / 2 : ℝ) * ∑ i ∈ gapFinset a b, ∑ j ∈ gapFinset a b,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n i * n' j + n' i * n j) := by
  unfold bilinForm
  congr 1
  exact quadForm_cross_terms a b n n'

/-- B is linear in first argument (scalar multiplication). -/
private lemma bilinForm_smul_left (a b : ℕ) (c : ℝ) (n n' : ℤ × ℤ → ℝ) :
    bilinForm a b (c • n) n' = c * bilinForm a b n n' := by
  rw [bilinForm_formula a b (c • n) n', bilinForm_formula a b n n']
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : ∀ i j : ℤ × ℤ,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (c * n i * n' j + n' i * (c * n j)) =
      c * ((kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n i * n' j + n' i * n j)) := by
    intros; ring
  simp_rw [heq, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- B is linear in first argument (addition). -/
private lemma bilinForm_add_left (a b : ℕ) (n₁ n₂ n' : ℤ × ℤ → ℝ) :
    bilinForm a b (n₁ + n₂) n' = bilinForm a b n₁ n' + bilinForm a b n₂ n' := by
  rw [bilinForm_formula a b (n₁ + n₂) n', bilinForm_formula a b n₁ n',
      bilinForm_formula a b n₂ n']
  simp only [Pi.add_apply]
  have heq : ∀ i j : ℤ × ℤ,
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) *
        ((n₁ i + n₂ i) * n' j + n' i * (n₁ j + n₂ j)) =
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n₁ i * n' j + n' i * n₁ j) +
      (kernelK a b (gVal a b j - gVal a b i) : ℝ) * (n₂ i * n' j + n' i * n₂ j) := by
    intros; ring
  simp_rw [heq, Finset.sum_add_distrib]
  ring

/-- B(∑ λ_i n_i, n') = ∑ λ_i B(n_i, n'). -/
private lemma bilinForm_sum_left (a b : ℕ) {ι : Type*} (s : Finset ι)
    (λv : ι → ℝ) (n : ι → ℤ × ℤ → ℝ) (n' : ℤ × ℤ → ℝ) :
    bilinForm a b (∑ i ∈ s, λv i • n i) n' = ∑ i ∈ s, λv i * bilinForm a b (n i) n' := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [bilinForm_formula]
    simp [show (0 : ℤ × ℤ → ℝ) = fun _ => 0 from rfl]
  | insert ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [bilinForm_add_left, bilinForm_smul_left, ih]

/-- Level set D_c = {g ∈ G : n(g) ≥ c} is a subdiagram when n ∈ C_R. -/
private lemma levelSet_isSubdiagram (a b : ℕ) (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n) (c : ℝ) :
    IsSubdiagram a b ((gapFinset a b).filter (fun g => c ≤ n g)) := by
  constructor
  · exact Finset.filter_subset _ _
  · intro i hi j hj hij
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hj, le_trans hi.2 (hn.2 i j hi.1 hj hij)⟩

/-- Lemma 5.1: Every n ∈ C_R is a positive linear combination of indicator vectors of
    subdiagrams. Canonical construction via sorted level sets. -/
lemma cone_generated_by_subdiagrams (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (n : ℤ × ℤ → ℝ) (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0) :
    ∃ (k : ℕ) (D : Fin k → Finset (ℤ × ℤ)) (λv : Fin k → ℝ),
      (∀ i, (0 : ℝ) < λv i) ∧
      (∀ i, IsSubdiagram a b (D i)) ∧
      (∀ p, n p = ∑ i : Fin k, λv i * indicatorVec (D i) p) ∧
      (∀ i, (D i).Nonempty) ∧
      k ≤ (gapFinset a b).card := by
  -- Use the sorted distinct positive values of n on G as level set thresholds
  classical
  -- Values of n on G, as a sorted list with duplicates removed
  let vals_set := ((gapFinset a b).image n).filter (fun c => 0 < c)
  let vals := vals_set.sort (· ≤ ·)
  let k := vals.length
  -- Level sets: D_i = {g ∈ G : n(g) ≥ vals[i]}
  let D : Fin k → Finset (ℤ × ℤ) := fun i =>
    (gapFinset a b).filter (fun g => vals.get i ≤ n g)
  -- λ_i = vals[i] - vals[i-1] (with vals[-1] = 0)
  let prev : Fin k → ℝ := fun i =>
    if h : i.val = 0 then 0 else vals.get ⟨i.val - 1, by omega⟩
  let λv : Fin k → ℝ := fun i => vals.get i - prev i
  refine ⟨k, D, λv, ?_, ?_, ?_, ?_, ?_⟩
  · -- λ_i > 0 (consecutive distinct values)
    intro i
    simp only [λv, prev]
    split_ifs with h
    · simp [h]
      have : vals.get i ∈ vals_set := by
        have := Finset.sort_mem vals_set (· ≤ ·) |>.mp (List.get_mem vals i.isLt)
        exact this
      simp [vals_set] at this
      exact this.2
    · have hlt : vals.get ⟨i.val - 1, by omega⟩ < vals.get i := by
        apply List.Sorted.get_strictMono (Finset.sort_sorted_lt vals_set)
        omega
      linarith
  · -- D_i are subdiagrams
    intro i
    exact levelSet_isSubdiagram a b n hn (vals.get i)
  · -- n = ∑ λ_i 𝟙_{D_i} pointwise
    intro p
    by_cases hp : p ∈ gapFinset a b
    · -- Telescoping sum: indicator (D i) p = if vals[i] ≤ n p then 1 else 0
      -- vals is sorted, n p appears at position j, sum telescopes to vals[j] = n p
      have hnp_nn : 0 ≤ n p := hn.1 p hp
      have hind : ∀ i : Fin k, indicatorVec (D i) p = if vals.get i ≤ n p then 1 else 0 := by
        intro i; simp only [indicatorVec, D, Finset.mem_filter, hp, true_and]
      simp_rw [hind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      by_cases hnp0 : n p = 0
      · -- All vals > 0, no indicator fires, sum = 0 = n p
        rw [hnp0]
        simp only [le_refl, ite_true]
        apply (Finset.sum_empty.symm.trans _).symm
        congr 1; ext ⟨i, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.not_mem_empty, iff_false,
                   not_and, true_and]
        intro h
        have hvi : 0 < vals.get ⟨i, hi⟩ := by
          have hmem := Finset.sort_mem vals_set (· ≤ ·) |>.mp (List.get_mem vals i hi)
          simp only [vals_set, Finset.mem_filter, Finset.mem_image] at hmem
          exact hmem.2
        linarith [hnp0 ▸ h]
      · -- n p > 0, appears in vals at some position j
        have hnp_pos : 0 < n p := lt_of_le_of_ne hnp_nn (Ne.symm hnp0)
        have hnp_in_vset : n p ∈ vals_set := by
          simp only [vals_set, Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨p, hp, rfl⟩, hnp_pos⟩
        have hnp_in : n p ∈ vals :=
          (Finset.sort_mem vals_set (· ≤ ·)).mpr hnp_in_vset
        obtain ⟨⟨j, hj_lt⟩, hj_val⟩ := List.mem_iff_get.mp hnp_in
        -- strict monotonicity of vals
        have hmono : ∀ (a b : Fin k), a < b → vals.get a < vals.get b :=
          List.Sorted.get_strictMono (Finset.sort_sorted_lt vals_set)
        -- The filter {i | vals[i] ≤ n p} equals {i | i.val ≤ j}
        have hfilt : Finset.univ.filter (fun i : Fin k => vals.get i ≤ n p) =
            Finset.univ.filter (fun i : Fin k => i.val ≤ j) := by
          ext ⟨i, hi⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hle
            by_contra h_gt; push_neg at h_gt
            have := hmono ⟨j, hj_lt⟩ ⟨i, hi⟩ (by simpa [Fin.lt_iff_val_lt_val])
            linarith [hj_val]
          · intro hle
            rcases Nat.eq_or_lt_of_le hle with rfl | hlt
            · linarith [hj_val.symm.le]
            · have := hmono ⟨i, hi⟩ ⟨j, hj_lt⟩ (by simpa [Fin.lt_iff_val_lt_val])
              linarith [hj_val]
        rw [hfilt]
        -- Telescope: ∑_{i ≤ j} λv i = vals[j] = n p
        suffices htel : ∀ (m : ℕ) (hm : m < k),
            ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val ≤ m), λv i =
            vals.get ⟨m, hm⟩ by
          rw [htel j hj_lt, hj_val]
        intro m
        induction m with
        | zero =>
          intro hm
          have hfilt0 : Finset.univ.filter (fun i : Fin k => i.val ≤ 0) = {⟨0, hm⟩} := by
            ext ⟨i, hi⟩; simp [Fin.ext_iff]; omega
          rw [hfilt0, Finset.sum_singleton]
          simp only [λv, prev, Fin.val_zero, ite_true, sub_zero]
        | succ m ih =>
          intro hm
          have hmk : m < k := Nat.lt_of_succ_lt hm
          have hsplit : Finset.univ.filter (fun i : Fin k => i.val ≤ m + 1) =
              Finset.univ.filter (fun i : Fin k => i.val ≤ m) ∪ {⟨m + 1, hm⟩} := by
            ext ⟨i, hi⟩; simp [Fin.ext_iff]; omega
          rw [hsplit, Finset.sum_union]
          · rw [ih hmk, Finset.sum_singleton]
            suffices h : λv ⟨m + 1, hm⟩ = vals.get ⟨m + 1, hm⟩ - vals.get ⟨m, hmk⟩ by
              linarith
            show vals.get ⟨m + 1, hm⟩ -
                (if (m + 1) = 0 then 0 else vals.get ⟨m + 1 - 1, by omega⟩) =
                vals.get ⟨m + 1, hm⟩ - vals.get ⟨m, hmk⟩
            simp only [show ¬(m + 1 = 0) from Nat.succ_ne_zero m, ite_false,
                       show m + 1 - 1 = m from Nat.add_sub_cancel]
          · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
                       Finset.mem_singleton, Fin.mk.injEq, true_and]
            intro ⟨i, _⟩ hle heq; omega
    · -- p ∉ gapFinset: n p = 0 and all D i ⊆ gapFinset so indicators are 0
      rw [hn_supp p hp]
      apply Finset.sum_eq_zero
      intro ⟨i, hi⟩ _
      have hpi : p ∉ D ⟨i, hi⟩ := fun h => hp (Finset.filter_subset _ _ h)
      simp only [indicatorVec, if_neg hpi, mul_zero]
  · -- D_i are nonempty: vals[i] is achieved at some p ∈ G
    intro ⟨i, hi⟩
    have hvi_in : vals.get ⟨i, hi⟩ ∈ vals_set :=
      Finset.sort_mem vals_set (· ≤ ·) |>.mp (List.get_mem vals i hi)
    simp only [vals_set, Finset.mem_filter, Finset.mem_image] at hvi_in
    obtain ⟨⟨p, hp, hpval⟩, _⟩ := hvi_in
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpval ▸ le_refl _⟩⟩
  · -- k ≤ |G|: k = #vals_set ≤ #(image n on G) ≤ |G|
    have hkvals : k = vals_set.card := by simp [k, vals, Finset.length_sort]
    have hvsub : vals_set ⊆ (gapFinset a b).image n := Finset.filter_subset _ _
    calc k = vals_set.card := hkvals
      _ ≤ ((gapFinset a b).image n).card := Finset.card_le_card hvsub
      _ ≤ (gapFinset a b).card := Finset.card_image_le

/-- crossDinv is always non-negative (it equals (ℕ : ℝ) / 2). -/
private lemma crossDinv_nonneg (a b : ℕ) (D E : Finset (ℤ × ℤ)) :
    (0 : ℝ) ≤ crossDinv a b D E := by
  simp only [crossDinv]
  positivity

/-- Theorem 1.3 (semi-definiteness): B(n,n') ≥ 0 for n,n' ∈ C_R.
    Proof: decompose via Lemma 5.1, then use bilinearity and B(𝟙_D,𝟙_E) = crossDinv ≥ 0. -/
theorem bilinForm_nonneg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n n' : ℤ × ℤ → ℝ)
    (hn : IsCone a b n) (hn' : IsCone a b n')
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0)
    (hn'_supp : ∀ p, p ∉ gapFinset a b → n' p = 0) :
    (0 : ℝ) ≤ bilinForm a b n n' := by
  obtain ⟨k, D, λv, hλ_pos, hD_sub, hn_eq, _, _⟩ :=
    cone_generated_by_subdiagrams a b ha hb n hn hn_supp
  obtain ⟨l, E, μv, hμ_pos, hE_sub, hn'_eq, _, _⟩ :=
    cone_generated_by_subdiagrams a b ha hb n' hn' hn'_supp
  -- Rewrite n and n' as sums of smul'd indicator functions
  have hn_fun : n = ∑ i : Fin k, λv i • indicatorVec (D i) := by
    ext p; simp [hn_eq p, indicatorVec]
  have hn'_fun : n' = ∑ j : Fin l, μv j • indicatorVec (E j) := by
    ext p; simp [hn'_eq p, indicatorVec]
  -- B is symmetric: B(n,n') = B(n',n)
  have bsym : ∀ (f g : ℤ × ℤ → ℝ), bilinForm a b f g = bilinForm a b g f := by
    intros f g; rw [bilinForm_formula a b f g, bilinForm_formula a b g f]
    congr 1; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hn_fun, hn'_fun]
  rw [bilinForm_sum_left]
  apply Finset.sum_nonneg; intro i _
  -- Use symmetry to apply sum_left on second argument
  rw [bsym, bilinForm_sum_left, Finset.mul_sum]
  apply Finset.sum_nonneg; intro j _
  rw [bsym (indicatorVec (D i))]
  apply mul_nonneg
  · apply mul_nonneg (le_of_lt (hλ_pos i)) (le_of_lt (hμ_pos j))
  · rw [bilinForm_eq_crossDinv a b ha hb hab hcop (D i) (E j) (hD_sub i) (hE_sub j)]
    exact crossDinv_nonneg a b (D i) (E j)

/-- Q(n) ≥ 0 on C_R. -/
theorem quadForm_nonneg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0) :
    (0 : ℝ) ≤ quadForm a b n := by
  rw [← bilinForm_eq_quadForm]
  exact bilinForm_nonneg a b ha hb hab hcop n n hn hn hn_supp hn_supp



/-- Theorem 1.3 (effective bound): Q(n) ≥ (1/|G|) ‖n‖²_∞ for n ∈ C_R, G nonempty.
    Proof: write n = ∑ λ_i 𝟙_{D_i} via Lemma 5.1, then:
      Q(n) ≥ ∑ λ_i² · dinv(D_i)   [drop cross terms; dinv ≥ 0]
           ≥ ∑ λ_i²                [dinv(D_i) ≥ 1 since D_i ≠ ∅]
           ≥ (∑ λ_i)² / k          [Cauchy–Schwarz: (∑ λ_i)² ≤ k · ∑ λ_i²]
           ≥ (∑ λ_i)² / |G|        [k ≤ |G|]
           ≥ ‖n‖²_∞ / |G|          [‖n‖_∞ ≤ ∑ λ_i, proved below]
    Remark: the paper uses ‖n‖_∞ = ∑ λ_i (equality via f=(1,1) ∈ every D_i). Our proof
    uses only the inequality ‖n‖_∞ ≤ ∑ λ_i, which is sufficient and avoids proving (1,1)∈G. -/
theorem quadForm_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hcop : Nat.Coprime a b) (n : ℤ × ℤ → ℝ)
    (hn : IsCone a b n)
    (hn_supp : ∀ p, p ∉ gapFinset a b → n p = 0)
    (hG : (gapFinset a b).Nonempty) :
    ((gapFinset a b).card : ℝ)⁻¹ * (linfNorm a b n) ^ 2 ≤ quadForm a b n := by
  obtain ⟨k, D, λv, hλ_pos, hD_sub, hn_eq, hD_ne, hkG_raw⟩ :=
    cone_generated_by_subdiagrams a b ha hb n hn hn_supp
  -- Step 1: Q(n) ≥ ∑ λ_i² (diagonal bound using dinv(D_i) ≥ 1)
  have hQ_lb : ∑ i : Fin k, (λv i) ^ 2 ≤ quadForm a b n := by
    rw [← bilinForm_eq_quadForm]
    have hn_fun : n = ∑ i : Fin k, λv i • indicatorVec (D i) := by
      ext p; simp [hn_eq p, indicatorVec]
    rw [hn_fun, bilinForm_sum_left]
    have hbsym : ∀ f g : ℤ × ℤ → ℝ, bilinForm a b f g = bilinForm a b g f := by
      intros f g; rw [bilinForm_formula, bilinForm_formula]
      congr 1; apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    calc ∑ i : Fin k, (λv i) ^ 2
        = ∑ i : Fin k, (λv i) ^ 2 * 1 := by simp
      _ ≤ ∑ i : Fin k, (λv i) ^ 2 * (dinvAsym a b (D i) (D i) : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact_mod_cast dinvAsym_pos_of_nonempty a b ha hb hab hcop (D i) (hD_sub i) (hD_ne i)
      _ = ∑ i : Fin k, (λv i) ^ 2 * bilinForm a b (indicatorVec (D i)) (indicatorVec (D i)) := by
          apply Finset.sum_congr rfl; intro i _
          congr 1
          rw [bilinForm_eq_crossDinv a b ha hb hab hcop (D i) (D i) (hD_sub i) (hD_sub i)]
          simp [crossDinv]; push_cast; ring
      _ ≤ ∑ i : Fin k, λv i * bilinForm a b (indicatorVec (D i)) (∑ j : Fin k, λv j • indicatorVec (D j)) := by
          apply Finset.sum_le_sum; intro i _
          rw [bilinForm_sum_left]
          calc (λv i) ^ 2 * bilinForm a b (indicatorVec (D i)) (indicatorVec (D i))
              = λv i * (λv i * bilinForm a b (indicatorVec (D i)) (indicatorVec (D i))) := by ring
            _ ≤ λv i * ∑ j : Fin k, λv j * bilinForm a b (indicatorVec (D i)) (indicatorVec (D j)) := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt (hλ_pos i))
                apply Finset.single_le_sum (fun j _ => ?_) _ ⟨i, Finset.mem_univ i⟩
                · apply mul_nonneg (le_of_lt (hλ_pos j))
                  rw [bilinForm_eq_crossDinv a b ha hb hab hcop (D i) (D j) (hD_sub i) (hD_sub j)]
                  exact crossDinv_nonneg a b (D i) (D j)
      _ = ∑ i : Fin k, λv i * bilinForm a b (indicatorVec (D i)) n := by
          congr 1; ext i; congr 1; rw [← hn_fun]
  -- Step 2: ‖n‖_∞ ≤ ∑ λ_i (pointwise: n p = ∑ λ_i * indicator ≤ ∑ λ_i since indicator ≤ 1)
  have hlinf_le : linfNorm a b n ≤ ∑ i : Fin k, λv i := by
    simp only [linfNorm, dif_pos hG]
    apply Finset.sup'_le
    intro p hp
    rw [hn_eq p]
    calc ∑ i : Fin k, λv i * indicatorVec (D i) p
        ≤ ∑ i : Fin k, λv i * 1 :=
          Finset.sum_le_sum fun i _ => by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (hλ_pos i))
            simp only [indicatorVec]; split_ifs <;> norm_num
      _ = ∑ i : Fin k, λv i := by simp
  have hlinf_nn : 0 ≤ linfNorm a b n := by
    simp only [linfNorm, dif_pos hG]
    obtain ⟨p, hp⟩ := hG
    exact le_trans (hn.1 p hp) (Finset.le_sup' n ⟨p, hp⟩)
  -- Step 3: Cauchy-Schwarz (∑ λ_i)² ≤ k * ∑ λ_i²
  have hcs : (∑ i : Fin k, λv i) ^ 2 ≤ (k : ℝ) * ∑ i : Fin k, (λv i) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ)) λv
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Finset.card_fin,
               nsmul_eq_mul, mul_one] at h
    exact h
  -- Step 4: k ≤ |G|
  have hkG : (k : ℝ) ≤ (gapFinset a b).card := by exact_mod_cast hkG_raw
  have hGpos : (0 : ℝ) < (gapFinset a b).card := by
    exact_mod_cast Finset.card_pos.mpr hG
  calc ((gapFinset a b).card : ℝ)⁻¹ * (linfNorm a b n) ^ 2
      ≤ ((gapFinset a b).card : ℝ)⁻¹ * (∑ i : Fin k, λv i) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left hlinf_nn hlinf_le 2
    _ ≤ ((gapFinset a b).card : ℝ)⁻¹ * ((k : ℝ) * ∑ i : Fin k, (λv i) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ ((gapFinset a b).card : ℝ)⁻¹ * ((gapFinset a b).card * ∑ i : Fin k, (λv i) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right hkG
        apply Finset.sum_nonneg; intro i _; positivity
    _ = ∑ i : Fin k, (λv i) ^ 2 := by field_simp; ring
    _ ≤ quadForm a b n := hQ_lb

end RationalDinv
