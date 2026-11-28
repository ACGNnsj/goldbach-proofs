import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 二元区间孪生素数计数满足一致的线性对数下界（解析硬核）。
-- child 1 en: The dyadic twin-prime count admits a uniform linearithmic lower bound (the analytic core).
-- child 2 zh: 区间非退化时，加权因子恒为正（初等正性）。
-- child 2 en: The weight factor stays positive on non-degenerate intervals (elementary positivity).

theorem Conjectures.Cuts.Cut622cb42ca9a08c134eafdcd6
    (h₁ : ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      K * (√((2 : ℝ) * ↑X) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑X)) ≤
        ↑{x4 ∈ Finset.Ioc X ((2 : ℕ) * X) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card)
    (h₂ : ∀ X : ℕ, 1 ≤ X → 0 < √((2 : ℝ) * ↑X) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑X)) :
    (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * (√((2 : ℝ) * ↑x3) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x3)) < ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  intro x1 x2
  have hK0 : (0 : ℝ) < max x1 0 + 1 := by
    have h := le_max_right x1 (0 : ℝ)
    linarith
  obtain ⟨N, hN⟩ := h₁ (max x1 0 + 1) hK0
  refine ⟨max x2 N + 1, by omega, ?_⟩
  have hX1 : N ≤ max x2 N + 1 := by omega
  have hXge1 : 1 ≤ max x2 N + 1 := by omega
  have h1X := hN _ hX1
  have hfX := h₂ _ hXge1
  have hx : x1 ≤ max x1 0 + 1 - 1 := by
    have h := le_max_left x1 (0 : ℝ)
    linarith
  have e1 : x1 * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) ≤
      (max x1 0 + 1 - 1) * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) :=
    mul_le_mul_of_nonneg_right hx (le_of_lt hfX)
  have e2 : (max x1 0 + 1 - 1) * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) =
      (max x1 0 + 1) * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) -
        (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) := by ring
  have e3 : (max x1 0 + 1) * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) -
        (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) <
      (max x1 0 + 1) * (√((2 : ℝ) * ↑(max x2 N + 1)) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑(max x2 N + 1))) := by
    linarith [hfX]
  linarith [e1, e2, e3, h1X]
