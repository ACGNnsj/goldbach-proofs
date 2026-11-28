import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 严格窗内孪生素数对数权质量满足一致的线性对数下界（解析硬核）。
-- child 1 en: The log-weighted twin-prime mass in strict windows admits a uniform linearithmic lower bound (the analytic core).
-- child 2 zh: 对任意正常数，充分大的 X 满足 X·log X 控制 X 的常数倍。
-- child 2 en: For any positive constant, X·log X dominates a constant multiple of X for all large X.

theorem Conjectures.Cuts.Cut0a8814e50293f623a10af437
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      c * ↑X * Real.log ↑X ≤
        ∑ n ∈ Finset.range ((2 : ℕ) * X + (1 : ℕ)),
          if X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X ∧ Nat.Prime n ∧ Nat.Prime (n + (2 : ℕ)) then Real.log ↑n * Real.log ↑(n + (2 : ℕ)) else (0 : ℝ))
    (h₂ : ∀ c : ℝ, 0 < c → ∃ c' : ℝ, 0 < c' ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      c' * ↑X ≤ c * ↑X * Real.log ↑X) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)), if x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ)) := by
  obtain ⟨c, hc, N1, hN1⟩ := h₁
  obtain ⟨c', hc', N2, hN2⟩ := h₂ c hc
  refine ⟨c', hc', fun B => ?_⟩
  refine ⟨max B (max N1 N2) + 1, by omega, ?_⟩
  have g1 := hN2 (max B (max N1 N2) + 1) (by omega)
  have g2 := hN1 (max B (max N1 N2) + 1) (by omega)
  exact le_trans g1 g2
