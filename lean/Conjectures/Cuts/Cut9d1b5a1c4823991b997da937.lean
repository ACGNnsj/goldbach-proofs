import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 粗糙窗内素数或半素数点集占全窗点数的比例有一致正常数下界（筛法硬核）。
-- child 1 en: The prime-or-semiprime points in the rough window carry a uniform positive proportion of the window (the sieve core).
-- child 2 zh: 有限集上，好子集占比例至少 c 则其补集点数至多占 1-c（初等计数）。
-- child 2 en: On a finite set, if a good subset holds proportion at least c then its complement holds at most 1-c (elementary counting).

theorem Conjectures.Cuts.Cut9d1b5a1c4823991b997da937
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      c * ↑({x ∈ Finset.range (X + (1 : ℕ)) | (1 : ℕ) < x ∧ Nat.Prime (x + (2 : ℕ)) ∧ ∀ d ∈ x.divisors, Nat.Prime d → X ≤ d ^ (10 : ℕ)}).card ≤
        ↑({x ∈ {x ∈ Finset.range (X + (1 : ℕ)) | (1 : ℕ) < x ∧ Nat.Prime (x + (2 : ℕ)) ∧ ∀ d ∈ x.divisors, Nat.Prime d → X ≤ d ^ (10 : ℕ)} |
          Nat.Prime x ∨ ∃ x3 ∈ x.divisors, Nat.Prime x3 ∧ Nat.Prime (x / x3) ∧ x3 ≠ x / x3}).card)
    (h₂ : ∀ (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p], ∀ c : ℝ, 0 < c →
      c * ↑s.card ≤ ↑(s.filter p).card → ↑(s.filter (fun x => ¬ p x)).card ≤ ((1 : ℝ) - c) * ↑s.card) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}; let x2 : ℕ → Prop := fun (x2 : ℕ) => Nat.Prime x2 ∨ ∃ x3 ∈ x2.divisors, Nat.Prime x3 ∧ Nat.Prime (x2 / x3) ∧ x3 ≠ x2 / x3; ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → ↑{x7 ∈ x1 x5 | ¬x2 x7}.card ≤ ((1 : ℝ) - x3) * ↑(x1 x5).card) := by
  obtain ⟨c, hc, N, hN⟩ := h₁
  refine ⟨c, hc, N, fun X hX => ?_⟩
  exact h₂ _ _ c hc (hN X hX)
