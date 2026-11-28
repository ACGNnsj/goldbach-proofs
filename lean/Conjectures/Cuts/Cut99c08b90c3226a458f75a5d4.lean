import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss

-- child 1 zh: 放宽互补条件的超集表示数仍受 23/50 主项控制（筛法硬核）。
-- child 1 en: The superset representation count with the relaxed complement condition stays under the 23/50 main term (the sieve core).
-- child 2 zh: 有限集上，子集的表示数不超过超集的表示数（初等单调性）。
-- child 2 en: On finite sets, the representation count over a subset is at most that over a superset (elementary monotonicity).

theorem Conjectures.Cuts.Cut99c08b90c3226a458f75a5d4
    (h₁ : ∃ N : ℕ, ∀ X : ℕ, N ≤ X → Even X →
      ↑({x9 ∈ {x4 ∈ Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ)) | ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)} |
        X - x9 ∈ Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ))}).card ≤
        (23 / 50 : ℝ) * ((↑(Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ))).card : ℝ) * (↑X.totient : ℝ) / (↑X : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) X.sqrt) with ¬x5 ∣ X, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ))))
    (h₂ : ∀ (s w : Finset ℕ), s ⊆ w → ∀ X : ℕ,
      (↑(({x9 ∈ s | X - x9 ∈ s}).card) : ℝ) ≤ (↑(({x9 ∈ s | X - x9 ∈ w}).card) : ℝ)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑{x9 ∈ x3 x6 | x6 - x9 ∈ x3 x6}.card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  obtain ⟨N, hN⟩ := h₁
  refine ⟨N, fun X hNX hEven => ?_⟩
  have hsub : {x ∈ Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ)) | ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x.minFac ∧ Nat.Prime x.minFac ∧ Nat.Prime (x / x.minFac)} ⊆
      Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ)) :=
    fun x hx => (Finset.mem_filter.mp hx).1
  have hN' := hN X hNX hEven
  beta_reduce
  exact le_trans
    (h₂ {x ∈ Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ)) | ⌊(↑X : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x.minFac ∧ Nat.Prime x.minFac ∧ Nat.Prime (x / x.minFac)}
      (Finset.Icc ((X + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * X / (3 : ℕ))) hsub X)
    hN'
