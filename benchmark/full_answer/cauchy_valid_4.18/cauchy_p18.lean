import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p18 (n : ℕ) (hn : n > 2) (a : Fin n → ℝ) (ha1 : ∀ i, a i < 1) (ha2 : ∀ i, a i ≥ 0) (hs : ∑ i : Fin n, a i = n - 2) : ∑ i : Fin n, ((a i)^2 / (1 - a i)) ≥ ((n : ℝ) - 2)^2 / 2 := by
  have h1 : (∑ i : Fin n, ((a i)^2 / (1 - a i))) * (∑ i : Fin n, (1 - a i)) ≥ (∑ i : Fin n, a i)^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    exact div_nonneg (sq_nonneg _) (by linarith [ha1 i])
    intro i _
    linarith [ha1 i]
    intro i _
    rw [div_mul, div_self, div_one]
    linarith [ha1 i]
  rw [hs] at h1
  have h2 : ∑ i : Fin n, (1 - a i) = 2 := by
    rw [Finset.sum_sub_distrib]
    rw [hs]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  nlinarith
