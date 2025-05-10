import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p18 (n : ℕ) (hn : n > 2) (a : Fin n → ℝ) (ha1 : ∀ i, a i < 1) (ha2 : ∀ i, a i ≥ 0) (hs : ∑ i : Fin n, a i = n - 2) : ∑ i : Fin n, ((a i)^2 / (1 - a i)) ≥ ((n : ℝ) - 2)^2 / 2 := by
  have h1 : (∑ i : Fin n, ((a i)^2 / (1 - a i))) * (∑ i : Fin n, (1 - a i)) ≥ (∑ i : Fin n, a i)^2 := by
    convert_to (∑ i : Fin n, ((a i) / √(1 - a i))^2) * (∑ i : Fin n, (√(1 - a i))^2) ≥ (∑ i : Fin n, (a i) / √(1 - a i) * √(1 - a i))^2

    have g1 : (∑ i : Fin n, ((a i)^2 / (1 - a i))) * (∑ i : Fin n, (1 - a i)) = (∑ i : Fin n, ((a i) / √(1 - a i))^2) * (∑ i : Fin n, (√(1 - a i))^2) := by
      congr! with i1 _ i2 _
      rw [div_pow, sq_sqrt]
      linarith [ha1 i1]
      rw [sq_sqrt]
      linarith [ha1 i2]
    exact g1

    have g2 : (∑ i : Fin n, a i)^2 = (∑ i : Fin n, (a i) / √(1 - a i) * √(1 - a i))^2 := by
      congr! with i
      rw [div_mul, div_self, div_one]
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [ha1 i]))
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [hs] at h1
  have h2 : ∑ i : Fin n, (1 - a i) = 2 := by
    rw [Finset.sum_sub_distrib]
    rw [hs]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  nlinarith
