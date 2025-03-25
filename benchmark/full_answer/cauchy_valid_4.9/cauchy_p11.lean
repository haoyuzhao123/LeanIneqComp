import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p11 (x y z: ℝ) (h : x^2 + 2 * y^2 + 4 * z^2 > 0) : (x + y + z)^2 / (x^2 + 2 * y^2 + 4 * z^2) ≤ 7 / 4 := by
  have h1 : (x^2 + 2 * y^2 + 4 * z^2) * (1 + 1/2 + 1/4) ≥ (x + y + z)^2 := by
    convert_to (∑ i : Fin 3, (![x, √2 * y, 2 * z] i)^2) *
            (∑ i : Fin 3, (![1, 1 / √2, 1 / √4] i)^2) ≥
            (∑ i : Fin 3, ![x, √2 * y, 2 * z] i * ![1, 1 / √2, 1 / √4] i)^2
    simp [Fin.sum_univ_three]
    left; ring_nf; simp
    simp [Fin.sum_univ_three]
    have h11 : √4 = 2 := by
      have h10 : √4 = √(2^2) := by norm_num
      rw [h10, Real.sqrt_sq]
      norm_num
    ring_nf; simp [h11]; ring
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [mul_comm] at h1
  rw [div_le_iff]
  linarith
  exact h
