import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p17 (a b c d e : ℝ) (h : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - e)^2 = 1) : a - 2 * b - c + 2 * e ≤ √10 := by
  let x := a - b
  let y := b - c
  let z := c - d
  let w := d - e
  have h0 : x^2 + y^2 + z^2 + w^2 = 1 := h
  have h1 : a - 2 * b - c + 2 * e = x - y - 2 * z - 2 * w := by ring
  have h2 : (x^2 + y^2 + z^2 + w^2) * 10 ≥ (x - y - 2 * z - 2 * w)^2 := by
    convert_to (∑ i : Fin 4, (![x^2, y^2, z^2, w^2] i)) *
            (∑ i : Fin 4, (![1^2, (-1)^2, (-2)^2, (-2)^2] i)) ≥
            (∑ i : Fin 4, ![x, - y, - 2 * z, - 2 * w] i)^2
    simp [Fin.sum_univ_four]
    left; norm_num
    simp [Fin.sum_univ_four]
    ring
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> norm_num
    intro i _
    fin_cases i <;> norm_num
    ring; ring
  rw [h0, ← h1] at h2
  apply Real.le_sqrt_of_sq_le at h2
  norm_num at h2
  exact h2
