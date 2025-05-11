import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p16 (x y a b: ℝ) (hy : y ≠ 0) (hb : b ≠ 0) (hxy : x^2 + 1 / y^2 = 1) (hab : a^2 + 1 / b^2 = 4) : |a / y + x / b| ≤ 2 := by
  have h1 : (x^2 + 1 / y^2) * (a^2 + 1 / b^2) ≥ (a / y + x / b)^2 := by
    convert_to (∑ i : Fin 2, (![1 / y^2, x^2] i)) *
            (∑ i : Fin 2, (![a^2, 1 / b^2] i)) ≥
            (∑ i : Fin 2, ![a / y, x / b] i)^2
    simp [Fin.sum_univ_two]; left; ring
    simp [Fin.sum_univ_two]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> simp [sq_nonneg]; ring; rw [div_pow, inv_eq_one_div, mul_div, mul_one]
  rw [hxy, hab] at h1
  rw [← sq_le_sq₀, sq_abs]
  linarith
  exact abs_nonneg _
  norm_num
