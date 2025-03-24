import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p20 (a b c : ℝ) (ha : a > 1) (hb : b > 1) (hc : c > 1) (h : (a^2 - 1) / 2 + (b^2 - 1) / 2 + (c^2 - 1) / 3 = 1) : a + b + c ≤ 7 * √3 / 3 := by
  have h0 : a^2 / 2 + b^2 / 2 + c^2 / 3 = 7 / 3 := by linarith [h]
  have h1 : 7 * (a^2 / 2 + b^2 / 2 + c^2 / 3) ≥ (a + b + c)^2 := by
    convert_to (∑ i : Fin 3, (![√2, √2, √3] i)^2) *
            (∑ i : Fin 3, (![√(a^2 / 2), √(b^2 / 2), √(c^2 / 3)] i)^2) ≥
            (∑ i : Fin 3, ![√2, √2, √3] i * ![√(a^2 / 2), √(b^2 / 2), √(c^2 / 3)] i)^2
    simp [Fin.sum_univ_three]
    field_simp; left; norm_num
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h0] at h1
  norm_num at h1
  apply le_of_sq_le_sq
  have : (7 * √3 / 3) ^ 2 = 49 / 3 := by
    ring; norm_num
  nlinarith
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) (by norm_num)
