import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p24 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (hxy : 2 * x - y^2 / x > 0) (hyz : 2 * y - z^2 / y > 0) (hzx : 2 * z - x^2 / z > 0) : x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z) ≥ x^2 + y^2 + z^2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have hxy1 : 2 * x^2 - y^2 > 0 := by
    have h0 : 2 * x^2 - y^2 = x * (2 * x - y^2 / x) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hx hxy
  have hyz1 : 2 * y^2 - z^2 > 0 := by
    have h0 : 2 * y^2 - z^2 = y * (2 * y - z^2 / y) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hy hyz
  have hzx1 : 2 * z^2 - x^2 > 0 := by
    have h0 : 2 * z^2 - x^2 = z * (2 * z - x^2 / z) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hz hzx
  have h1 : (x^2 + y^2 + z^2) * (x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z)) ≥ (x^2 + y^2 + z^2)^2 := by
    convert_to (∑ i : Fin 3, (![2 * x^2 - y^2, 2 * y^2 - z^2, 2 * z^2 - x^2] i)) *
            (∑ i : Fin 3, (![x^3 / (2 * x - y^2 / x), y^3 / (2 * y - z^2 / y), z^3 / (2 * z - x^2 / z)] i)) ≥
            (∑ i : Fin 3, ![x^2, y^2, z^2] i)^2
    simp [Fin.sum_univ_three]; left; ring
    simp [Fin.sum_univ_three]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp <;> linarith
    intro i _
    fin_cases i <;> simp [sq_nonneg] <;> exact div_nonneg (pow_nonneg (by linarith) 3) (by linarith)
    intro i _
    fin_cases i <;> field_simp [sq_nonneg] <;> simp [mul_div_right_comm, mul_assoc, sq] <;> rw [div_self] <;> ring_nf <;> linarith
  rw [sq (x ^ 2 + y ^ 2 + z ^ 2)] at h1
  apply le_of_mul_le_mul_left h1
  nlinarith
