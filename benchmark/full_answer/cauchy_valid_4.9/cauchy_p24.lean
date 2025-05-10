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
    convert_to (∑ i : Fin 3, (![√(2 * x^2 - y^2), √(2 * y^2 - z^2), √(2 * z^2 - x^2)] i)^2) *
            (∑ i : Fin 3, (![√(x^3 / (2 * x - y^2 / x)), √(y^3 / (2 * y - z^2 / y)), √(z^3 / (2 * z - x^2 / z))] i)^2) ≥
            (∑ i : Fin 3, ![√(2 * x^2 - y^2), √(2 * y^2 - z^2), √(2 * z^2 - x^2)] i * ![√(x^3 / (2 * x - y^2 / x)), √(y^3 / (2 * y - z^2 / y)), √(z^3 / (2 * z - x^2 / z))] i)^2

    have g1 : (x^2 + y^2 + z^2) * (x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z)) =
    (∑ i : Fin 3, (![√(2 * x^2 - y^2), √(2 * y^2 - z^2), √(2 * z^2 - x^2)] i)^2) *
    (∑ i : Fin 3, (![√(x^3 / (2 * x - y^2 / x)), √(y^3 / (2 * y - z^2 / y)), √(z^3 / (2 * z - x^2 / z))] i)^2) := by
      simp [Fin.sum_univ_three]
      repeat rw [sq_sqrt]
      field_simp; left; ring
      all_goals exact div_nonneg (pow_nonneg (by linarith [hx, hy, hz]) _) (by linarith [hxy, hyz, hzx])
      all_goals linarith
    exact g1

    have g2 : (x^2 + y^2 + z^2)^2 = (∑ i : Fin 3, ![√(2 * x^2 - y^2), √(2 * y^2 - z^2), √(2 * z^2 - x^2)] i * ![√(x^3 / (2 * x - y^2 / x)), √(y^3 / (2 * y - z^2 / y)), √(z^3 / (2 * z - x^2 / z))] i)^2 := by
      simp [Fin.sum_univ_three]
      field_simp
      repeat rw [mul_div_right_comm]
      rw [mul_assoc 2 x x, ← sq, div_self, one_mul]
      rw [mul_assoc 2 y y, ← sq, div_self, one_mul]
      rw [mul_assoc 2 z z, ← sq, div_self, one_mul]
      calc
        x ^ 2 + y ^ 2 + z ^ 2
          = sqrt (x ^ 4) + sqrt (y ^ 4) + sqrt (z ^ 4) := by
            rw [← Real.sqrt_sq (sq_nonneg x), ← pow_mul]
            rw [← Real.sqrt_sq (sq_nonneg y), ← pow_mul]
            rw [← Real.sqrt_sq (sq_nonneg z), ← pow_mul]
        _ = sqrt (x ^ 3) * sqrt x + sqrt (y ^ 3) * sqrt y + sqrt (z ^ 3) * sqrt z := by
          rw [pow_succ x, Real.sqrt_mul]
          rw [pow_succ y, Real.sqrt_mul]
          rw [pow_succ z, Real.sqrt_mul]
          repeat exact pow_nonneg (by linarith [hx, hy, hz]) _

      repeat exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [sq (x ^ 2 + y ^ 2 + z ^ 2)] at h1
  apply le_of_mul_le_mul_left h1
  nlinarith
