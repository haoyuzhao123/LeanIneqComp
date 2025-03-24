import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem schur_p2 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 + a / b + b / c + c / a ≥ a + b + c + 1 / a + 1 / b + 1 / c := by
  let x := a
  let y : ℝ := 1
  let z := a * b
  have hx : 0 < x := by positivity
  have hy : (0 : ℝ) < y := by positivity
  have hz : 0 < z := by positivity
  have pos : 0 < x * y * z := by positivity
  have h1 : a = x / y := by ring
  have h2 : b = z / x := by field_simp; ring
  have h3 : c = y / z := by
    field_simp
    ring
    rw [mul_comm c a, mul_assoc, mul_comm c b, ← mul_assoc]
    exact h

  rw [h1, h2, h3]

  have eq1 : x / y + y / z + z / x + 1 / (x / y) + 1 / (y / z) + 1 / (z / x) = (x ^ 2 * z + x * z ^ 2 + y ^ 2 * z + y * z ^ 2 + x ^ 2 * y + x * y ^ 2) / (x * y * z) := by
    field_simp [hx, hy, hz]
    ring
  have eq2 : 3 + x / y / (z / x) + z / x / (y / z) + y / z / (x / y) = (3 * x * y * z + x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) := by
    field_simp [hx, hy, hz, pow_three]
    ring

  have schur : x^2 * z + x * z^2 + y^2 * z + y * z^2 + x^2 * y + x * y^2 ≤ 3 * x * y * z + x^3 + y^3 + z^3 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_self_nonneg (x - y + z), mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]

  rw [← div_le_div_iff_of_pos_right pos] at schur
  nlinarith
