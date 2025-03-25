import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem schur_p5 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : 2 * a^2 * (b + c) + 2 * b^2 * (c + a) + 2 * c^2 * (a + b) ≥ a^3 + b^3 + c^3 + 9 * a * b * c := by
  let x := (a + c - b) / 2
  let y := (a + b - c) / 2
  let z := (b + c - a) / 2
  have hx : x > 0 := by
    have : a + c - b > 0 := by linarith
    positivity
  have hy : y > 0 := by
    have : a + b - c > 0 := by linarith
    positivity
  have hz : z > 0 := by
    have : b + c - a > 0 := by linarith
    positivity
  have ha1 : a = x + y := by ring
  have hb1 : b = y + z := by ring
  have hc1 : c = z + x := by ring

  rw [ha1, hb1, hc1]

  have schur : x^2 * z + x * z^2 + y^2 * z + y * z^2 + x^2 * y + x * y^2 ≤ 3 * x * y * z + x^3 + y^3 + z^3 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_self_nonneg (x - y + z), mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]

  have eq1 : 2 * (x + y) ^ 2 * (y + z + (z + x)) + 2 * (y + z) ^ 2 * (z + x + (x + y)) + 2 * (z + x) ^ 2 * (x + y + (y + z)) - ((x + y) ^ 3 + (y + z) ^ 3 + (z + x) ^ 3 + 9 * (x + y) * (y + z) * (z + x)) = 2 * (3 * x * y * z + x^3 + y^3 + z^3 - (x^2 * z + x * z^2 + y^2 * z + y * z^2 + x^2 * y + x * y^2)) := by ring

  nlinarith
