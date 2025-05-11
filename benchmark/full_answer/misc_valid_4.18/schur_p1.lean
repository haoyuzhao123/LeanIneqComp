import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem schur_p1 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  let x := a
  let y := 1
  let z := 1 / b
  have hx : 0 < x := by positivity
  have hy : (0 : ℝ) < y := by positivity
  have hz : 0 < z := by positivity
  have h1 : a = x / y := by ring
  have h2 : b = y / z := by field_simp; ring; rw [mul_inv_cancel₀]; linarith
  have h3 : c = z / x := by
    have h31 : x = a := by linarith
    have h32 : z = 1 / b := by linarith
    rw [h31, h32]
    field_simp
    ring
    rw [mul_comm, mul_comm c b, ← mul_assoc]
    exact h

  rw [h1, h2, h3]
  field_simp

  have schur : (x - y + z) * (y - z + x) * (z - x + y) ≤ y * z * x := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_self_nonneg (x - y + z), mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]

  apply div_le_one_of_le₀ schur
  positivity
