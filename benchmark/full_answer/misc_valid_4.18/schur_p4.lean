import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem schur_p4 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1): 5 * (a^2 + b^2 + c^2) ≤ 6 * (a^3 + b^3 + c^3) + 1 := by
  have schur : a^2 * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a * b^2 ≤ 3 * a * b * c + a^3 + b^3 + c^3 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_self_nonneg (a - b + c), mul_self_nonneg (b - c + a), mul_self_nonneg (c - a + b)]

  have ineq : 5 * (a^3 + b^3 + c^3) + 5 * (a^2 * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a * b^2) ≤ 7 * (a^3 + b^3 + c^3) + 3 * (a^2 * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a * b^2) + 6 * a * b * c := by linarith

  have eq1 : 5 * (a^3 + b^3 + c^3) + 5 * (a^2 * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a * b^2) = 5 * (a^2 + b^2 + c^2) * (a + b + c) := by ring
  have eq2 : 7 * (a^3 + b^3 + c^3) + 3 * (a^2 * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a * b^2) + 6 * a * b * c = 6 * (a^3 + b^3 + c^3) + (a + b + c)^3 := by ring

  rw [eq1, eq2] at ineq
  rw [h] at ineq
  norm_num at ineq
  exact ineq
