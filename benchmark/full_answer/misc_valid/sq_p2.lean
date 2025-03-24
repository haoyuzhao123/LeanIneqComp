import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem sq_p2 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b * c * (a + b + c) := by
  have g: a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c) ≥ 0 := by
    calc a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c) = (1:ℝ)/2 * (b^2 * (a-c)^2 + a^2 * (b-c)^2 + c^2 * (a-b)^2) := by ring
      _ ≥ 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]
  nlinarith
