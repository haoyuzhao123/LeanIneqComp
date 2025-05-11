import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem sq_p3 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a ^ 4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
  have abp : a * b > 0 := by nlinarith
  have bcp : b * c > 0 := by nlinarith
  have cap : c * a > 0 := by nlinarith

  have g : a ^ 4 + b^4 + c^4 - a * b * c * (a + b + c) ≥ 0 := by
    calc a ^ 4 + b^4 + c^4 - a * b * c * (a + b + c) = (1:ℝ)/2 * ((a^2 + b^2 + c^2 + 2 * a * b) * (a-b)^2 + (a^2 + b^2 + c^2 + 2 * b * c) * (b-c)^2 + (a^2 + b^2 + c^2 + 2 * c * a) * (c-a)^2) := by ring
      _ ≥ 0 := by nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]

  nlinarith
