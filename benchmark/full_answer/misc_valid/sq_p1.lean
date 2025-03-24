import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem sq_p1 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a+b) * (b+c) * (c+a) ≥ 8 * a * b * c := by
  have g : (a+b) * (b+c) * (c+a) - 8 * a * b * c ≥ 0 := by
    calc (a+b) * (b+c) * (c+a) - 8 * a * b * c = a * (b-c)^2 + b * (c-a)^2 + c * (a-b)^2 := by ring
      _ ≥ 0 := by nlinarith [ sq_nonneg (b-c) , sq_nonneg (c-a) , sq_nonneg (a-b)]
  nlinarith
