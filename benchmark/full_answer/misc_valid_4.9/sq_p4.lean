import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem sq_p4 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a+b+c)^3 ≥ 27 * a * b * c := by
  have g : (a+b+c)^3 - 27 * a * b * c ≥ 0 := by
    calc (a+b+c)^3 - 27 * a * b * c = (1:ℝ)/2 * ((a+b+7*c) * (a-b)^2 + (a+c+7*b) * (a-c)^2 + (b+c+7*a) * (b-c)^2) := by ring
      _ ≥ 0 := by nlinarith [ sq_nonneg (b-c) , sq_nonneg (c-a) , sq_nonneg (a-b)]
  nlinarith
