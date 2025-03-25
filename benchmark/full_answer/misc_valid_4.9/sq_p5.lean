import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem sq_p5 (a b c d: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a^2 + b^2 + c^2 + d^2 ≥ a*b + b*c + c*d + d*a := by
  have g : a^2 + b^2 + c^2 + d^2 - a*b - b*c - c*d - d*a ≥ 0 := by
    calc a^2 + b^2 + c^2 + d^2 - a*b - b*c - c*d - d*a = (1:ℝ)/2 * ( (a-b)^2 + (b-c)^2 + (c-d)^2 + (d-a)^2 ) := by ring
      _ ≥ 0 := by nlinarith
  nlinarith
