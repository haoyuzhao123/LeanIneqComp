import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem schur_p3 (a b c t: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≥ b)(hbc : b ≥ c) (ht : t > 0) : a^t * (a - b) * (a - c) + b^t * (b - c) * (b - a) + c^t * (c - a) * (c - b) ≥ 0 := by
  have hab1 : a - b ≥ 0 := by linarith
  have hbc1 : b - c ≥ 0 := by linarith
  have hca1 : a - c ≥ 0 := by linarith
  have ha1 : a^t > 0 := by positivity
  have hb1 : b^t > 0 := by positivity
  have hc1 : c^t > 0 := by positivity
  have h1 : (a - b) * (a^t * (a - c) - b^t * (b - c)) + c^t * (a - c) * (b - c) ≥ 0 := by
    have : c^t * (a - c) * (b - c) ≥ 0 := by positivity
    have : a^t * (a - c) - b^t * (b - c) ≥ 0 := by
      have eq : a^t * (a - c) - b^t * (b - c) = (a^t - b^t) * (a - c) + b^t * (a - b) := by ring
      rw [eq]
      have : b^t ≤ a^t := by
        apply Real.rpow_le_rpow
        positivity
        linarith
        positivity
      have : a^t - b^t ≥ 0 := by linarith
      positivity
    positivity
  nlinarith
