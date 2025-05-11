import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem induction_p1 (n : ℕ) (h : n ≥ 4) : 2 ^ n ≥ n + 1 := by
  induction' h with k h IH
  · calc 2 ^ 4 = 16 := by norm_num
      _ ≥ 4 + 1 := by norm_num
  calc 2 ^ k.succ = 2 ^ k * 2 := Nat.pow_succ 2 k
    _ ≥ (k + 1) * 2 := by linarith
    _ = 2 * k + 2 := by ring
    _ ≥ k + 2 := by linarith
