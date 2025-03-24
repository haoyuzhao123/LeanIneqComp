import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem induction_p2 (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) : 1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction' h₁ with k h₁ IH
  · calc 1 + ↑(succ 0) * x = 1 + x := by simp
      _ ≤ (1 + x) ^ (succ 0 : ℕ) := by simp
  calc 1 + ↑k.succ * x = 1 + ↑k * x + x := by rw [Nat.cast_succ] ; ring
    _ ≤ 1 + ↑k * x + x + ↑k * x * x := by nlinarith [ sq_nonneg (x) ]
    _ = (1 + x) * (1 + ↑k * x) := by ring
    _ ≤ (1 + x) * (1 + x) ^ (k : ℕ) := by nlinarith
    _ = (1 + x) ^ k.succ := by rw [pow_succ]; ring
