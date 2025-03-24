import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem induction_p3 (n : ℕ) (h₀ : 4 ≤ n) : n ^ 2 ≤ n ! := by
  induction' h₀ with k g IH
  · calc 4 ^ 2 = 16 := by simp
      _ ≤ 24 := by simp
      _ = 4 ! := by simp [Nat.factorial_succ]
  have j : k ≥ 4 := by norm_cast
  calc k.succ ^ 2 = (k + 1) ^ 2 := by simp
    _ = k ^ 2 + 2 * k + 1 := by ring
    _ ≤ k ^ 2 + 2 * k + 4 := by simp
    _ ≤ k ^ 2 + 2 * k + k := by simp_all
    _ = k ^ 2 + 3 * k := by ring
    _ ≤ k ^ 2 + k ^ 2 := by nlinarith
    _ = 2 * k ^ 2 := by ring
    _ ≤ k.succ * k ^ 2 := by nlinarith
    _ ≤ k.succ * k ! := by nlinarith
    _ = k.succ ! := by apply Nat.factorial_succ
