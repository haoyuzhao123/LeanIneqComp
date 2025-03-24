import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem induction_p4 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction' h₀ with k g IH
  · calc 3 ! = 6 := by simp [Nat.factorial_succ]
      _ < 9 := by simp
      _ = 3 ^ (3 - 1) := by simp

  have lk : k ^ (k - 1) ≤ k.succ ^ (k - 1) := by
    -- Apply the lemma that if `a ≤ b`, then `a^j ≤ b^j` for non-negative `j`.
    apply Nat.pow_le_pow_left
    -- Prove that `k ≤ k.succ` (since `k.succ = k + 1`).
    exact Nat.le_succ k

  have lksucc : k.succ * ( k.succ ^ (k - 1) ) = k.succ ^ k := by
    induction' g with j h hk
    <;> simp_all [Nat.pow_succ]
    ring

  calc k.succ ! = k.succ * k ! := by apply Nat.factorial_succ
    _ < k.succ * k ^ (k - 1) := by nlinarith
    -- Apply the lemma that if `a ≤ b`, then `a^k ≤ b^k` for non-negative `k`.
    -- Prove that `n ≤ n.succ` (since `n.succ = n + 1`).
    _ ≤ k.succ * (k.succ ^ (k - 1)) := by nlinarith
    --_ = k.succ ^ (k - 1) * k.succ := by ring
    _ = k.succ ^ k := by apply lksucc
