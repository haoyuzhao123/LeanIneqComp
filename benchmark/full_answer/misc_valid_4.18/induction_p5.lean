import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem induction_p5 (n : ℕ) (h₀ : 0 < n) : (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
  induction' h₀ with m j IH
  · calc ∏ k ∈ Finset.Icc 1 (succ 0), (1 + (1 : ℝ) / ↑k ^ 3) = 1 + (1 : ℝ) / 1 ^ 3 := by norm_cast; rw [Finset.Icc_self, Finset.prod_singleton]
      _ = (2 : ℝ) := by norm_num
      _ ≤ 3 - (1 : ℝ) / (succ 0) := by norm_num

  have hsuccm: (succ m : ℝ) ^ 3 > 0 := by norm_cast; simp

  have hmp: m > 0 := by cases m with
  | zero =>
    -- Case 1: `m = 0` leads to a contradiction with `j : 0 ≥ 1`
    contradiction
  | succ m' =>
    simp

  have hmnn : m ≥ 0 := by linarith

  have hmpr : (m : ℝ) > 0 := by norm_cast
  have hmsucccum : (succ m : ℝ) ^ 3 * m > 0 := by nlinarith

  have ineq_poly : ((succ m : ℝ) ^ 3 + (1 : ℝ)) * (3 * (m : ℝ) - 1) ≤ (3 * (succ m : ℝ) ^ 3 * (m : ℝ) - (succ m : ℝ) ^ 2 * m) := by
    norm_num at j
    simp [pow_succ]
    nlinarith [ mul_self_nonneg (m : ℝ) ]

  have ineq: (1 + (1 : ℝ) / (succ m) ^ 3) * (3 - (1 : ℝ) / m) ≤ (3 - (1 : ℝ) / (succ m)) := by
    calc (1 + (1 : ℝ) / (succ m) ^ 3) * (3 - (1 : ℝ) / m) = ((succ m : ℝ) ^ 3 + (1 : ℝ)) * (3 * (m : ℝ) - 1) / ((succ m : ℝ) ^ 3 * m) := by field_simp
      _ ≤ (3 * (succ m : ℝ) ^ 3 * (m : ℝ) - (succ m : ℝ) ^ 2 * m) / ((succ m : ℝ) ^ 3 * m) := by gcongr
      _ = (3 * succ m - 1) * (succ m : ℝ) ^ 2 * (m : ℝ) / ((succ m : ℝ) ^ 3 * m) := by ring
      _ = (3 * succ m - 1) * (succ m : ℝ) ^ 2 / (succ m : ℝ) ^ 3 := by field_simp; ring
      _ = (3 * succ m - 1) / (succ m : ℝ) := by field_simp; ring
      _ = 3 * succ m / succ m - (1 : ℝ) / (succ m) := by ring
      _ = 3 - (1 : ℝ) / (succ m) := by field_simp

  have ihp : 1 + (1 : ℝ) / (m.succ : ℝ) ^ 3 > 0 := by field_simp
  calc ∏ k ∈ Finset.Icc 1 m.succ, (1 + 1 / ↑k ^ 3) = (∏ k ∈ Finset.Icc 1 m, (1 + 1 / ↑k ^ 3)) * (1 + (1 : ℝ) / (m.succ : ℝ) ^ 3) := by apply Finset.prod_Ioc_succ_top hmnn
    _ ≤ (3 - (1 : ℝ) / m) * (1 + (1 : ℝ) / (m.succ : ℝ) ^ 3) := by nlinarith
    _ ≤ (3 - (1 : ℝ) / (succ m)) := by nlinarith
