import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

-- 又名：我没做出来的题
theorem cauchy_p21 (n : ℕ) (hn : n > 1) (a : Fin (n + 1) → ℝ) (ha : ∀ i, a i > 0) (h : a n = a 0) (hs : ∑ i : Fin n, a i = 1): ∑ i : Fin n, (a i)^2 / (a i + a (i + 1)) ≥ 1 / 2 := by
  have hsum : ∑ i : Fin n, a ↑↑i = 1 := hs
  convert_to ∑ i : Fin n, (a i)^2 / (a i + a (i + 1)) ≥ (∑ i : Fin n, a i)^2 / ∑ i : Fin n, (a i + a (i + 1))
  rw [Finset.sum_add_distrib, hsum]
  have hplus : ∑ i : Fin n, a (↑↑i + 1) = ∑ i : Fin n, a ↑↑i := by sorry
  rw [hplus, hsum]
  norm_num
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  exact add_pos (ha i) (ha (i + 1))
