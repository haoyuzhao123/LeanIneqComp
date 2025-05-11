import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p15 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / (b i)^2 ≥ (∑ i, a i / b i)^2 / ∑ i, a i := by
  convert_to ∑ i, (a i / b i)^2 / a i ≥ (∑ i, a i / b i)^2 / ∑ i, a i
  congr with i
  field_simp; rw [eq_comm]
  calc
    a i ^ 2 / (b i ^ 2 * a i) = a i ^ 2 / (a i * b i ^ 2) := by rw [mul_comm]
    _ = a i * a i / (a i * b i ^ 2) := by rw [pow_two]
    _ = a i * a i / a i / b i ^ 2  := by rw [div_div]
    _ = a i / b i ^ 2 := by rw [← mul_div, mul_div_cancel₀]; exact ne_of_gt (ha i)
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  exact ha i
