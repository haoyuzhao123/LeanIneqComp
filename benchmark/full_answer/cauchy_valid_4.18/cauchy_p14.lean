import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p14 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / b i ≥ (∑ i, a i)^2 / ∑ i, a i * b i := by
  convert_to ∑ i, (a i)^2 / (a i * b i) ≥ (∑ i, a i)^2 / ∑ i, a i * b i
  congr with i
  simp [sq, div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc]
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  apply mul_pos (ha i) (hb i)
