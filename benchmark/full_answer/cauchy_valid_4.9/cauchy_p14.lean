import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p14 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / b i ≥ (∑ i, a i)^2 / ∑ i, a i * b i := by
  have h1 : (∑ i, a i / b i) * (∑ i, a i * b i) ≥ (∑ i, a i)^2 := by
    convert_to (∑ i, (√(a i / b i))^2) *
            (∑ i, (√(a i * b i))^2) ≥
            (∑ i, √(a i / b i) * √(a i * b i))^2
    congr! with i1 _ i2 _
    rw [sq_sqrt]
    exact div_nonneg (by linarith [ha i1]) (by linarith [hb i1])
    rw [sq_sqrt]
    exact mul_nonneg (by linarith [ha i2]) (by linarith [hb i2])
    congr! with i
    rw [← Real.sqrt_mul, mul_comm_div, ← mul_div, div_self]
    simp
    rw [Real.sqrt_mul_self]
    linarith [ha i]
    linarith [hb i]
    exact div_nonneg (by linarith [ha i]) (by linarith [hb i])
    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [ge_iff_le]
  apply div_le_of_nonneg_of_le_mul
  apply Finset.sum_nonneg
  congr! with i
  exact mul_nonneg (by linarith [ha i]) (by linarith [hb i])
  apply Finset.sum_nonneg
  congr! with i
  exact div_nonneg (by linarith [ha i]) (by linarith [hb i])
  linarith
