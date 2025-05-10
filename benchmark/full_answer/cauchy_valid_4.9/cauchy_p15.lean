import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p15 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / (b i)^2 ≥ (∑ i, a i / b i)^2 / ∑ i, a i := by
  have h1 : (∑ i, a i / (b i)^2) * (∑ i, a i) ≥ (∑ i, a i / (b i))^2 := by
    convert_to (∑ i, (√(a i) / (b i))^2) *
            (∑ i, (√(a i))^2) ≥
            (∑ i, √(a i) / (b i) * √(a i))^2

    have g1 : (∑ i : Fin n, a i / b i ^ 2) * ∑ i : Fin n, a i = (∑ i : Fin n, (√(a i) / b i) ^ 2) * ∑ i : Fin n, √(a i) ^ 2 := by
      congr! with i1 _ i2 _
      field_simp
      rw [Real.sq_sqrt]
      linarith [ha i1]
      rw [Real.sq_sqrt]
      linarith [ha i2]
    exact g1

    have g2 : (∑ i : Fin n, a i / b i) ^ 2 = (∑ i : Fin n, √(a i) / b i * √(a i)) ^ 2 := by
      congr with i
      rw [div_mul_eq_mul_div, Real.mul_self_sqrt]
      linarith [ha i]
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [ge_iff_le]
  apply div_le_of_nonneg_of_le_mul

  have nonneg1 : 0 ≤ ∑ i : Fin n, a i := by
    apply Finset.sum_nonneg
    congr! with i
    linarith [ha i]
  exact nonneg1

  have nonneg2 : 0 ≤ ∑ i : Fin n, a i / b i ^ 2 := by
    apply Finset.sum_nonneg
    congr! with i
    exact div_nonneg (by linarith [ha i]) (sq_nonneg _)
  exact nonneg2

  linarith

