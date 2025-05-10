import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p13 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1) ≤ √15 := by
  have h1 : 3 * (2 * (a + b + c) + 3) ≥ (√(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1))^2 := by
    convert_to (∑ i : Fin 3, (![1, 1, 1] i)^2) *
            (∑ i : Fin 3, (![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i)^2) ≥
            (∑ i : Fin 3, ![1, 1, 1] i * ![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i)^2

    have g1 : 3 * (2 * (a + b + c) + 3) =
    (∑ i : Fin 3, ![1, 1, 1] i ^ 2) * ∑ i : Fin 3, ![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp; ring
    exact g1

    have g2 : (√(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1)) ^ 2 =
    (∑ i : Fin 3, ![1, 1, 1] i * ![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i) ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [h] at h1
  norm_num at h1
  apply Real.sqrt_le_sqrt at h1
  rw [Real.sqrt_sq (add_nonneg (add_nonneg (Real.sqrt_nonneg (2 * a + 1)) (Real.sqrt_nonneg (2 * b + 1))) (Real.sqrt_nonneg (2 * c + 1)))] at h1
  exact h1

