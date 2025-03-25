import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p16 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x ^ 3 + (1:ℝ) / 3 * y ^ 3  ≥ x^2 * y := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^3, x^3, y^3]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        nlinarith [ sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 3, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 3, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 3, (w i : ℝ) * S i) / (∑ i: Fin 3, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_three, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_three] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_three] at amgm

  have x2p : 0 < x ^ 2 := by nlinarith
  have x3p : 0 < x ^ 3 := by nlinarith
  have x6p : 0 < x ^ 6 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y3p : 0 < y ^ 3 := by nlinarith

  have xtrans : (x ^ 6) ^ (3⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 3 )^ (3⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.le]

  calc 2 / 3 * x ^ 3 + 1 / 3 * y ^ 3 = ( x ^ 3 + x ^ 3 + y ^ 3 ) / 3 := by ring
    _ ≥ (x ^ 3 * x ^ 3 * y ^ 3 ) ^ (3⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 6 * y ^ 3) ^ (3⁻¹: ℝ ) := by ring
    _ = (x ^ 6) ^ (3⁻¹: ℝ ) * (y ^ 3 )^ (3⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y := by rw [xtrans, ytrans]
