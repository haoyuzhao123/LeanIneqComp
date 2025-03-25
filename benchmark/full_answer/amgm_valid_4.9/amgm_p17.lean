import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p17 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (1:ℝ) / 2 * x ^ 4 + (1:ℝ) / 4 * y ^ 4 + (1:ℝ) / 4 * z ^ 4 ≥ x^2 * y * z := by
  -- Step 1: Define the four numbers to apply AM-GM
  let S := ![x^4, x^4, y^4, z^4]
  let w := ![1, 1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [ sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 4, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 4, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 4, (w i : ℝ) * S i) / (∑ i: Fin 4, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_four, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_four] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_four] at amgm

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x8p : 0 < x ^ 8 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith

  have xtrans : (x ^ 8) ^ (4⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 4 )^ (4⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.1.le]

  have ztrans : (z ^ 4 )^ (4⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.2.le]

  calc 1 / 2 * x ^ 4 + 1 / 4 * y ^ 4 + 1 / 4 * z ^ 4 = ( x ^ 4 + x ^ 4 + y ^ 4 + z ^ 4) / 4 := by ring
    _ ≥ (x ^ 4 * x ^ 4 * y ^ 4 * z ^ 4) ^ (4⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 8 * y ^ 4 * z ^ 4) ^ (4⁻¹: ℝ ) := by ring
    _ = (x ^ 8 * y ^ 4) ^ (4⁻¹: ℝ ) * (z ^ 4) ^ (4⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = (x ^ 8 )^ (4⁻¹: ℝ ) * (y ^ 4) ^ (4⁻¹: ℝ ) * (z ^ 4) ^ (4⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y * z := by rw [xtrans, ytrans, ztrans]
