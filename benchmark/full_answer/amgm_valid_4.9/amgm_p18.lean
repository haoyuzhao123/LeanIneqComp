import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p18 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (2:ℝ) / 5 * x ^ 5 + (2:ℝ) / 5 * y ^ 5 + (1:ℝ) / 5 * z ^ 5 ≥ x^2 * y^2 * z := by
  -- Step 1: Define the five numbers to apply AM-GM
  let S := ![x^5, x^5, y^5, y^5, z^5]
  let w := ![1, 1, 1, 1, 1]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x5p : 0 < x ^ 5 := by nlinarith
  have x10p : 0 < x ^ 10 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have y5p : 0 < y ^ 5 := by nlinarith
  have y10p : 0 < y ^ 10 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith
  have z5p : 0 < z ^ 5 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 5, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 5, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 5, (w i : ℝ) * S i) / (∑ i: Fin 5, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_five, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_five] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_five] at amgm


  have xtrans : (x ^ 10) ^ (5⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 10 )^ (5⁻¹: ℝ ) = y ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.2.1)]
    norm_num

  have ztrans : (z ^ 5 )^ (5⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.2.le]

  calc 2 / 5 * x ^ 5 + 2 / 5 * y ^ 5 + 1 / 5 * z ^ 5 = ( x ^ 5 + x ^ 5 + y ^ 5 + y ^ 5 + z ^ 5) / 5 := by ring
    _ ≥ (x ^ 5 * x ^ 5 * y ^ 5 * y ^ 5 * z ^ 5) ^ (5⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 10 * y ^ 10 * z ^ 5) ^ (5⁻¹: ℝ ) := by ring
    _ = (x ^ 10 * y ^ 10) ^ (5⁻¹: ℝ ) * (z ^ 5) ^ (5⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = (x ^ 10 )^ (5⁻¹: ℝ ) * (y ^ 10) ^ (5⁻¹: ℝ ) * (z ^ 5) ^ (5⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y ^ 2 * z := by rw [xtrans, ytrans, ztrans]
