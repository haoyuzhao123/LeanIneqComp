import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p19 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (3:ℝ)/5 * x^5 + (1:ℝ)/5 * y^5 + (1:ℝ)/5 * z^5 ≥ x ^ 3 * y * z := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^5, y^5, z^5]
  let l := ![(3:ℝ)/5, (1:ℝ)/5, (1:ℝ)/5]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x5p : 0 < x ^ 5 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have y5p : 0 < y ^ 5 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith
  have z5p : 0 < z ^ 5 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [x5p, y5p, z5p]

  have l_nonneg : ∀ i ∈ Finset.univ, 0 ≤ l i := by
      intros i
      fin_cases i
      all_goals
        simp [l]
        <;> norm_num

  have l_sump : 0 < ∑ i : Fin 3, l i := by
      simp [l]
      simp [Fin.sum_univ_three]
      norm_num

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 3, S i ^ (l i : ℝ)) ^ ((∑ i : Fin 3, (l i : ℝ))⁻¹) ≤ (∑ i : Fin 3, (l i : ℝ) * S i) / (∑ i: Fin 3, (l i : ℝ)) := by
      apply Real.geom_mean_le_arith_mean
      exact l_nonneg
      exact l_sump
      exact h_nonneg

  simp [S] at amgm
  simp [l] at amgm
  simp [Fin.sum_univ_three] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_three] at amgm

  have xtrans : (x ^ 5) ^ (3/5: ℝ ) = x ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx) ]
    norm_num
    norm_cast

  have ytrans : (y ^ 5)^ (5⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hy)]
    norm_num

  have ztrans : (z ^ 5 )^ (5⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hz)]
    norm_num

  calc (3:ℝ)/5 * x^5 + (1:ℝ)/5 * y^5 + (1:ℝ)/5 * z^5 ≥ (x ^ 5) ^ (3/5: ℝ ) * (y ^ 5) ^ (5⁻¹:ℝ) * (z ^ 5) ^ (5⁻¹:ℝ) := by nlinarith
    _ = x^3 * y * z := by rw [xtrans, ytrans, ztrans]
