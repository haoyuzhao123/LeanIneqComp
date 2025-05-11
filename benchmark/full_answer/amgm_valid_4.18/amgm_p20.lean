import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p20 (x y z w: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y^6 + (1:ℝ)/6 * z^6 + (1:ℝ)/6 * w^6 ≥ x^2 * y^2 * z * w := by
  -- Step 1: Define the four numbers to apply AM-GM
  let S := ![x^6, y^6, z^6, w^6]
  let l := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/6, (1:ℝ)/6]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x6p : 0 < x ^ 6 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have y6p : 0 < y ^ 6 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith
  have z6p : 0 < z ^ 6 := by nlinarith
  have w2p : 0 < w ^ 2 := by nlinarith
  have w4p : 0 < w ^ 4 := by nlinarith
  have w6p : 0 < w ^ 6 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [x6p, y6p, z6p, w6p]

  have l_nonneg : ∀ i ∈ Finset.univ, 0 ≤ l i := by
      intros i
      fin_cases i
      all_goals
        simp [l]
        <;> norm_num

  have l_sump : 0 < ∑ i : Fin 4, l i := by
      simp [l]
      simp [Fin.sum_univ_four]
      norm_num

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 4, S i ^ (l i : ℝ)) ^ ((∑ i : Fin 4, (l i : ℝ))⁻¹) ≤ (∑ i : Fin 4, (l i : ℝ) * S i) / (∑ i: Fin 4, (l i : ℝ)) := by
      apply Real.geom_mean_le_arith_mean
      exact l_nonneg
      exact l_sump
      exact h_nonneg

  simp [S] at amgm
  simp [l] at amgm
  simp [Fin.sum_univ_four] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_four] at amgm

  have xtrans : (x ^ 6) ^ ((1: ℝ)/3 ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx) ]
    norm_num

  have ytrans : (y ^ 6)^ ((1: ℝ)/3 ) = y ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hy)]
    norm_num

  have ztrans : (z ^ 6 )^ (6⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hz)]
    norm_num

  have wtrans : (w ^ 6 )^ (6⁻¹: ℝ ) = w := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hw)]
    norm_num

  calc (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y^6 + (1:ℝ)/6 * z^6 + (1:ℝ)/6 * w^6 ≥ (x ^ 6) ^ ((1:ℝ)/3) * (y ^ 6) ^ ((1:ℝ)/3) * (z ^ 6) ^ (6⁻¹:ℝ) * (w ^ 6) ^ (6⁻¹:ℝ) := by nlinarith
    _ = x^2 * y^2 * z * w := by rw [xtrans, ytrans, ztrans, wtrans]
