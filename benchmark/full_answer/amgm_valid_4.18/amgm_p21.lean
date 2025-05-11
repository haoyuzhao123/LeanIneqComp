import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p21 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (2:ℝ)/3 * x^2 + (1:ℝ)/6 * y^2 + (1:ℝ)/6 * z^2 ≥ x^((4:ℝ)/3) * y^((1:ℝ)/3) * z^((1:ℝ)/3) := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^2, y^2, z^2]
  let l := ![(2:ℝ)/3, (1:ℝ)/6, (1:ℝ)/6]

  have x2p : 0 < x ^ 2 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [x2p, y2p, z2p]

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

  have xtrans : (x ^ 2) ^ ((2: ℝ)/3 ) = x ^ ((4: ℝ)/3 ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx) ]
    norm_num

  have ytrans : (y ^ 2 )^ ((1: ℝ)/6 ) = y ^ ((1: ℝ)/3 )  := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hy) ]
    norm_num

  have ztrans : (z ^ 2 )^ ((1: ℝ)/6 ) = z ^ ((1: ℝ)/3 ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hz) ]
    norm_num

  calc (2:ℝ)/3 * x^2 + (1:ℝ)/6 * y^2 + (1:ℝ)/6 * z^2 ≥ (x ^ 2) ^ ((2: ℝ)/3 ) * (y ^ 2 )^ ((1: ℝ)/6 ) * (z ^ 2 )^ ((1: ℝ)/6 ) := by nlinarith
    _ = x ^ ((4: ℝ)/3 ) * y ^ ((1: ℝ)/3 ) * z ^ ((1: ℝ)/3 ) := by rw [xtrans, ytrans, ztrans]
