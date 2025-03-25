import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p14 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x ^ 6 + (1:ℝ) / 3 * y ^ 6  ≥ x^4 * y^2 := by
  -- Step 1: Define the two numbers to apply AM-GM
  let S := ![x^6, y^6]
  let l := ![(2:ℝ) / 3, (1:ℝ) / 3]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x3p : 0 < x ^ 3 := by nlinarith
  have x6p : 0 < x ^ 6 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y3p : 0 < y ^ 3 := by nlinarith
  have y6p : 0 < y ^ 6 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith

  have l_nonneg : ∀ i ∈ Finset.univ, 0 ≤ l i := by
      intros i
      fin_cases i
      all_goals
        simp [l]
        <;> norm_num

  have l_sump : 0 < ∑ i : Fin 2, l i := by
      simp [l]
      norm_num

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 2, S i ^ (l i : ℝ)) ^ ((∑ i : Fin 2, (l i : ℝ))⁻¹) ≤ (∑ i : Fin 2, (l i : ℝ) * S i) / (∑ i: Fin 2, (l i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    exact l_nonneg
    exact l_sump
    exact h_nonneg

  simp [S] at amgm
  simp [l] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_two] at amgm

  have xtrans : (x ^ 6) ^ ((2:ℝ)/3) = x ^ 4 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num
    norm_cast

  have ytrans : (y ^ 6 )^ (3⁻¹: ℝ ) = y ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.2) ]
    norm_num

  calc (2:ℝ) / 3 * x ^ 6 + (1:ℝ) / 3 * y ^ 6 ≥ (x ^ 6) ^ ((2:ℝ)/3) * (y ^ 6 )^ (3⁻¹: ℝ ) := by nlinarith
    _ = x ^ 4 * y^2 := by rw [xtrans, ytrans]
