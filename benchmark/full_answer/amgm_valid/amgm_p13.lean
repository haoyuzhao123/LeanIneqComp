import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p13 (x y: ℝ )  (h : x > 0 ∧ y> 0): (4:ℝ) / 5 * x ^ 5 + (1:ℝ) / 5 * y ^ 5  ≥ x^4 * y := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^5, y^5]
  let l := ![(4:ℝ) / 5, (1:ℝ) / 5]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x3p : 0 < x ^ 3 := by nlinarith
  have x5p : 0 < x ^ 5 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y3p : 0 < y ^ 3 := by nlinarith
  have y5p : 0 < y ^ 5 := by nlinarith

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

  have xtrans : (x ^ 5) ^ ((4:ℝ)/5) = x ^ 4 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num
    norm_cast

  have ytrans : (y ^ 5 )^ (5⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.2) ]
    norm_num

  calc (4:ℝ) / 5 * x ^ 5 + (1:ℝ) / 5 * y ^ 5 ≥ (x ^ 5) ^ ((4:ℝ)/5) * (y ^ 5 )^ (5⁻¹: ℝ ) := by nlinarith
    _ = x ^ 4 * y := by rw [xtrans, ytrans]
