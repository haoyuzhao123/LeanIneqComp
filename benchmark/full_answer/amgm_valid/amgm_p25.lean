import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p25 (a b c : ℝ) (ap : a > 0) (bp : b> 0) (cp : c> 0) : a^7 + b^7 + c^7 ≥ a^4 * b^3 + b^4 * c^3 + c^4 * a^3 := by
  have x7y7gex4y3lem (x y: ℝ ) (hx : x > 0 ) (hy : y> 0) : (4:ℝ) / 7 * x ^ 7 + (3:ℝ) / 7 * y ^ 7  ≥ x^4 * y^3 := by
    -- Step 1: Define the two numbers to apply AM-GM
    let S := ![x^7, y^7]
    let l := ![(4:ℝ) / 7, (3:ℝ) / 7]

    have x2p : 0 < x ^ 2 := by nlinarith
    have x4p : 0 < x ^ 4 := by nlinarith
    have x6p : 0 < x ^ 6 := by nlinarith
    have x7p : 0 < x ^ 7 := by nlinarith
    have y2p : 0 < y ^ 2 := by nlinarith
    have y4p : 0 < y ^ 4 := by nlinarith
    have y6p : 0 < y ^ 6 := by nlinarith
    have y7p : 0 < y ^ 7 := by nlinarith

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

    have xtrans : (x ^ 7) ^ ((4:ℝ)/7) = x ^ 4 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hx) ]
      norm_num
      norm_cast

    have ytrans : (y ^ 7 )^ ((3:ℝ)/7) = y ^ 3 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hy) ]
      norm_num
      norm_cast

    calc (4:ℝ) / 7 * x ^ 7 + (3:ℝ) / 7 * y ^ 7 ≥ (x ^ 7) ^ ((4:ℝ)/7) * (y ^ 7 )^ ((3:ℝ)/7) := by nlinarith
      _ = x ^ 4 * y ^ 3 := by rw [xtrans, ytrans]

  have hab : (4:ℝ)/7 * a^7 + (3:ℝ)/7 * b^7  ≥ a^4 * b^3 := by apply x7y7gex4y3lem a b ap bp
  have hbc : (4:ℝ)/7 * b^7 + (3:ℝ)/7 * c^7  ≥ b^4 * c^3 := by apply x7y7gex4y3lem b c bp cp
  have hca : (4:ℝ)/7 * c^7 + (3:ℝ)/7 * a^7  ≥ c^4 * a^3 := by apply x7y7gex4y3lem c a cp ap

  nlinarith
