import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p24 (a b c : ℝ) (ap : a > 0) (bp : b> 0) (cp : c> 0) : a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a := by
  have x3y3gex2ylem (x y: ℝ )  (hx : x > 0) (hy : y> 0): (2:ℝ) / 3 * x ^ 3 + (1:ℝ) / 3 * y ^ 3  ≥ x^2 * y := by
    -- Step 1: Define the two numbers to apply AM-GM
    let S := ![x^3, y^3]
    let l := ![(2:ℝ) / 3, (1:ℝ) / 3]

    have x2p : 0 < x ^ 2 := by nlinarith
    have x3p : 0 < x ^ 3 := by nlinarith
    have y2p : 0 < y ^ 2 := by nlinarith
    have y3p : 0 < y ^ 3 := by nlinarith

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

    have xtrans : (x ^ 3) ^ ((2:ℝ)/3) = x ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hx) ]
      norm_num

    have ytrans : (y ^ 3 )^ (3⁻¹: ℝ ) = y := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hy) ]
      norm_num

    calc (2:ℝ) / 3 * x ^ 3 + (1:ℝ) / 3 * y ^ 3 ≥ (x ^ 3) ^ ((2:ℝ)/3) * (y ^ 3 )^ (3⁻¹: ℝ ) := by nlinarith
      _ = x ^ 2 * y := by nlinarith

  have hab : (2:ℝ) / 3 * a^3 + (1:ℝ) / 3 * b^3  ≥ a^2 * b := by apply x3y3gex2ylem a b ap bp
  have hbc : (2:ℝ) / 3 * b^3 + (1:ℝ) / 3 * c^3  ≥ b^2 * c := by apply x3y3gex2ylem b c bp cp
  have hca : (2:ℝ) / 3 * c^3 + (1:ℝ) / 3 * a^3  ≥ c^2 * a := by apply x3y3gex2ylem c a cp ap

  nlinarith
