import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p5 (x y: ℝ )  (h : x > 0 ∧ y> 0): (4:ℝ) / 7 * x + (3:ℝ) / 7 * y  ≥ x^((4:ℝ) / 7) * y^((3:ℝ) / 7) := by
  -- Step 1: Define the two numbers to apply weighted AM-GM
  let S := ![x, y]
  let l := ![(4:ℝ) / 7, (3:ℝ) / 7]

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

  nlinarith
