import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p4 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x + (1:ℝ) / 3 * y  ≥ x^((2:ℝ) / 3) * y^((1:ℝ) / 3) := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y]
  let l := ![(2:ℝ) / 3, (1:ℝ) / 3]

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

  -- the following simp rewrite (1:ℝ)/n to n⁻¹
  simp
  linarith
