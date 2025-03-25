import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p6 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (2:ℝ)/5 * x + (2:ℝ)/5 * y + (1:ℝ)/5 * z ≥ x ^ ((2:ℝ)/5) * y ^ ((2:ℝ)/5) * z ^ ((1:ℝ)/5) := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, z]
  let l := ![(2:ℝ)/5, (2:ℝ)/5, (1:ℝ)/5]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [hx, hy, hz]

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

  -- the following simp rewrite (1:ℝ)/n to n⁻¹
  simp
  linarith
