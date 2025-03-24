import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p7 (x y z w: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : (1:ℝ)/3 * x + (1:ℝ)/3 * y + (1:ℝ)/6 * z + (1:ℝ)/6 * w ≥ x ^ ((1:ℝ)/3) * y ^ ((1:ℝ)/3) * z ^ ((1:ℝ)/6) * w ^ ((1:ℝ)/6) := by
  -- Step 1: Define the four numbers to apply AM-GM
  let S := ![x, y, z, w]
  let l := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/6, (1:ℝ)/6]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [hx, hy, hz, hw]

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

  linarith
