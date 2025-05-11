import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p2 (x y: ℝ) (hx : x > 0) (hy : y > 0) : (2 * x + y) / 3 ≥ (x * x * y) ^ (3⁻¹: ℝ ) := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, x, y]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [hx, hy]

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 3, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 3, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 3, (w i : ℝ) * S i) / (∑ i: Fin 3, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_three, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_three] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_three] at amgm

  linarith
