import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p1 (x y : ℝ) (h : x > 0) (g : y > 0) : ((1:ℝ)/3 * x + (2:ℝ)/3 * y) ^ 4 ≤ (1:ℝ)/3 * x^4 + (2:ℝ)/3 * y ^ 4  := by
  let w := ![(1:ℝ)/3, (2:ℝ)/3]
  let S := ![x, y]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 2, w i = 1 := by
      simp [w]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 2, w i * S i)^4 ≤ ∑ i : Fin 2, w i * S i ^ 4 := by
    apply (convexOn_pow 4).map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  nlinarith
