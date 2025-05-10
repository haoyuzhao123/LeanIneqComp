import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p2 (x y : ℝ) : Real.exp ((1:ℝ)/4 * x + (3:ℝ)/4 * y) ≤ (1:ℝ)/4 * Real.exp x + (3:ℝ)/4 * Real.exp y  := by
  let w := ![(1:ℝ)/4, (3:ℝ)/4]
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

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.univ := by
      intros i
      fin_cases i
      all_goals
        simp [S]

  have jensen_ineq : Real.exp (∑ i : Fin 2, w i * S i) ≤ ∑ i : Fin 2, w i * Real.exp (S i) := by
    apply convexOn_exp.map_sum_le w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  simp
  nlinarith
