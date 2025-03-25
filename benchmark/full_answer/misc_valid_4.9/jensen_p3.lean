import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p3 (x y : ℝ) (h : x > 0) (g : y > 0): ((1:ℝ)/4 * x + (3:ℝ)/4 * y) * Real.log ((1:ℝ)/4 * x + (3:ℝ)/4 * y) ≤ (1:ℝ)/4 * x * Real.log x + (3:ℝ)/4 * y * Real.log y := by
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

  have s_nonneg : ∀ i ∈ Finset.univ, S i ∈ Set.Ici 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 2, w i * S i) * Real.log (∑ i : Fin 2, w i * S i) ≤ ∑ i : Fin 2, w i * ((S i) * Real.log (S i)) := by
    apply Real.convexOn_mul_log.map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  simp
  nlinarith
