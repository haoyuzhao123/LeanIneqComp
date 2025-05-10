import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p5 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * x ^ ((1:ℝ)/3) + (3:ℝ)/8 * y ^ ((1:ℝ)/3) + (3:ℝ)/8 * z ^ ((1:ℝ)/3) ≤ ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) ^ ((1:ℝ)/3) := by
  let w := ![(1:ℝ)/4, (3:ℝ)/8, (3:ℝ)/8]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, S i ∈ Set.Ici 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : ∑ i : Fin 3, w i * (S i) ^ ((1:ℝ)/3) ≤ (∑ i : Fin 3, w i * S i) ^ ((1:ℝ)/3) := by
    apply (concaveOn_rpow (by positivity) (by norm_num)).le_map_sum w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  simp
  nlinarith
