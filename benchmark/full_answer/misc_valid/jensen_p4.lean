import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p4 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = 3) : (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y ^ 6 + (1:ℝ)/3 * z ^ 6 ≥ 1 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 3, w i * S i)^6 ≤ ∑ i : Fin 3, w i * S i ^ 6 := by
    apply (convexOn_pow 6).map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  calc (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y ^ 6 + (1:ℝ)/3 * z ^ 6 ≥ ((1:ℝ)/3 * x + (1:ℝ)/3 * y + (1:ℝ)/3 * z)^6 := by linarith
    _ = ((1:ℝ)/3 * (x + y + z))^6 := by ring
    _ = ((1:ℝ)/3 * 3)^6 := by rw [k]
    _ = 1 := by norm_num
