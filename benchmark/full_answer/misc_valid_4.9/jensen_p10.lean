import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p10 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = (π:ℝ)): (1:ℝ)/3 * Real.cos (x/2) + (1:ℝ)/3 * Real.cos (y/2) + (1:ℝ)/3 * Real.cos (z/2) ≤ √3 / 2 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x/2, y/2, z/2]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have xlepi : x ≤ (π:ℝ) := by
    have yzp : y+z > 0 := by linarith
    linarith

  have ylepi : y ≤ (π:ℝ) := by
    have xzp : x+z > 0 := by linarith
    linarith

  have zlepi : z ≤ (π:ℝ) := by
    have xyp : x+y > 0 := by linarith
    linarith

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.Icc (-((π:ℝ) / 2)) ((π:ℝ) / 2) := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        apply And.intro (by linarith) (by linarith)

  have jensen_ineq : ∑ i : Fin 3, w i * Real.cos (S i) ≤ Real.cos (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_cos_Icc.concaveOn.le_map_sum w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq
  rw [← Real.cos_pi_div_six]
  have sum : 3⁻¹ * (x / 2) + 3⁻¹ * (y / 2) + 3⁻¹ * (z / 2) = (π:ℝ) / 6 := by linarith [k]
  rw [sum] at jensen_ineq

  nlinarith
