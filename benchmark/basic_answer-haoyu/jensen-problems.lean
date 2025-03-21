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
        <;> positivity

  have jensen_ineq : (∑ i : Fin 2, w i * S i)^4 ≤ ∑ i : Fin 2, w i * S i ^ 4 := by
    apply (convexOn_pow 4).map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  nlinarith

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

  nlinarith

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

  nlinarith


theorem jensen_p4 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * x ^ ((1:ℝ)/2) + (3:ℝ)/8 * y ^ ((1:ℝ)/2) + (3:ℝ)/8 * z ^ ((1:ℝ)/2) ≤ ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) ^ ((1:ℝ)/2) := by
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

  have jensen_ineq : ∑ i : Fin 3, w i * (S i) ^ ((1:ℝ)/2) ≤ (∑ i : Fin 3, w i * S i) ^ ((1:ℝ)/2) := by
    apply (concaveOn_rpow (by positivity) (by norm_num)).le_map_sum w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  nlinarith

theorem jensen_p5 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * Real.log x + (3:ℝ)/8 * Real.log y + (3:ℝ)/8 * Real.log z ≤ Real.log ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) := by
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

  have s_pos : ∀ i ∈ Finset.univ, S i ∈ Set.Ioi 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : ∑ i : Fin 3, w i * Real.log (S i) ≤ Real.log (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_log_Ioi.concaveOn.le_map_sum w_nonneg w_sump s_pos

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  nlinarith
