import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p1 (x y z: ℝ ) (h₁: x+ y + z = 3) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): (x * y * z) ^ (3⁻¹: ℝ ) ≤ 1 := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, z]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [h₂.1, h₂.2.1, h₂.2.2]

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

theorem amgm_p2 (x y: ℝ ) (h₁: x+ 2 * y = 3) (h₂ : x > 0 ∧ y> 0): (x * y ^ 2) ^ (3⁻¹: ℝ ) ≤ 1 := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, y]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [h₂.1, h₂.2]

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

  have h : (x * y * y) ^ (3⁻¹: ℝ ) = (x * y ^ 2) ^ (3⁻¹: ℝ ) := by ring
  linarith

theorem amgm_p3 (x y: ℝ ) (h₁: x+ 2 * y = 3) (h₂ : x > 0 ∧ y> 0): x * y ^ 2 ≤ 1 := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, y]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [h₂.1, h₂.2]

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

  have xyypos: x * y * y > 0 := mul_pos (mul_pos h₂.1 h₂.2) h₂.2
  have xyyonethird: (x * y * y) ^ (3⁻¹: ℝ ) ≤ 1 := by linarith
  have xyyonethird' : ((x * y * y) ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 1 ^ 3 := by gcongr

  calc x * y ^ 2 = x * y * y := by ring
    _ = ((x * y * y) ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [xyypos.le]
    _ ≤ 1 ^ 3 := xyyonethird'
    _ = 1 := by norm_num



theorem amgm_p4 (x y z: ℝ ) (h₁: x+ y + z = 3) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): x * y * z ≤ 1 := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, z]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [h₂.1, h₂.2.1, h₂.2.2]

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

  have xyzpos: x * y * z > 0 := mul_pos (mul_pos h₂.1 h₂.2.1) h₂.2.2
  have xyzonethird: (x * y * z) ^ (3⁻¹: ℝ ) ≤ 1 := by linarith
  have xyzonethird' : ((x * y * z) ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 1 ^ 3 := by gcongr

  calc x*y*z = ((x * y * z) ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [xyzpos.le]
    _ ≤ 1 ^ 3 := xyzonethird'
    _ = 1 := by norm_num

theorem amgm_p5 (x y z: ℝ ) (h₁: x+ 2 * y + 2 * z = 10) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): x * y ^ 2 * z ^ 2 ≤ 32 := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x, y, y, z, z]
  let w := ![1, 1, 1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [h₂.1, h₂.2.1, h₂.2.2]

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 5, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 5, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 5, (w i : ℝ) * S i) / (∑ i: Fin 5, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_five, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_five] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_five] at amgm

  have xyyzzpos: x * y * y * z * z > 0 := mul_pos (mul_pos (mul_pos (mul_pos h₂.1 h₂.2.1) h₂.2.1) h₂.2.2 ) h₂.2.2
  have xyyzzonefifth: (x * y * y * z * z) ^ (5⁻¹: ℝ ) ≤ 2 := by linarith
  have xyyzzonefifth' : ((x * y * y * z * z) ^ (5⁻¹: ℝ )) ^ 5 ≤ 2 ^ 5 := by gcongr

  calc x * y ^ 2 * z ^ 2 = x * y * y * z * z := by ring
    _ = ((x * y * y * z * z) ^ ((5:ℝ )⁻¹)) ^ 5 := by rw [← Real.rpow_natCast] ; simp [xyyzzpos.le]
    _ ≤ 2 ^ 5 := xyyzzonefifth'
    _ = 32 := by norm_num
