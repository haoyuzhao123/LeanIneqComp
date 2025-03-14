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

  calc x*y^2*z^2 = x * y * y * z * z := by ring
    _ = ((x * y * y * z * z) ^ ((5:ℝ )⁻¹)) ^ 5 := by rw [← Real.rpow_natCast] ; simp [xyyzzpos.le]
    _ ≤ 2 ^ 5 := xyyzzonefifth'
    _ = 32 := by norm_num

theorem amgm_p6 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x ^ 3 + (1:ℝ) / 3 * y ^ 3  ≥ x^2 * y := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^3, x^3, y^3]
  let w := ![1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        nlinarith [ sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]

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

  have x2p : 0 < x ^ 2 := by nlinarith
  have x3p : 0 < x ^ 3 := by nlinarith
  have x6p : 0 < x ^ 6 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y3p : 0 < y ^ 3 := by nlinarith

  have xtrans : (x ^ 6) ^ (3⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 3 )^ (3⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.le]

  calc 2 / 3 * x ^ 3 + 1 / 3 * y ^ 3 = ( x ^ 3 + x ^ 3 + y ^ 3 ) / 3 := by ring
    _ ≥ (x ^ 3 * x ^ 3 * y ^ 3 ) ^ (3⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 6 * y ^ 3) ^ (3⁻¹: ℝ ) := by ring
    _ = (x ^ 6) ^ (3⁻¹: ℝ ) * (y ^ 3 )^ (3⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y := by rw [xtrans, ytrans]

theorem amgm_p7 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (1:ℝ) / 2 * x ^ 4 + (1:ℝ) / 4 * y ^ 4 + (1:ℝ) / 4 * z ^ 4 ≥ x^2 * y * z := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^4, x^4, y^4, z^4]
  let w := ![1, 1, 1, 1]

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith [ sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]

  -- Apply AM-GM inequality
  have amgm : (∏ i : Fin 4, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 4, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 4, (w i : ℝ) * S i) / (∑ i: Fin 4, (w i : ℝ)) := by
    apply Real.geom_mean_le_arith_mean
    field_simp
    simp [Fin.sum_univ_four, w]
    norm_num
    exact h_nonneg

  simp [S] at amgm
  simp [w] at amgm
  simp [Fin.sum_univ_four] at amgm
  norm_num at amgm
  simp [Fin.prod_univ_four] at amgm

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x8p : 0 < x ^ 8 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith

  have xtrans : (x ^ 8) ^ (4⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 4 )^ (4⁻¹: ℝ ) = y := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.1.le]

  have ztrans : (z ^ 4 )^ (4⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.2.le]

  calc 1 / 2 * x ^ 4 + 1 / 4 * y ^ 4 + 1 / 4 * z ^ 4 = ( x ^ 4 + x ^ 4 + y ^ 4 + z ^ 4) / 4 := by ring
    _ ≥ (x ^ 4 * x ^ 4 * y ^ 4 * z ^ 4) ^ (4⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 8 * y ^ 4 * z ^ 4) ^ (4⁻¹: ℝ ) := by ring
    _ = (x ^ 8 * y ^ 4) ^ (4⁻¹: ℝ ) * (z ^ 4) ^ (4⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = (x ^ 8 )^ (4⁻¹: ℝ ) * (y ^ 4) ^ (4⁻¹: ℝ ) * (z ^ 4) ^ (4⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y * z := by rw [xtrans, ytrans, ztrans]
