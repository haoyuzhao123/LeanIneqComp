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

theorem amgm_p8 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (2:ℝ) / 5 * x ^ 5 + (2:ℝ) / 5 * y ^ 5 + (1:ℝ) / 5 * z ^ 5 ≥ x^2 * y^2 * z := by
  -- Step 1: Define the three numbers to apply AM-GM
  let S := ![x^5, x^5, y^5, y^5, z^5]
  let w := ![1, 1, 1, 1, 1]

  have x2p : 0 < x ^ 2 := by nlinarith
  have x4p : 0 < x ^ 4 := by nlinarith
  have x5p : 0 < x ^ 5 := by nlinarith
  have x10p : 0 < x ^ 10 := by nlinarith
  have y2p : 0 < y ^ 2 := by nlinarith
  have y4p : 0 < y ^ 4 := by nlinarith
  have y5p : 0 < y ^ 5 := by nlinarith
  have y10p : 0 < y ^ 10 := by nlinarith
  have z2p : 0 < z ^ 2 := by nlinarith
  have z4p : 0 < z ^ 4 := by nlinarith
  have z5p : 0 < z ^ 5 := by nlinarith

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        linarith

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


  have xtrans : (x ^ 10) ^ (5⁻¹: ℝ ) = x ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.1) ]
    norm_num

  have ytrans : (y ^ 10 )^ (5⁻¹: ℝ ) = y ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt h.2.1)]
    norm_num

  have ztrans : (z ^ 5 )^ (5⁻¹: ℝ ) = z := by
    rw [← Real.rpow_natCast]
    simp [Real.rpow_mul, h.2.2.le]

  calc 2 / 5 * x ^ 5 + 2 / 5 * y ^ 5 + 1 / 5 * z ^ 5 = ( x ^ 5 + x ^ 5 + y ^ 5 + y ^ 5 + z ^ 5) / 5 := by ring
    _ ≥ (x ^ 5 * x ^ 5 * y ^ 5 * y ^ 5 * z ^ 5) ^ (5⁻¹: ℝ ) := by apply amgm
    _ = (x ^ 10 * y ^ 10 * z ^ 5) ^ (5⁻¹: ℝ ) := by ring
    _ = (x ^ 10 * y ^ 10) ^ (5⁻¹: ℝ ) * (z ^ 5) ^ (5⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = (x ^ 10 )^ (5⁻¹: ℝ ) * (y ^ 10) ^ (5⁻¹: ℝ ) * (z ^ 5) ^ (5⁻¹: ℝ ) := by rw [mul_rpow (by positivity) (by positivity)]
    _ = x ^ 2 * y ^ 2 * z := by rw [xtrans, ytrans, ztrans]


theorem amgm_p9 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0) (g : x * y * z = (1 : ℝ)) : (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x := by
  -- We first transform the problem into homogeneous inequality using xyz = 1
  -- Then we apply AM-GM inequaltiy
  have homo : (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x ^ 2 * y * z := by
    -- Step 1: Define the seven numbers to apply AM-GM
    let S := ![x^3 * y, y^3 * z, z^3 * x]
    let w := ![(4:ℝ) / 7, (1:ℝ) / 7, (2:ℝ) / 7]

    have xp : 0 < x := by linarith
    have yp : 0 < y := by linarith
    have zp : 0 < z := by linarith
    have x2p : 0 < x ^ 2 := by nlinarith
    have y2p : 0 < y ^ 2 := by nlinarith
    have z2p : 0 < z ^ 2 := by nlinarith
    have x3p : 0 < x ^ 3 := by nlinarith
    have y3p : 0 < y ^ 3 := by nlinarith
    have z3p : 0 < z ^ 3 := by nlinarith
    have x3yp : 0 < x ^ 3 * y := by nlinarith
    have y3zp : 0 < y ^ 3 * z := by nlinarith
    have z3xp : 0 < z ^ 3 * x := by nlinarith

    have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        nlinarith

    have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

    have w_sump : 0 < ∑ i : Fin 3, w i := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

    -- Apply AM-GM inequality
    have amgm : (∏ i : Fin 3, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 3, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 3, (w i : ℝ) * S i) / (∑ i: Fin 3, (w i : ℝ)) := by
      apply Real.geom_mean_le_arith_mean
      exact w_nonneg
      exact w_sump
      exact h_nonneg

    simp [S] at amgm
    simp [w] at amgm
    simp [Fin.sum_univ_three] at amgm
    norm_num at amgm
    simp [Fin.prod_univ_three] at amgm

    have xtrans : (x ^ 3) ^ ((4 : ℝ) / 7) * x ^ ((2 : ℝ) / 7) = x ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt h.1) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have ytrans : y^ ((4 : ℝ) / 7) * (y ^ 3) ^ ((1 : ℝ) / 7) = y := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt h.2.1) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have ztrans : z ^ ((1 : ℝ) / 7) * (z ^ 3) ^ ((2 : ℝ) / 7) = z := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt h.2.2) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have transform : (x ^ 3 * y) ^ ((4 : ℝ) / 7) * (y ^ 3 * z) ^ ((1 : ℝ) / 7) * (z ^ 3 * x) ^ ((2 : ℝ) / 7) = x ^ 2 * y * z := by
      calc (x ^ 3 * y) ^ ((4 : ℝ) / 7) * (y ^ 3 * z) ^ ((1 : ℝ) / 7) * (z ^ 3 * x) ^ ((2 : ℝ) / 7) = (x ^ 3) ^ ((4 : ℝ) / 7) * y^ ((4 : ℝ) / 7) * (y ^ 3 * z) ^ ((1 : ℝ) / 7) * (z ^ 3 * x) ^ ((2 : ℝ) / 7) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = (x ^ 3) ^ ((4 : ℝ) / 7) * y^ ((4 : ℝ) / 7) * ((y ^ 3) ^ ((1 : ℝ) / 7) * z ^ ((1 : ℝ) / 7)) * (z ^ 3 * x) ^ ((2 : ℝ) / 7) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = (x ^ 3) ^ ((4 : ℝ) / 7) * y^ ((4 : ℝ) / 7) * ((y ^ 3) ^ ((1 : ℝ) / 7) * z ^ ((1 : ℝ) / 7)) * ((z ^ 3) ^ ((2 : ℝ) / 7) * x ^ ((2 : ℝ) / 7)) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = ((x ^ 3) ^ ((4 : ℝ) / 7) * x ^ ((2 : ℝ) / 7)) * (y^ ((4 : ℝ) / 7) * (y ^ 3) ^ ((1 : ℝ) / 7)) * (z ^ ((1 : ℝ) / 7) * (z ^ 3) ^ ((2 : ℝ) / 7)) := by ring
        _ = x^2 * y * z := by rw [xtrans, ytrans, ztrans]


    calc (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ (x ^ 3 * y) ^ ((4 : ℝ) / 7) * (y ^ 3 * z) ^ ((1 : ℝ) / 7) * (z ^ 3 * x) ^ ((2 : ℝ) / 7) := by nlinarith
      _ = x ^ 2 * y * z := by rw [transform]

  calc (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x ^ 2 * y * z := homo
    _ = x * (x * y * z) := by ring
    _ = x := by rw [g] ; simp

theorem amgm_p10 (a b c d: ℝ)  (ap : a > 0)  (bp : b> 0) (cp : c> 0) ( dp : d> 0) (g : a * b * c * d = (1 : ℝ)) : (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a := by
  -- We first transform the problem into homogeneous inequality using xyz = 1
  -- Then we apply AM-GM inequaltiy
  have homo : (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a ^ 2 * b * c * d := by
    -- Step 1: Define the seven numbers to apply AM-GM
    let S := ![a^4 * b, b^4 * c, c^4 * d, d^4 * a]
    let w := ![(23:ℝ) / 51, (7:ℝ) / 51, (11:ℝ) / 51, (10:ℝ) / 51]

    have a2p : 0 < a ^ 2 := by nlinarith
    have b2p : 0 < b ^ 2 := by nlinarith
    have c2p : 0 < c ^ 2 := by nlinarith
    have d2p : 0 < d ^ 2 := by nlinarith
    have a4p : 0 < a ^ 4 := by nlinarith
    have b4p : 0 < b ^ 4 := by nlinarith
    have c4p : 0 < c ^ 4 := by nlinarith
    have d4p : 0 < d ^ 4 := by nlinarith
    have a4bp : 0 < a ^ 4 * b := by nlinarith
    have b4cp : 0 < b ^ 4 * c := by nlinarith
    have c4dp : 0 < c ^ 4 * d := by nlinarith
    have d4ap : 0 < d ^ 4 * a := by nlinarith

    have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        nlinarith

    have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

    have w_sump : 0 < ∑ i : Fin 4, w i := by
      simp [w]
      simp [Fin.sum_univ_four]
      norm_num

    -- Apply AM-GM inequality
    have amgm : (∏ i : Fin 4, S i ^ (w i : ℝ)) ^ ((∑ i : Fin 4, (w i : ℝ))⁻¹) ≤ (∑ i : Fin 4, (w i : ℝ) * S i) / (∑ i: Fin 4, (w i : ℝ)) := by
      apply Real.geom_mean_le_arith_mean
      exact w_nonneg
      exact w_sump
      exact h_nonneg

    simp [S] at amgm
    simp [w] at amgm
    simp [Fin.sum_univ_four] at amgm
    norm_num at amgm
    simp [Fin.prod_univ_four] at amgm

    have atrans : (a ^ 4) ^ ((23:ℝ) / 51) * a ^ ((10:ℝ) / 51) = a ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt ap) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have btrans : (b ^ 4)^ ((7:ℝ) / 51) * b ^ ((23:ℝ) / 51) = b := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt bp) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have ctrans : c ^ ((7:ℝ) / 51) * (c ^ 4) ^ ((11:ℝ) / 51) = c := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt cp) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity

    have dtrans : d ^ ((11:ℝ) / 51) * (d ^ 4) ^ ((10:ℝ) / 51) = d := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt dp) ]
      norm_num
      rw [← Real.rpow_add ]
      norm_num
      positivity


    have transform : (a ^ 4 * b) ^ ((23:ℝ) / 51) * (b ^ 4 * c) ^ ((7:ℝ) / 51) * (c ^ 4 * d) ^ ((11:ℝ) / 51) * (d ^ 4 * a) ^ ((10:ℝ) / 51) = a ^ 2 * b * c * d := by
      calc (a ^ 4 * b) ^ ((23:ℝ) / 51) * (b ^ 4 * c) ^ ((7:ℝ) / 51) * (c ^ 4 * d) ^ ((11:ℝ) / 51) * (d ^ 4 * a) ^ ((10:ℝ) / 51) = ((a ^ 4) ^ ((23:ℝ) / 51) * b ^ ((23:ℝ) / 51)) * (b ^ 4 * c) ^ ((7:ℝ) / 51) * (c ^ 4 * d) ^ ((11:ℝ) / 51) * (d ^ 4 * a) ^ ((10:ℝ) / 51) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = ((a ^ 4) ^ ((23:ℝ) / 51) * b ^ ((23:ℝ) / 51)) * ((b ^ 4 ) ^ ((7:ℝ) / 51) * c ^ ((7:ℝ) / 51)) * (c ^ 4 * d) ^ ((11:ℝ) / 51) * (d ^ 4 * a) ^ ((10:ℝ) / 51) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = ((a ^ 4) ^ ((23:ℝ) / 51) * b ^ ((23:ℝ) / 51)) * ((b ^ 4 ) ^ ((7:ℝ) / 51) * c ^ ((7:ℝ) / 51)) * ((c ^ 4) ^ ((11:ℝ) / 51) * d ^ ((11:ℝ) / 51)) * (d ^ 4 * a) ^ ((10:ℝ) / 51) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = ((a ^ 4) ^ ((23:ℝ) / 51) * b ^ ((23:ℝ) / 51)) * ((b ^ 4 ) ^ ((7:ℝ) / 51) * c ^ ((7:ℝ) / 51)) * ((c ^ 4) ^ ((11:ℝ) / 51) * d ^ ((11:ℝ) / 51)) * ((d ^ 4) ^ ((10:ℝ) / 51) * a ^ ((10:ℝ) / 51)) := by rw [mul_rpow (by positivity) (by positivity)]
        _ = ((a ^ 4) ^ ((23:ℝ) / 51) * a ^ ((10:ℝ) / 51)) * ((b ^ 4)^ ((7:ℝ) / 51) * b ^ ((23:ℝ) / 51)) * (c ^ ((7:ℝ) / 51) * (c ^ 4) ^ ((11:ℝ) / 51)) * (d ^ ((11:ℝ) / 51) * (d ^ 4) ^ ((10:ℝ) / 51)) := by ring
        _ = a ^ 2 * b * c * d := by rw [atrans, btrans, ctrans, dtrans]


    calc (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ (a ^ 4 * b) ^ ((23:ℝ) / 51) * (b ^ 4 * c) ^ ((7:ℝ) / 51) * (c ^ 4 * d) ^ ((11:ℝ) / 51) * (d ^ 4 * a) ^ ((10:ℝ) / 51) := by nlinarith
      _ = a ^ 2 * b * c * d := by rw [transform]

  calc (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a ^ 2 * b * c * d := homo
    _ = a * (a * b * c * d) := by ring
    _ = a := by rw [g] ; simp
