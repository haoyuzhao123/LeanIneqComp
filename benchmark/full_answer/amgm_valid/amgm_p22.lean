import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p22 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0) (g : x * y * z = (1 : ℝ)) : (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x := by
  -- We first transform the problem into homogeneous inequality using xyz = 1
  -- Then we apply AM-GM inequaltiy
  have homo : (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x ^ 2 * y * z := by
    -- Step 1: Define the three numbers to apply AM-GM
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
