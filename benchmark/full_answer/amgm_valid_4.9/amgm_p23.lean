import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p23 (a b c d: ℝ)  (ap : a > 0)  (bp : b> 0) (cp : c> 0) ( dp : d> 0) (g : a * b * c * d = (1 : ℝ)) : (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a := by
  -- We first transform the problem into homogeneous inequality using xyz = 1
  -- Then we apply AM-GM inequaltiy
  have homo : (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a ^ 2 * b * c * d := by
    -- Step 1: Define the four numbers to apply AM-GM
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
