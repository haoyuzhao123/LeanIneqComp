import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p22 (a b c d e s : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)  (he : e > 0) (hs : s = a + b + c + d + e) : a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a)) ≥ 1 := by
  have h1 : (a + b + c + d + e)^2 * (a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a))) ≥ (a + b + c + d + e)^2 * 1 := by
    convert_to (∑ i : Fin 5, (![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i)^2) *
            (∑ i : Fin 5, (![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2) ≥
            (∑ i : Fin 5, ![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i * ![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2

    have g1 : (a + b + c + d + e)^2 * (a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a))) =
    (∑ i : Fin 5, (![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i)^2) *
    (∑ i : Fin 5, (![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2) := by
      simp [Fin.sum_univ_five]
      rw [hs]
      field_simp
      repeat rw [sq_sqrt]
      ring
      all_goals nlinarith
    exact g1

    have g2 : (a + b + c + d + e)^2 * 1 = (∑ i : Fin 5, ![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i * ![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2 := by
      simp [Fin.sum_univ_five]
      field_simp
      repeat rw [← mul_div, div_self, mul_one]
      all_goals rw [Real.sqrt_ne_zero']
      all_goals nlinarith
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq
  have hpos : (a + b + c + d + e)^2 > 0 := by nlinarith
  have hineq := (mul_le_mul_left hpos).mp h1
  exact hineq
