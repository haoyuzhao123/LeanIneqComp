import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p6 (a b c : ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : ((b + c) + (c + a) + (a + b)) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ (1 + 1 + 1)^2 := by
    convert_to (∑ i : Fin 3, (![√(b + c), √(c + a), √(a + b)] i)^2) *
            (∑ i : Fin 3, (![√(1 / (b + c)), √(1 / (c + a)), √(1 / (a + b))] i)^2) ≥
            (∑ i : Fin 3, ![√(b + c), √(c + a), √(a + b)] i * ![√(1 / (b + c)), √(1 / (c + a)), √(1 / (a + b))] i)^2
    simp [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (a + b + c) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) = a / (b + c) + b / (c + a) + c / (a + b) + 3 := by
    field_simp
    ring
  linarith
