import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p7 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 1) : 1 / (b + c + d) + 1 / (c + d + a) + 1 / (a + b + d) + 1 / (a + b + c) ≥ 16 / 3 := by
  have h1 : (3 * (a + b + c + d)) * (1 / (b + c + d) + 1 / (c + d + a) + 1 / (a + b + d) + 1 / (a + b + c)) ≥ 16 := by
    convert_to (∑ i : Fin 4, (![√(b + c + d), √(c + d + a), √(a + b + d), √(a + b + c)] i)^2) *
            (∑ i : Fin 4, (![√(1 / (b + c + d)), √(1 / (c + d + a)), √(1 / (a + b + d)), √(1 / (a + b + c))] i)^2) ≥
            (∑ i : Fin 4, ![√(b + c + d), √(c + d + a), √(a + b + d), √(a + b + c)] i * ![√(1 / (b + c + d)), √(1 / (c + d + a)), √(1 / (a + b + d)), √(1 / (a + b + c))] i)^2
    simp [Fin.sum_univ_four]
    field_simp; left; ring
    simp [Fin.sum_univ_four]
    field_simp [mul_assoc, mul_comm, mul_left_comm]
    norm_num
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith
