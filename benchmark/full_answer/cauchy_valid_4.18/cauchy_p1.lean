import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p1 (x y : ℝ) (h₂ : x > 0 ∧ y > 0) : ( x + y ) * ( 1 / x + 1 / y ) ≥ 4 := by
  have hx : x > 0 := h₂.1
  have hy : y > 0 := h₂.2
  convert_to (∑ i : Fin 2, (![√x, √y] i)^2) *
      (∑ i : Fin 2, (![1 / √x, 1 / √y] i)^2) ≥
      (∑ i : Fin 2, ![√x, √y] i * ![1 / √x, 1 / √y] i)^2
  simp [Fin.sum_univ_two]
  field_simp [sqrt_sq]
  simp [Fin.sum_univ_two]
  field_simp; norm_num
  apply Finset.sum_mul_sq_le_sq_mul_sq
