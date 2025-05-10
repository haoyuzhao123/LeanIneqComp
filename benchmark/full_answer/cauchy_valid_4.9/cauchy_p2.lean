import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p2 (x y z: ℝ) (h₂ : x > 0 ∧ y > 0 ∧ z > 0 ) : ( x + y + z ) * ( 1 / x + 1 / y + 1 / z ) ≥ 9 := by
  have hx : x > 0 := h₂.1
  have hy : y > 0 := h₂.2.1
  have hz : z > 0 := h₂.2.2
  convert_to (∑ i : Fin 3, (![√x, √y, √z] i)^2) *
      (∑ i : Fin 3, (![1 / √x, 1 / √y, 1 / √z] i)^2) ≥
      (∑ i : Fin 3, ![√x, √y, √z] i * ![1 / √x, 1 / √y, 1 / √z] i)^2

  have g1 : (x + y + z) * (1 / x + 1 / y + 1 / z) =
    (∑ i : Fin 3, ![√x, √y, √z] i ^ 2) * ∑ i : Fin 3, ![1 / √x, 1 / √y, 1 / √z] i ^ 2 := by
    simp [Fin.sum_univ_three]
    field_simp [sqrt_sq]
  exact g1

  have g2 : 9 = (∑ i : Fin 3, ![√x, √y, √z] i * ![1 / √x, 1 / √y, 1 / √z] i) ^ 2 := by
    simp [Fin.sum_univ_three]
    field_simp; norm_num
  exact g2

  apply Finset.sum_mul_sq_le_sq_mul_sq
