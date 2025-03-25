import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p5 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x + y + z = 3) : 4 / x + 1 / y + 9 / z ≥ 12 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (x + y + z) * (4 / x + 1 / y + 9 / z) ≥ 36 := by
    convert_to (∑ i : Fin 3, (![√(x), √(y), √(z)] i)^2) *
            (∑ i : Fin 3, (![√(4 / x), √(1 / y), √(9 / z)] i)^2) ≥
            (∑ i : Fin 3, ![√(x), √(y), √(z)] i * ![√(4 / x), √(1 / y), √(9 / z)] i)^2
    simp [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three]
    field_simp
    have h11 : √4 = 2 := by
      have h10 : √4 = √(2^2) := by norm_num
      rw [h10, Real.sqrt_sq]
      norm_num
    have h12 : Real.sqrt 9 = 3 := by
      have h20 : √9 = √(3^2) := by norm_num
      rw [h20, Real.sqrt_sq]
      norm_num
    simp [h11, h12]
    norm_num
    rw [ge_iff_le]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith
