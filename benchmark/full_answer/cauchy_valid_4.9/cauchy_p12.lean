import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p12 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : 1 / (2 * x + y) + 3 / (x + y) = 2) : 6 * x + 5 * y ≥ 13 / 2 + 2 * √3 := by
  have h1 : (1 / (2 * x + y) + 3 / (x + y)) * (6 * x + 5 * y) ≥ 13 + 4 * √3 := by
    convert_to (∑ i : Fin 2, (![√(1 / (2 * x + y)), √(3 / (x + y))] i)^2) *
            (∑ i : Fin 2, (![√(2 * x + y), √(4 * x + 4 * y)] i)^2) ≥
            (∑ i : Fin 2, ![√(1 / (2 * x + y)), √(3 / (x + y))] i * ![√(2 * x + y), √(4 * x + 4 * y)] i)^2

    have g1 : (1 / (2 * x + y) + 3 / (x + y)) * (6 * x + 5 * y) =
    (∑ i : Fin 2, ![√(1 / (2 * x + y)), √(3 / (x + y))] i ^ 2) * ∑ i : Fin 2, ![√(2 * x + y), √(4 * x + 4 * y)] i ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp; left; ring
    exact g1

    have g2 : 13 + 4 * √3 = (∑ i : Fin 2, ![√(1 / (2 * x + y)), √(3 / (x + y))] i * ![√(2 * x + y), √(4 * x + 4 * y)] i) ^ 2 := by
      simp [Fin.sum_univ_three]
      have h_sq : √(4 * x + 4 * y) = 2 * √(x + y) := by
        calc √(4 * x + 4 * y) = Real.sqrt (4 * (x + y)) := by rw [mul_add]
        _ = Real.sqrt 4 * Real.sqrt (x + y) := by rw [Real.sqrt_mul (by linarith)]
        _ = 2 * Real.sqrt (x + y) := by
          have h10 : √4 = √(2^2) := by norm_num
          rw [h10, Real.sqrt_sq]
          norm_num
      field_simp [h_sq]
      ring_nf
      field_simp
      ring
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith
