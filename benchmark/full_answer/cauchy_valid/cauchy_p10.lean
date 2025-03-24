import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p10 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : √(2 * x + 1) + √(2 * y + 3) = 4) : x + y ≥ 2 := by
  have h1 : (2 * (x + y) + 4) * 2 ≥ (√(2 * x + 1) + √(2 * y + 3))^2 := by
    convert_to (∑ i : Fin 2, (![√(2 * x + 1), √(2 * y + 3)] i)^2) *
            (∑ i : Fin 2, (![1, 1] i)^2) ≥
            (∑ i : Fin 2, ![√(2 * x + 1), √(2 * y + 3)] i * ![1, 1] i)^2
    simp [Fin.sum_univ_two]
    rw [sq_sqrt, sq_sqrt]
    ring
    linarith
    linarith
    simp [Fin.sum_univ_two]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [g] at h1
  nlinarith
