import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p3 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hxy : x + y ≤ 1) : 4 * x^2 + 4 * y^2 + (1 - x - y)^2 ≥ 2 / 3 := by
  have h1 : (4 * x^2 + 4 * y^2 + (1 - x - y)^2) * (1 / 4 + 1 / 4 + 1) ≥ 1 := by
    convert_to (∑ i : Fin 3, (![2 * x, 2 * y, 1 - x - y] i)^2) *
            (∑ i : Fin 3, (![1 / 2, 1 / 2, 1] i)^2) ≥
            (∑ i : Fin 3, ![2 * x, 2 * y, 1 - x - y] i * ![1 / 2, 1 / 2, 1] i)^2

    have g1 : (4 * x ^ 2 + 4 * y ^ 2 + (1 - x - y) ^ 2) * (1 / 4 + 1 / 4 + 1) =
    (∑ i : Fin 3, ![2 * x, 2 * y, 1 - x - y] i ^ 2) * ∑ i : Fin 3, ![1 / 2, 1 / 2, 1] i ^ 2 := by
      simp [Fin.sum_univ_three]
      ring
    exact g1

    have g2 : 1 = (∑ i : Fin 3, ![2 * x, 2 * y, 1 - x - y] i * ![1 / 2, 1 / 2, 1] i) ^ 2 := by
      simp [Fin.sum_univ_three]
      ring
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith
