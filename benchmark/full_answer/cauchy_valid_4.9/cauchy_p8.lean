import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p8 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x * (x + y) + y * (y + z) + z * (z + x) = 1) : x / (x + y) + y / (y + z) + z / (z + x) ≥ (x + y + z) ^ 2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (x * (x + y) + y * (y + z) + z * (z + x)) * (x / (x + y) + y / (y + z) + z / (z + x)) ≥ (x + y + z)^2 := by
    convert_to (∑ i : Fin 3, (![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i)^2) *
            (∑ i : Fin 3, (![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i)^2) ≥
            (∑ i : Fin 3, ![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i * ![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i)^2

    have g1 : (x * (x + y) + y * (y + z) + z * (z + x)) * (x / (x + y) + y / (y + z) + z / (z + x)) =
    (∑ i : Fin 3, ![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i ^ 2) *
    ∑ i : Fin 3, ![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp [mul_assoc, mul_comm, mul_left_comm, sq]
    exact g1

    have g2 : (x + y + z) ^ 2 =
    (∑ i : Fin 3,
      ![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i * ![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i) ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp [mul_assoc, mul_comm, mul_left_comm]
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith

