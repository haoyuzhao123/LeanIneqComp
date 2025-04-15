import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p9 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) ( g : z * (x + y) + x * (y + z) + y * (z + x) = 1) : z / (x + y) + x / (y + z) + y / (z + x) ≥ (x + y + z) ^ 2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (z * (x + y) + x * (y + z) + y * (z + x)) * (z / (x + y) + x / (y + z) + y / (z + x)) ≥ (x + y + z) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i)^2) *
              (∑ i : Fin 3, (![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i)^2) ≥
              (∑ i : Fin 3, (![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i * ![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i))^2

    have g1 : (z * (x + y) + x * (y + z) + y * (z + x)) * (z / (x + y) + x / (y + z) + y / (z + x)) =
    (∑ i : Fin 3, ![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i ^ 2) *
    ∑ i : Fin 3, ![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp [mul_assoc, mul_comm, mul_left_comm, sq]
    exact g1

    have g2 : (x + y + z) ^ 2 = (∑ i : Fin 3,
      ![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i * ![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i) ^ 2 := by
      simp [Fin.sum_univ_three]
      field_simp [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm]
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith
