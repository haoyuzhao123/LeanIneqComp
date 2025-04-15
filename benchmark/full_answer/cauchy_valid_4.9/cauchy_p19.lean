import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p19 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2) = 2) : x^2 + y^2 + z^2 + 3 ≥ (x + y + z)^2 := by
  have h1 : (x^2 / (1 + x^2) + y^2 / (1 + y^2) + z^2 / (1 + z^2)) * (x^2 + y^2 + z^2 + 3) ≥ (x + y + z) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i)^2) *
              (∑ i : Fin 3, (![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i)^2) ≥
              (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i * ![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i))^2

    have g1 : (x^2 / (1 + x^2) + y^2 / (1 + y^2) + z^2 / (1 + z^2)) * (x^2 + y^2 + z^2 + 3) =
    (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i)^2) * (∑ i : Fin 3, (![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i)^2) := by
      simp [Fin.sum_univ_three]
      field_simp; left; ring
    exact g1

    have g2 : (x + y + z) ^ 2 = (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i * ![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i))^2 := by
      simp [Fin.sum_univ_three]
      field_simp [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm]
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  have h2 : x^2 / (1 + x^2) + y^2 / (1 + y^2) + z^2 / (1 + z^2) = 1 := by
    have key : ∀ a : ℝ, a^2 / (1 + a^2) = 1 - (1 / (1 + a^2)) :=
    λ a => by field_simp [← add_comm (a^2) 1]
    calc
      (x^2 / (1 + x^2)) + (y^2 / (1 + y^2)) + (z^2 / (1 + z^2)) = (1 - (1 / (1 + x^2))) + (1 - (1 / (1 + y^2))) + (1 - (1 / (1 + z^2))) := by rw [key x, key y, key z]
      _ = 3 - (1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2)) := by ring
      _ = 1 := by rw [h]; norm_num
  nlinarith
