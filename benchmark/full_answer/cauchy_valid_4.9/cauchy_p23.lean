import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p23 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : x^2 + y^2 / 2 = 1) : x + √(2 + 3 * y^2) ≤ 2 * √21 / 3 := by
  have h1 : (x^2 + y^2 / 2 + 1 / 3) * 7 ≥ (x + √(2 + 3 * y^2))^2 := by
    convert_to (∑ i : Fin 2, (![x, √(y^2 / 2 + 1 / 3)] i)^2) *
            (∑ i : Fin 2, (![1, √6] i)^2) ≥
            (∑ i : Fin 2, ![x, √(y^2 / 2 + 1 / 3)] i * ![1, √6] i)^2
    simp [Fin.sum_univ_two]
    rw [sq_sqrt]
    ring
    nlinarith
    simp [Fin.sum_univ_two]
    have h_sqrt : √(2 + 3 * y ^ 2) = √(y ^ 2 / 2 + 3⁻¹) * √6 := by
      calc
        √(2 + 3 * y ^ 2) = √((y ^ 2 / 2 + 3⁻¹) * 6) := by
          congr;
          field_simp
          ring
        _ = √(y ^ 2 / 2 + 3⁻¹) * √6 := by rw [sqrt_mul (by positivity)]
    rw [h_sqrt]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [g] at h1
  apply Real.sqrt_le_sqrt at h1
  rw [Real.sqrt_sq] at h1
  have h_num : √((1 + 1 / 3) * 7) = 2 * √21 / 3 := by
    rw [← sq_eq_sq]
    ring_nf; rw [sq_sqrt, sq_sqrt]; norm_num
    norm_num; norm_num
    exact Real.sqrt_nonneg ((1 + 1 / 3) * 7)
    exact div_nonneg (by linarith [Real.sqrt_nonneg 21]) (by norm_num)
  rw [h_num] at h1
  exact h1
  nlinarith [Real.sqrt_nonneg (2 + 3 * y ^ 2)]
