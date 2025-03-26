import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p16 (x y a b: ℝ) (hy : y ≠ 0) (hb : b ≠ 0) (hxy : x^2 + 1 / y^2 = 1) (hab : a^2 + 1 / b^2 = 4) : |a / y + x / b| ≤ 2 := by
  have h1 : (x^2 + 1 / y^2) * (a^2 + 1 / b^2) ≥ (|a / y| + |x / b|)^2 := by
    convert_to (∑ i : Fin 2, (![(1 / |y|), |x|] i)^2) *
            (∑ i : Fin 2, (![|a|, (1 / |b|)] i)^2) ≥
            (∑ i : Fin 2, ![(1 / |y|), |x|] i * ![|a|, (1 / |b|)] i)^2
    simp [Fin.sum_univ_two]; left; ring
    simp [Fin.sum_univ_two]
    rw [abs_div, abs_div, inv_mul_eq_div, ← div_eq_mul_inv]
    apply Finset.sum_mul_sq_le_sq_mul_sq

  apply Real.sqrt_le_sqrt at h1
  rw [hxy, hab] at h1

  have h2 : √((|a / y| + |x / b|)^2) ≥ |a / y + x / b| := by
    rw [sqrt_sq]
    apply abs_add
    positivity

  apply le_trans h2
  have sqrt2 : √(1 * 4) = 2 := by
    rw [← sq_eq_sq, sq_sqrt]
    norm_num
    norm_num
    exact sqrt_nonneg _
    norm_num
  linarith
