import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p17 (a b c d e : ℝ) (h : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - e)^2 = 1) : a - 2 * b - c + 2 * e ≤ √10 := by
  let x := a - b
  let y := b - c
  let z := c - d
  let w := d - e
  have h0 : x^2 + y^2 + z^2 + w^2 = 1 := h
  have h1 : a - 2 * b - c + 2 * e = x - y - 2 * z - 2 * w := by ring

  have h2 : (x^2 + y^2 + z^2 + w^2) * 10 ≥ (|x| + |y| + 2 * |z| + 2 * |w|)^2 := by
    convert_to (∑ i : Fin 4, (![|x|, |y|, |z|, |w|] i)^2) *
            (∑ i : Fin 4, (![1, 1, 2, 2] i)^2) ≥
            (∑ i : Fin 4, ![|x|, |y|, |z|, |w|] i * ![1, 1, 2, 2] i)^2

    have g1 : (x^2 + y^2 + z^2 + w^2) * 10 = (∑ i : Fin 4, (![|x|, |y|, |z|, |w|] i)^2) * (∑ i : Fin 4, (![1, 1, 2, 2] i)^2) := by
      simp [Fin.sum_univ_four]
      left; norm_num
    exact g1

    have g2 : (|x| + |y| + 2 * |z| + 2 * |w|) ^ 2 = (∑ i : Fin 4, ![|x|, |y|, |z|, |w|] i * ![1, 1, 2, 2] i) ^ 2 := by
      simp [Fin.sum_univ_four]
      ring
    exact g2

    apply Finset.sum_mul_sq_le_sq_mul_sq

  apply Real.sqrt_le_sqrt at h2
  rw [h0, one_mul] at h2

  have h3 : √((|x| + |y| + 2 * |z| + 2 * |w|)^2) ≥ x - y - 2 * z - 2 * w := by
    rw [sqrt_sq]
    have : x ≤ |x| := le_abs_self x
    have : -y ≤ |y| := neg_le_abs y
    have : -2 * z ≤ 2 * |z| := by linarith [neg_le_abs z]
    have : -2 * w ≤ 2 * |w| := by linarith [neg_le_abs w]
    linarith

    have nonneg : 0 ≤ |x| + |y| + 2 * |z| + 2 * |w| := by
      apply add_nonneg
      · apply add_nonneg;
        · exact add_nonneg (abs_nonneg x) (abs_nonneg y)
        · exact mul_nonneg (by norm_num) (abs_nonneg z)
      · exact mul_nonneg (by norm_num) (abs_nonneg w)
    exact nonneg

  rw [← h1] at h3
  linarith
