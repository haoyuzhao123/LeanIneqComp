import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- 我没做出来的题
theorem cauchy_p21 (n : ℕ) (hn : n > 1) (a : Fin (n + 1) → ℝ) (ha : ∀ i, a i > 0) (h : a n = a 0) (hs : ∑ i : Fin n, a i = 1): ∑ i : Fin n, (a i)^2 / (a i + a (i + 1)) ≥ 1 / 2 := by
  have hsum : ∑ i : Fin n, a ↑↑i = 1 := hs
  convert_to ∑ i : Fin n, (a i)^2 / (a i + a (i + 1)) ≥ (∑ i : Fin n, a i)^2 / ∑ i : Fin n, (a i + a (i + 1))
  rw [Finset.sum_add_distrib, hsum]
  have hplus : ∑ i : Fin n, a (↑↑i + 1) = ∑ i : Fin n, a ↑↑i := by
    have h1 : a ↑(n - 1) = a (Fin.last (n - 1)) := by rw [Fin.val_last]
    have h2 : ∑ i : Fin ((n-1) +1), a (i) = ∑ i : Fin ((n-1)), a (i) + a (n-1) := by
      rw [Fin.sum_univ_castSucc]
      norm_num
      congr
      sorry
    sorry
  rw [hplus, hsum]
  norm_num
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  exact add_pos (ha i) (ha (i + 1))

-- original cauchy p9, move to hard / test 3
theorem cauchy_p9 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : √z * (√x + √y) + √x * (√y + √z) + √y * (√z + √x) = 1) : √z / (√x + √y) + √x / (√y + √z) + √y / (√z + √x) ≥ x + y + z + 2 * (√(x * y) + √(y * z) + √(z * x)) := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (√z * (√x + √y) + √x * (√y + √z) + √y * (√z + √x)) * (√z / (√x + √y) + √x / (√y + √z) + √y / (√z + √x)) ≥ (√x + √y + √z) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√(√z * (√x + √y)), √(√x * (√y + √z)), √(√y * (√z + √x))] i)^2) *
              (∑ i : Fin 3, (![√(√z / (√x + √y)), √(√x / (√y + √z)), √(√y / (√z + √x))] i)^2) ≥
              (∑ i : Fin 3, (![√(√z * (√x + √y)), √(√x * (√y + √z)), √(√y * (√z + √x))] i * ![√(√z / (√x + √y)), √(√x / (√y + √z)), √(√y / (√z + √x))] i))^2
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, sq]
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (√x + √y + √z) ^ 2 = x + y + z + 2 * (√(x * y) + √(y * z) + √(z * x)) := by
    ring
    field_simp [sq_sqrt]
    ring
  nlinarith


-- original cauchy p18, move to test 2 of original cauchy p18
theorem cauchy_p18  (x y z : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) (h : 1/x + 1/y + 1/z = 2) : Real.sqrt (x + y + z) ≥ Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) := by
  have hx1 : x - 1 > 0 := by linarith
  have hy1 : y - 1 > 0 := by linarith
  have hz1 : z - 1 > 0 := by linarith
  have h1 : ((x - 1) / x + (y - 1) / y + (z - 1) / z) * (x + y + z) ≥ (Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1)) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√((x - 1) / x), √((y - 1) / y), √((z - 1) / z)] i)^2) *
              (∑ i : Fin 3, (![√x, √y, √z] i)^2) ≥
              (∑ i : Fin 3, (![√((x - 1) / x), √((y - 1) / y), √((z - 1) / z)] i * ![√x, √y, √z] i))^2
    simp [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (x - 1) / x + (y - 1) / y + (z - 1) / z = 1 := by
    have key : ∀ a : ℝ, a^2 / (1 + a^2) = 1 - (1 / (1 + a^2)) :=
    λ a => by field_simp [← add_comm (a^2) 1]
    calc
      (x - 1) / x + (y - 1) / y + (z - 1) / z = 3 - (1/x + 1/y + 1/z) := by field_simp; ring
      _ = 1 := by rw [h]; norm_num
  rw [h2, one_mul] at h1
  apply Real.sqrt_le_sqrt at h1
  rw [Real.sqrt_sq (add_nonneg (add_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (y - 1))) (Real.sqrt_nonneg (z - 1)))] at h1
  exact h1


-- original cauchy p20, move to test 2 of modified cauchy p20
theorem cauchy_p20 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(3 * c + 1) ≤ 7 * √3 / 3 := by
  have h1 : 7 / 2 * (2 * (a + b + c) + 8 / 3) ≥ (√(2 * a + 1) + √(2 * b + 1) + √(3 * c + 1))^2 := by
    convert_to (∑ i : Fin 3, (![1, 1, √(3 / 2)] i)^2) *
            (∑ i : Fin 3, (![√(2 * a + 1), √(2 * b + 1), √(2 * c + 2 / 3)] i)^2) ≥
            (∑ i : Fin 3, ![1, 1, √(3 / 2)] i * ![√(2 * a + 1), √(2 * b + 1), √(2 * c + 2 / 3)] i)^2
    simp [Fin.sum_univ_three]
    field_simp; ring
    simp [Fin.sum_univ_three]
    have g : √(3 * c + 1) = √3 / √2 * √(2 * c + 2 / 3) := by
      field_simp
      rw [← sqrt_mul] <;> ring_nf <;> norm_num
      rw [← sqrt_mul] <;> ring_nf
      rw [← sqrt_mul] <;> ring_nf
      norm_num
      linarith
    rw [g]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h] at h1
  norm_num at h1
  apply Real.sqrt_le_sqrt at h1
  rw [Real.sqrt_sq (add_nonneg (add_nonneg (Real.sqrt_nonneg (2 * a + 1)) (Real.sqrt_nonneg (2 * b + 1))) (Real.sqrt_nonneg (3 * c + 1)))] at h1
  have g0 : √(49 / 3) = 7 * √3 / 3 := by
    field_simp
    simp [mul_assoc, Real.mul_self_sqrt]
    norm_num
  rw [← g0]
  exact h1


-- original cauchy p23, move to test 2 of modified cauchy p23
theorem cauchy_p23 (x y z: ℝ) (h : x^2 + 2 * y^2 + 4 * z^2 > 0) : (x + y + z) / √(x^2 + 2 * y^2 + 4 * z^2) ≤ √7 / 2 := by
  have h1 : (x^2 + 2 * y^2 + 4 * z^2) * (1 + 1/2 + 1/4) ≥ (x + y + z)^2 := by
    convert_to (∑ i : Fin 3, (![x^2, 2 * y^2, 4 * z^2] i)) *
            (∑ i : Fin 3, (![1, 1/2, 1/4] i)) ≥
            (∑ i : Fin 3, ![x, y, z] i)^2
    simp [Fin.sum_univ_three]
    simp [Fin.sum_univ_three]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> norm_num
    intro i _
    fin_cases i <;> field_simp
  norm_num at h1
  have h_frac : (x + y + z)^2 / (x^2 + 2 * y^2 + 4 * z^2) ≤ 7 / 4 := by
    rw [mul_comm] at h1
    rw [div_le_iff₀]
    exact h1
    exact h
  apply Real.sqrt_le_sqrt at h_frac
  rw [sqrt_div] at h_frac
  have h_sq : (x + y + z) ≤ √((x + y + z) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h_xyz : (x + y + z) / √(x ^ 2 + 2 * y ^ 2 + 4 * z ^ 2) ≤ √(7 / 4) := by
    apply le_trans _ h_frac
    apply div_le_div_of_nonneg_right h_sq (sqrt_nonneg _)
  have h_norm : √(7 / 4) = √7 / 2 := by norm_num
  linarith
  exact sq_nonneg _
