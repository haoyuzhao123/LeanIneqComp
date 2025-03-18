import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p1 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hxy : x + y ≤ 1) : 4 * x^2 + 4 * y^2 + (1 - x - y)^2 ≥ 2 / 3 := by
  have h1 : (4 * x^2 + 4 * y^2 + (1 - x - y)^2) * (1 / 4 + 1 / 4 + 1) ≥ 1 := by
    convert_to (∑ i : Fin 3, (![2 * x, 2 * y, 1 - x - y] i)^2) *
            (∑ i : Fin 3, (![1 / 2, 1 / 2, 1] i)^2) ≥
            (∑ i : Fin 3, ![2 * x, 2 * y, 1 - x - y] i * ![1 / 2, 1 / 2, 1] i)^2
    simp [Fin.sum_univ_three]
    ring
    simp [Fin.sum_univ_three]
    ring
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p2 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hx1 : x ≤ 1) (hy1 : y ≤ 1) : x * √(1 - y^2) + y * √(1 - x^2) ≤ 1 := by
  apply le_of_sq_le_sq
  convert_to (∑ i : Fin 2, ![x, √(1 - x^2)] i * ![√(1 - y^2), y] i)^2 ≤
          (∑ i : Fin 2, (![x, √(1 - x^2)] i)^2) *
          (∑ i : Fin 2, (![√(1 - y^2), y] i)^2)
  simp [Fin.sum_univ_two]
  field_simp; rw [mul_comm]
  simp [Fin.sum_univ_two]
  rw [sq_sqrt, sq_sqrt]
  ring
  nlinarith; nlinarith
  apply Finset.sum_mul_sq_le_sq_mul_sq
  norm_num


theorem cauchy_p3 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x + y + z = 3) : 4 / x + 1 / y + 9 / z ≥ 12 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (x + y + z) * (4 / x + 1 / y + 9 / z) ≥ 36 := by
    convert_to (∑ i : Fin 3, (![√(x), √(y), √(z)] i)^2) *
            (∑ i : Fin 3, (![√(4 / x), √(1 / y), √(9 / z)] i)^2) ≥
            (∑ i : Fin 3, ![√(x), √(y), √(z)] i * ![√(4 / x), √(1 / y), √(9 / z)] i)^2
    simp [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three]
    field_simp
    norm_num
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p4 (a b c : ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : ((b + c) + (c + a) + (a + b)) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ (1 + 1 + 1)^2 := by
    convert_to (∑ i : Fin 3, (![√(b + c), √(c + a), √(a + b)] i)^2) *
            (∑ i : Fin 3, (![√(1 / (b + c)), √(1 / (c + a)), √(1 / (a + b))] i)^2) ≥
            (∑ i : Fin 3, ![√(b + c), √(c + a), √(a + b)] i * ![√(1 / (b + c)), √(1 / (c + a)), √(1 / (a + b))] i)^2
    simp [Fin.sum_univ_three]
    field_simp
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (a + b + c) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) = a / (b + c) + b / (c + a) + c / (a + b) + 3 := by
    field_simp
    ring
  linarith


theorem cauchy_p5 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 1) : 1 / (b + c + d) + 1 / (c + d + a) + 1 / (a + b + d) + 1 / (a + b + c) ≥ 16 / 3 := by
  have h1 : (3 * (a + b + c + d)) * (1 / (b + c + d) + 1 / (c + d + a) + 1 / (a + b + d) + 1 / (a + b + c)) ≥ 16 := by
    convert_to (∑ i : Fin 4, (![√(b + c + d), √(c + d + a), √(a + b + d), √(a + b + c)] i)^2) *
            (∑ i : Fin 4, (![√(1 / (b + c + d)), √(1 / (c + d + a)), √(1 / (a + b + d)), √(1 / (a + b + c))] i)^2) ≥
            (∑ i : Fin 4, ![√(b + c + d), √(c + d + a), √(a + b + d), √(a + b + c)] i * ![√(1 / (b + c + d)), √(1 / (c + d + a)), √(1 / (a + b + d)), √(1 / (a + b + c))] i)^2
    simp [Fin.sum_univ_four]
    field_simp; left; ring
    simp [Fin.sum_univ_four]
    field_simp [mul_assoc, mul_comm, mul_left_comm]
    norm_num
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p6 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x * (x + y) + y * (y + z) + z * (z + x) = 1) : x / (x + y) + y / (y + z) + z / (z + x) ≥ (x + y + z) ^ 2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (x * (x + y) + y * (y + z) + z * (z + x)) * (x / (x + y) + y / (y + z) + z / (z + x)) ≥ (x + y + z)^2 := by
    convert_to (∑ i : Fin 3, (![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i)^2) *
            (∑ i : Fin 3, (![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i)^2) ≥
            (∑ i : Fin 3, ![√(x * (x + y)), √(y * (y + z)), √(z * (z + x))] i * ![√(x / (x + y)), √(y / (y + z)), √(z / (z + x))] i)^2
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, sq]
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p7 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) ( g : z * (x + y) + x * (y + z) + y * (z + x) = 1) : z / (x + y) + x / (y + z) + y / (z + x) ≥ (x + y + z) ^ 2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have h1 : (z * (x + y) + x * (y + z) + y * (z + x)) * (z / (x + y) + x / (y + z) + y / (z + x)) ≥ (x + y + z) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i)^2) *
              (∑ i : Fin 3, (![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i)^2) ≥
              (∑ i : Fin 3, (![√(z * (x + y)), √(x * (y + z)), √(y * (z + x))] i * ![√(z / (x + y)), √(x / (y + z)), √(y / (z + x))] i))^2
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, sq]
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith

theorem cauchy_p8 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : √(2 * x + 1) + √(2 * y + 3) = 4) : x + y ≥ 2 := by
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


theorem cauchy_p10 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : 1 / (2 * x + y) + 3 / (x + y) = 2) : 6 * x + 5 * y ≥ 13 / 2 + 2 * √3 := by
  have h1 : (1 / (2 * x + y) + 3 / (x + y)) * (6 * x + 5 * y) ≥ 13 + 4 * √3 := by
    convert_to (∑ i : Fin 2, (![√(1 / (2 * x + y)), √(3 / (x + y))] i)^2) *
            (∑ i : Fin 2, (![√(2 * x + y), √(4 * x + 4 * y)] i)^2) ≥
            (∑ i : Fin 2, ![√(1 / (2 * x + y)), √(3 / (x + y))] i * ![√(2 * x + y), √(4 * x + 4 * y)] i)^2
    simp [Fin.sum_univ_three]
    field_simp; left; ring
    simp [Fin.sum_univ_three]
    have h_sq : √(4 * x + 4 * y) = 2 * √(x + y) := by
      calc √(4 * x + 4 * y) = Real.sqrt (4 * (x + y)) := by rw [mul_add]
      _ = Real.sqrt 4 * Real.sqrt (x + y) := by rw [Real.sqrt_mul (by linarith)]
      _ = 2 * Real.sqrt (x + y) := by ring
    field_simp [h_sq]
    ring_nf
    field_simp
    ring
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p11 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1) ≤ √15 := by
  have h1 : 3 * (2 * (a + b + c) + 3) ≥ (√(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1))^2 := by
    convert_to (∑ i : Fin 3, (![1, 1, 1] i)^2) *
            (∑ i : Fin 3, (![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i)^2) ≥
            (∑ i : Fin 3, ![1, 1, 1] i * ![√(2 * a + 1), √(2 * b + 1), √(2 * c + 1)] i)^2
    simp [Fin.sum_univ_three]
    field_simp; ring
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h] at h1
  norm_num at h1
  apply Real.sqrt_le_sqrt at h1
  rw [Real.sqrt_sq (add_nonneg (add_nonneg (Real.sqrt_nonneg (2 * a + 1)) (Real.sqrt_nonneg (2 * b + 1))) (Real.sqrt_nonneg (2 * c + 1)))] at h1
  exact h1


theorem cauchy_p12 (x y a b: ℝ) (hy : y ≠ 0) (hb : b ≠ 0) (hxy : x^2 + 1 / y^2 = 1) (hab : a^2 + 1 / b^2 = 4) : |a / y + x / b| ≤ 2 := by
  have h1 : (x^2 + 1 / y^2) * (a^2 + 1 / b^2) ≥ (a / y + x / b)^2 := by
    convert_to (∑ i : Fin 2, (![1 / y^2, x^2] i)) *
            (∑ i : Fin 2, (![a^2, 1 / b^2] i)) ≥
            (∑ i : Fin 2, ![a / y, x / b] i)^2
    simp [Fin.sum_univ_two]; left; ring
    simp [Fin.sum_univ_two]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> simp [sq_nonneg]; ring; rw [div_pow, inv_eq_one_div, mul_div, mul_one]
  rw [hxy, hab] at h1
  rw [← sq_le_sq₀, sq_abs]
  linarith
  exact abs_nonneg _
  norm_num


theorem cauchy_p13 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / b i ≥ (∑ i, a i)^2 / ∑ i, a i * b i := by
  convert_to ∑ i, (a i)^2 / (a i * b i) ≥ (∑ i, a i)^2 / ∑ i, a i * b i
  congr with i
  simp [sq, div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc]
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  apply mul_pos (ha i) (hb i)


theorem cauchy_p14 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / (b i)^2 ≥ (∑ i, a i / b i)^2 / ∑ i, a i := by
  convert_to ∑ i, (a i / b i)^2 / a i ≥ (∑ i, a i / b i)^2 / ∑ i, a i
  congr with i
  field_simp; rw [eq_comm]
  calc
    a i ^ 2 / (b i ^ 2 * a i) = a i ^ 2 / (a i * b i ^ 2) := by rw [mul_comm]
    _ = a i * a i / (a i * b i ^ 2) := by rw [pow_two]
    _ = a i * a i / a i / b i ^ 2  := by rw [div_div]
    _ = a i / b i ^ 2 := by rw [← mul_div, mul_div_cancel₀]; exact ne_of_gt (ha i)
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  exact ha i


theorem cauchy_p15 (a b c d e : ℝ) (h : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - e)^2 = 1) : a - 2 * b - c + 2 * e ≤ √10 := by
  let x := a - b
  let y := b - c
  let z := c - d
  let w := d - e
  have h0 : x^2 + y^2 + z^2 + w^2 = 1 := h
  have h1 : a - 2 * b - c + 2 * e = x - y - 2 * z - 2 * w := by ring
  have h2 : (x^2 + y^2 + z^2 + w^2) * 10 ≥ (x - y - 2 * z - 2 * w)^2 := by
    convert_to (∑ i : Fin 4, (![x^2, y^2, z^2, w^2] i)) *
            (∑ i : Fin 4, (![1^2, (-1)^2, (-2)^2, (-2)^2] i)) ≥
            (∑ i : Fin 4, ![x, - y, - 2 * z, - 2 * w] i)^2
    simp [Fin.sum_univ_four]
    left; norm_num
    simp [Fin.sum_univ_four]
    ring
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> norm_num
    intro i _
    fin_cases i <;> norm_num
    ring; ring
  rw [h0, ← h1] at h2
  apply Real.le_sqrt_of_sq_le at h2
  norm_num at h2
  exact h2


theorem cauchy_p16 (n : ℕ) (hn : n > 2) (a : Fin n → ℝ) (ha1 : ∀ i, a i < 1) (ha2 : ∀ i, a i ≥ 0) (hs : ∑ i : Fin n, a i = n - 2) : ∑ i : Fin n, ((a i)^2 / (1 - a i)) ≥ ((n : ℝ) - 2)^2 / 2 := by
  have h1 : (∑ i : Fin n, ((a i)^2 / (1 - a i))) * (∑ i : Fin n, (1 - a i)) ≥ (∑ i : Fin n, a i)^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    exact div_nonneg (sq_nonneg _) (by linarith [ha1 i])
    intro i _
    linarith [ha1 i]
    intro i _
    rw [div_mul, div_self, div_one]
    linarith [ha1 i]
  rw [hs] at h1
  have h2 : ∑ i : Fin n, (1 - a i) = 2 := by
    rw [Finset.sum_sub_distrib]
    rw [hs]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  nlinarith


theorem cauchy_p17 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2) = 2) : x^2 + y^2 + z^2 + 3 ≥ (x + y + z)^2 := by
  have h1 : (x^2 / (1 + x^2) + y^2 / (1 + y^2) + z^2 / (1 + z^2)) * (x^2 + y^2 + z^2 + 3) ≥ (x + y + z) ^ 2 := by
    convert_to (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i)^2) *
              (∑ i : Fin 3, (![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i)^2) ≥
              (∑ i : Fin 3, (![√(x^2 / (1 + x^2)), √(y^2 / (1 + y^2)), √(z^2 / (1 + z^2))] i * ![√(x^2 + 1), √(y^2 + 1), √(z^2 + 1)] i))^2
    simp [Fin.sum_univ_three]
    field_simp; left; ring
    simp [Fin.sum_univ_three]
    field_simp [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : x^2 / (1 + x^2) + y^2 / (1 + y^2) + z^2 / (1 + z^2) = 1 := by
    have key : ∀ a : ℝ, a^2 / (1 + a^2) = 1 - (1 / (1 + a^2)) :=
    λ a => by field_simp [← add_comm (a^2) 1]
    calc
      (x^2 / (1 + x^2)) + (y^2 / (1 + y^2)) + (z^2 / (1 + z^2)) = (1 - (1 / (1 + x^2))) + (1 - (1 / (1 + y^2))) + (1 - (1 / (1 + z^2))) := by rw [key x, key y, key z]
      _ = 3 - (1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2)) := by ring
      _ = 1 := by rw [h]; norm_num
  nlinarith


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


theorem cauchy_p19 (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (sum_eq : ∑ i, a i = ∑ i , b i): ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
  have h1 : (∑ i, (a i + b i)) * (∑ i, (a i)^2 / (a i + b i)) ≥ (∑ i, a i) ^ 2 := by
    convert_to (∑ i,(√(a i + b i))^2)*
        (∑ i, (a i / √(a i + b i))^2) ≥
        (∑ i, √(a i + b i) * (a i / √(a i + b i)))^2
    congr! with i1 h11 i2 h12
    have habl : a i1 + b i1 > 0 := by
      exact Right.add_pos' (ha i1) (hb i1)
    field_simp
    have hab2 : a i2 + b i2 > 0 := by
      exact Right.add_pos' (ha i2) (hb i2)
    field_simp
    congr! with i
    have hab : a i + b i > 0 := by
      exact Right.add_pos' (ha i) (hb i)
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq

  have h2: ∑ i, (a i + b i) = ∑ i, a i + ∑ i, b i := by
    rw [Finset.sum_add_distrib]
  have h3 : ∑ i, a i + ∑ i, b i=2 * ∑ i, a i := by
    linarith

  have h4 : ∑ i, a i > 0 := by
    apply Finset.sum_pos
    . intro i _
      exact ha i
    have h_nonempty : Nonempty (Fin n):= by
      apply Fin.pos_iff_nonempty.mp
      omega
    apply Finset.univ_nonempty

  have h5 : 2 * (∑ i, a i) * ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) ^ 2 := by
    rw [h2] at h1
    rw [h3] at h1
    linarith

  have h6 : (∑ i, a i)* ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i)*((∑ i, a i)/ 2):= by linarith

  have h7: ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i)/2 := by
    exact le_of_mul_le_mul_left h6 h4

  apply h7


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


theorem cauchy_p21 (a b c d e s : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)  (he : e > 0) (hs : s = a + b + c + d + e) : a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a)) ≥ 1 := by
  have h1 : (a + b + c + d + e)^2 * (a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a))) ≥ (a + b + c + d + e)^2 * 1 := by
    convert_to (∑ i : Fin 5, (![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i)^2) *
            (∑ i : Fin 5, (![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2) ≥
            (∑ i : Fin 5, ![a / √(a^2 + b * (s - b)), b / √(b^2 + c * (s - c)), c / √(c^2 + d * (s - d)), d / √(d^2 + e * (s - e)), e / √(e^2 + a * (s - a))] i * ![√(a^2 + b * (s - b)), √(b^2 + c * (s - c)), √(c^2 + d * (s - d)), √(d^2 + e * (s - e)), √(e^2 + a * (s - a))] i)^2
    simp [Fin.sum_univ_five]
    rw [hs]
    field_simp
    repeat rw [sq_sqrt]
    ring
    nlinarith; nlinarith; nlinarith; nlinarith
    simp [Fin.sum_univ_five]
    field_simp
    repeat rw [← mul_div, div_self, mul_one]
    rw [Real.sqrt_ne_zero']
    nlinarith
    rw [Real.sqrt_ne_zero']
    nlinarith
    rw [Real.sqrt_ne_zero']
    nlinarith
    rw [Real.sqrt_ne_zero']
    nlinarith
    rw [Real.sqrt_ne_zero']
    nlinarith
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have hpos : (a + b + c + d + e)^2 > 0 := by nlinarith
  have hineq := (mul_le_mul_left hpos).mp h1
  exact hineq


theorem cauchy_p22 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : x^2 + y^2 / 2 = 1) : x + √(2 + 3 * y^2) ≤ 2 * √21 / 3 := by
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
    rw [← sq_eq_sq₀]
    ring_nf; rw [sq_sqrt, sq_sqrt]; norm_num
    norm_num; norm_num
    exact Real.sqrt_nonneg ((1 + 1 / 3) * 7)
    exact div_nonneg (by linarith [Real.sqrt_nonneg 21]) (by norm_num)
  rw [h_num] at h1
  exact h1
  nlinarith [Real.sqrt_nonneg (2 + 3 * y ^ 2)]


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



theorem cauchy_p24 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (hxy : 2 * x - y^2 / x > 0) (hyz : 2 * y - z^2 / y > 0) (hzx : 2 * z - x^2 / z > 0) : x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z) ≥ x^2 + y^2 + z^2 := by
  have hx : x > 0 := h.1
  have hy : y > 0 := h.2.1
  have hz : z > 0 := h.2.2
  have hxy1 : 2 * x^2 - y^2 > 0 := by
    have h0 : 2 * x^2 - y^2 = x * (2 * x - y^2 / x) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hx hxy
  have hyz1 : 2 * y^2 - z^2 > 0 := by
    have h0 : 2 * y^2 - z^2 = y * (2 * y - z^2 / y) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hy hyz
  have hzx1 : 2 * z^2 - x^2 > 0 := by
    have h0 : 2 * z^2 - x^2 = z * (2 * z - x^2 / z) := by field_simp [sq]; ring
    rw [h0]
    apply smul_pos' hz hzx
  have h1 : (x^2 + y^2 + z^2) * (x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z)) ≥ (x^2 + y^2 + z^2)^2 := by
    convert_to (∑ i : Fin 3, (![2 * x^2 - y^2, 2 * y^2 - z^2, 2 * z^2 - x^2] i)) *
            (∑ i : Fin 3, (![x^3 / (2 * x - y^2 / x), y^3 / (2 * y - z^2 / y), z^3 / (2 * z - x^2 / z)] i)) ≥
            (∑ i : Fin 3, ![x^2, y^2, z^2] i)^2
    simp [Fin.sum_univ_three]; left; ring
    simp [Fin.sum_univ_three]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp <;> linarith
    intro i _
    fin_cases i <;> simp [sq_nonneg] <;> exact div_nonneg (pow_nonneg (by linarith) 3) (by linarith)
    intro i _
    fin_cases i <;> field_simp [sq_nonneg] <;> simp [mul_div_right_comm, mul_assoc, sq] <;> rw [div_self] <;> ring_nf <;> linarith
  rw [sq (x ^ 2 + y ^ 2 + z ^ 2)] at h1
  apply le_of_mul_le_mul_left h1
  nlinarith


theorem cauchy_p25 (n : ℕ) (x : Fin n → ℝ) (s : ℝ) (hn : n > 2) (hs : s = ∑ i, x i) (hx : ∀ i, x i < s - x i) : ∑ i, (x i)^2 / (s - 2 * x i) ≥ s / (n - 2) := by
  have hsx : ∀ i, s - 2 * x i = √(s - 2 * x i) ^ 2 := by
    intro i; rw [sq_sqrt]; nlinarith [hx i]

  have h_sum : ∑ i : Fin n, (s - 2 * x i) > 0 := by
    apply Finset.sum_pos
    congr! with i
    nlinarith [hx i]
    have h_nonempty : Nonempty (Fin n):= by
      apply Fin.pos_iff_nonempty.mp
      omega
    apply Finset.univ_nonempty

  have h1 : (∑ i, (x i)^2 / (s - 2 * x i)) * (∑ i, (s - 2 * x i)) ≥ s^2 := by
    rw [hs]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    -- 证明 ∀ i ∈ Finset.univ, 0 ≤ x i ^ 2 / (∑ i : Fin n, x i - 2 * x i)
    congr! with i
    rw [le_div_iff₀, zero_mul]
    exact sq_nonneg (x i)
    linarith [hx i]
    -- 证明 ∀ i ∈ Finset.univ, 0 ≤ ∑ i : Fin n, x i - 2 * x i
    congr! with i; linarith [hx i]
    -- 证明 ∀ i ∈ Finset.univ, x i ^ 2 = x i ^ 2 / (∑ i : Fin n, x i - 2 * x i) * (∑ i : Fin n, x i - 2 * x i)
    congr! with i
    rw [div_mul, div_self, div_one]
    have : ∑ i : Fin n, x i - 2 * x i > 0 := by linarith [hx i]
    exact ne_of_gt this

  have h3 : (∑ i, (s - 2 * x i)) = (n - 2) * s:= by
    calc
      ∑ i, (s - 2 * x i) = (∑ i, s) - ∑ i, (2 * x i) := by rw [Finset.sum_sub_distrib]
      _ = (∑ i, s) - 2 * ∑ i, x i := by rw [Finset.sum_const, Finset.mul_sum]
      _ = ↑n * s - 2 * s := by simp [hs, Nat.cast_sum]
      _ = (n - 2) * s := by ring
  rw [h3] at h1

  have h_pos : 0 < (↑n - 2) * s := by
    rw [← h3]
    exact h_sum

  apply (mul_le_mul_right h_pos).mp
  have h_simplify : s / (↑n - 2) * ((↑n - 2) * s) = s^2 := by
    calc
      s / (↑n - 2) * ((↑n - 2) * s) = s * ((↑n - 2) / (↑n - 2)) * s := by ring
      _ = s * 1 * s := by
        rw [div_self]
        have hn_real : (n : ℝ) - 2 > 0 := by
          have hn_real : (n : ℝ) > 2 := by exact_mod_cast hn
          linarith
        exact ne_of_gt hn_real
      _ = s * s := by ring
      _ = s^2 := by ring

  rw [h_simplify]
  exact h1
