import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_n_example (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (sum_eq : ∑ i, a i = ∑ i , b i): ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
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


theorem cauchy_3_example (a b c : ℝ)
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


theorem cauchy_p1_CS4 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x * (x + y) + y * (y + z) + z * (z + x) = 1) : x / (x + y) + y / (y + z) + z / (z + x) ≥ (x + y + z) ^ 2 := by
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


theorem cauchy_p2_CS5 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) ( g : z * (x + y) + x * (y + z) + y * (z + x) = 1) : z / (x + y) + x / (y + z) + y / (z + x) ≥ (x + y + z) ^ 2 := by
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


theorem cauchy_p3_hard1  (x y z : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) (h : 1/x + 1/y + 1/z = 2) : Real.sqrt (x + y + z) ≥ Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) := by
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


theorem cauchy_p4_hard2 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2) = 2) : x^2 + y^2 + z^2 + 3 ≥ (x + y + z)^2 := by
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


theorem cauchy_p6 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1) ≤ √15 := by
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


theorem cauchy_p7 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(3 * c + 1) ≤ 7 * √3 / 3 := by
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


-- 用了另一个形式
theorem cauchy_p8 (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / b i ≥ (∑ i, a i)^2 / ∑ i, a i * b i := by
  convert_to ∑ i, (a i)^2 / (a i * b i) ≥ (∑ i, a i)^2 / ∑ i, a i * b i
  congr with i
  simp [sq, div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc]
  apply Finset.sq_sum_div_le_sum_sq_div
  congr! with i
  apply mul_pos (ha i) (hb i)


theorem cauchy_p9 (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / (b i)^2 ≥ (∑ i, a i / b i)^2 / ∑ i, a i := by
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


-- 使用 Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul 版本的 Cauchy
theorem cauchy_p10_book_172 (n : ℕ) (x : Fin n → ℝ) (s : ℝ) (hn : n > 2) (hs : s = ∑ i, x i) (hx : ∀ i, x i < s - x i) : ∑ i, (x i)^2 / (s - 2 * x i) ≥ s / (n - 2) := by
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
        -- 需要证 ↑n - 2 ≠ 0
        sorry

      _ = s * s := by ring
      _ = s^2 := by ring

  rw [h_simplify]
  exact h1
