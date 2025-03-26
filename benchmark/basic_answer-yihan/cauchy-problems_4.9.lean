import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_p1 (x y : ℝ) (h₂ : x > 0 ∧ y > 0) : ( x + y ) * ( 1 / x + 1 / y ) ≥ 4 := by
  have hx : x > 0 := h₂.1
  have hy : y > 0 := h₂.2
  convert_to (∑ i : Fin 2, (![√x, √y] i)^2) *
      (∑ i : Fin 2, (![1 / √x, 1 / √y] i)^2) ≥
      (∑ i : Fin 2, ![√x, √y] i * ![1 / √x, 1 / √y] i)^2
  simp [Fin.sum_univ_two]
  field_simp [sqrt_sq]
  simp [Fin.sum_univ_two]
  field_simp; norm_num
  apply Finset.sum_mul_sq_le_sq_mul_sq


theorem cauchy_p2 (x y z: ℝ) (h₂ : x > 0 ∧ y > 0 ∧ z > 0 ) : ( x + y + z ) * ( 1 / x + 1 / y + 1 / z ) ≥ 9 := by
  have hx : x > 0 := h₂.1
  have hy : y > 0 := h₂.2.1
  have hz : z > 0 := h₂.2.2
  convert_to (∑ i : Fin 3, (![√x, √y, √z] i)^2) *
      (∑ i : Fin 3, (![1 / √x, 1 / √y, 1 / √z] i)^2) ≥
      (∑ i : Fin 3, ![√x, √y, √z] i * ![1 / √x, 1 / √y, 1 / √z] i)^2
  simp [Fin.sum_univ_three]
  field_simp [sqrt_sq]
  simp [Fin.sum_univ_three]
  field_simp; norm_num
  apply Finset.sum_mul_sq_le_sq_mul_sq


theorem cauchy_p3 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hxy : x + y ≤ 1) : 4 * x^2 + 4 * y^2 + (1 - x - y)^2 ≥ 2 / 3 := by
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


theorem cauchy_p4 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hx1 : x ≤ 1) (hy1 : y ≤ 1) : x * √(1 - y^2) + y * √(1 - x^2) ≤ 1 := by
  -- first prove the helper lemma
  have le_of_sq_le_sq (la lb : ℝ) (lh : la ^ 2 ≤ lb ^ 2) (hlb : 0 ≤ lb) : la ≤ lb := le_abs_self la |>.trans <| abs_le_of_sq_le_sq lh hlb

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


theorem cauchy_p5 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x + y + z = 3) : 4 / x + 1 / y + 9 / z ≥ 12 := by
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
    have h11 : √4 = 2 := by
      have h10 : √4 = √(2^2) := by norm_num
      rw [h10, Real.sqrt_sq]
      norm_num
    have h12 : Real.sqrt 9 = 3 := by
      have h20 : √9 = √(3^2) := by norm_num
      rw [h20, Real.sqrt_sq]
      norm_num
    simp [h11, h12]
    norm_num
    rw [ge_iff_le]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p6 (a b c : ℝ)
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


theorem cauchy_p7 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 1) : 1 / (b + c + d) + 1 / (c + d + a) + 1 / (a + b + d) + 1 / (a + b + c) ≥ 16 / 3 := by
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


theorem cauchy_p8 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (g : x * (x + y) + y * (y + z) + z * (z + x) = 1) : x / (x + y) + y / (y + z) + z / (z + x) ≥ (x + y + z) ^ 2 := by
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


theorem cauchy_p9 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) ( g : z * (x + y) + x * (y + z) + y * (z + x) = 1) : z / (x + y) + x / (y + z) + y / (z + x) ≥ (x + y + z) ^ 2 := by
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


theorem cauchy_p10 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : √(2 * x + 1) + √(2 * y + 3) = 4) : x + y ≥ 2 := by
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


theorem cauchy_p11 (x y z: ℝ) (h : x^2 + 2 * y^2 + 4 * z^2 > 0) : (x + y + z)^2 / (x^2 + 2 * y^2 + 4 * z^2) ≤ 7 / 4 := by
  have h1 : (x^2 + 2 * y^2 + 4 * z^2) * (1 + 1/2 + 1/4) ≥ (x + y + z)^2 := by
    convert_to (∑ i : Fin 3, (![x, √2 * y, 2 * z] i)^2) *
            (∑ i : Fin 3, (![1, 1 / √2, 1 / √4] i)^2) ≥
            (∑ i : Fin 3, ![x, √2 * y, 2 * z] i * ![1, 1 / √2, 1 / √4] i)^2
    simp [Fin.sum_univ_three]
    left; ring_nf; simp
    simp [Fin.sum_univ_three]
    have h11 : √4 = 2 := by
      have h10 : √4 = √(2^2) := by norm_num
      rw [h10, Real.sqrt_sq]
      norm_num
    ring_nf; simp [h11]; ring
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [mul_comm] at h1
  rw [div_le_iff]
  linarith
  exact h


theorem cauchy_p12 (x y: ℝ) (hx : x > 0) (hy : y > 0) (g : 1 / (2 * x + y) + 3 / (x + y) = 2) : 6 * x + 5 * y ≥ 13 / 2 + 2 * √3 := by
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
      _ = 2 * Real.sqrt (x + y) := by
        have h10 : √4 = √(2^2) := by norm_num
        rw [h10, Real.sqrt_sq]
        norm_num
    field_simp [h_sq]
    ring_nf
    field_simp
    ring
    apply Finset.sum_mul_sq_le_sq_mul_sq
  nlinarith


theorem cauchy_p13 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : √(2 * a + 1) + √(2 * b + 1) + √(2 * c + 1) ≤ √15 := by
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


theorem cauchy_p14 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / b i ≥ (∑ i, a i)^2 / ∑ i, a i * b i := by
  have h1 : (∑ i, a i / b i) * (∑ i, a i * b i) ≥ (∑ i, a i)^2 := by
    convert_to (∑ i, (√(a i / b i))^2) *
            (∑ i, (√(a i * b i))^2) ≥
            (∑ i, √(a i / b i) * √(a i * b i))^2
    congr! with i1 _ i2 _
    rw [sq_sqrt]
    exact div_nonneg (by linarith [ha i1]) (by linarith [hb i1])
    rw [sq_sqrt]
    exact mul_nonneg (by linarith [ha i2]) (by linarith [hb i2])
    congr! with i
    rw [← Real.sqrt_mul, mul_comm_div, ← mul_div, div_self]
    simp
    rw [Real.sqrt_mul_self]
    linarith [ha i]
    linarith [hb i]
    exact div_nonneg (by linarith [ha i]) (by linarith [hb i])
    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [ge_iff_le]
  apply div_le_of_nonneg_of_le_mul
  apply Finset.sum_nonneg
  congr! with i
  exact mul_nonneg (by linarith [ha i]) (by linarith [hb i])
  apply Finset.sum_nonneg
  congr! with i
  exact div_nonneg (by linarith [ha i]) (by linarith [hb i])
  linarith


theorem cauchy_p15 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) : ∑ i, a i / (b i)^2 ≥ (∑ i, a i / b i)^2 / ∑ i, a i := by
  have h1 : (∑ i, a i / (b i)^2) * (∑ i, a i) ≥ (∑ i, a i / (b i))^2 := by
    convert_to (∑ i, (√(a i) / (b i))^2) *
            (∑ i, (√(a i))^2) ≥
            (∑ i, √(a i) / (b i) * √(a i))^2
    congr! with i1 _ i2 _
    field_simp
    rw [Real.sq_sqrt]
    linarith [ha i1]
    rw [Real.sq_sqrt]
    linarith [ha i2]
    congr with i
    rw [div_mul_eq_mul_div, Real.mul_self_sqrt]
    linarith [ha i]
    apply Finset.sum_mul_sq_le_sq_mul_sq

  rw [ge_iff_le]
  apply div_le_of_nonneg_of_le_mul
  apply Finset.sum_nonneg
  congr! with i
  linarith [ha i]
  apply Finset.sum_nonneg
  congr! with i
  exact div_nonneg (by linarith [ha i]) (sq_nonneg _)
  linarith


theorem cauchy_p16 (x y a b: ℝ) (hy : y ≠ 0) (hb : b ≠ 0) (hxy : x^2 + 1 / y^2 = 1) (hab : a^2 + 1 / b^2 = 4) : |a / y + x / b| ≤ 2 := by
  -- prove a common version of cauchy
  have four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    calc 4 * a * b
      _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, mul_assoc, ← add_mul]; norm_num
      _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
      _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
      _ = (a + b) ^ 2 := (add_sq a b).symm
  have two_mul_le_add_of_sq_eq_mul {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
    apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
    conv_rhs => rw [← pow_two]
    convert four_mul_le_sq_add a b using 1
    rw [mul_mul_mul_comm, two_mul]; norm_num; rw [← pow_two, ht, mul_assoc]

  have sum_sq_le_sum_mul_sum_of_sq_eq_mul (n : ℕ) (s : Finset (Fin n)) {r f g : Fin n → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
    obtain h | h := (Finset.sum_nonneg hg).eq_or_gt
    · have ht' : ∑ i ∈ s, r i = 0 := Finset.sum_eq_zero fun i hi ↦ by
        simpa [(Finset.sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
      rw [h, ht']
      simp
    · refine le_of_mul_le_mul_of_pos_left
        (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
      calc
        _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
            gcongr with i hi
            have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
                (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
              conv_rhs => rw [mul_mul_mul_comm, ← ht i hi]
              ring
            refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
              (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
            repeat rw [mul_assoc]
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring

  have h1 : (x^2 + 1 / y^2) * (a^2 + 1 / b^2) ≥ (a / y + x / b)^2 := by
    convert_to (∑ i : Fin 2, (![1 / y^2, x^2] i)) *
            (∑ i : Fin 2, (![a^2, 1 / b^2] i)) ≥
            (∑ i : Fin 2, ![a / y, x / b] i)^2
    simp [Fin.sum_univ_two]; left; ring
    simp [Fin.sum_univ_two]
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    rw [inv_mul_eq_div]
    rw [mul_comm, inv_mul_eq_div]
    intro i _
    fin_cases i <;> simp [sq_nonneg]
    intro i _
    fin_cases i <;> simp [sq_nonneg]
  rw [hxy, hab] at h1
  have abs2 : 2 = |(2 : ℝ)| := by norm_num
  rw [abs2, ← sq_le_sq]
  linarith


theorem cauchy_p17 (a b c d e : ℝ) (h : (a - b)^2 + (b - c)^2 + (c - d)^2 + (d - e)^2 = 1) : a - 2 * b - c + 2 * e ≤ √10 := by
  -- prove a common version of cauchy
  have four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    calc 4 * a * b
      _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, mul_assoc, ← add_mul]; norm_num
      _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
      _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
      _ = (a + b) ^ 2 := (add_sq a b).symm
  have two_mul_le_add_of_sq_eq_mul {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
    apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
    conv_rhs => rw [← pow_two]
    convert four_mul_le_sq_add a b using 1
    rw [mul_mul_mul_comm, two_mul]; norm_num; rw [← pow_two, ht, mul_assoc]

  have sum_sq_le_sum_mul_sum_of_sq_eq_mul (n : ℕ) (s : Finset (Fin n)) {r f g : Fin n → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
    obtain h | h := (Finset.sum_nonneg hg).eq_or_gt
    · have ht' : ∑ i ∈ s, r i = 0 := Finset.sum_eq_zero fun i hi ↦ by
        simpa [(Finset.sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
      rw [h, ht']
      simp
    · refine le_of_mul_le_mul_of_pos_left
        (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
      calc
        _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
            gcongr with i hi
            have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
                (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
              conv_rhs => rw [mul_mul_mul_comm, ← ht i hi]
              ring
            refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
              (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
            repeat rw [mul_assoc]
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring

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
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> simp [sq_nonneg, mul_pow, mul_comm]
    intro i _
    fin_cases i <;> norm_num <;> positivity
    intro i _
    fin_cases i <;> norm_num
  rw [h0, ← h1] at h2
  apply Real.le_sqrt_of_sq_le at h2
  norm_num at h2
  exact h2


theorem cauchy_p18 (n : ℕ) (hn : n > 2) (a : Fin n → ℝ) (ha1 : ∀ i, a i < 1) (ha2 : ∀ i, a i ≥ 0) (hs : ∑ i : Fin n, a i = n - 2) : ∑ i : Fin n, ((a i)^2 / (1 - a i)) ≥ ((n : ℝ) - 2)^2 / 2 := by
  -- prove a common version of cauchy
  have four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    calc 4 * a * b
      _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, mul_assoc, ← add_mul]; norm_num
      _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
      _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
      _ = (a + b) ^ 2 := (add_sq a b).symm
  have two_mul_le_add_of_sq_eq_mul {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
    apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
    conv_rhs => rw [← pow_two]
    convert four_mul_le_sq_add a b using 1
    rw [mul_mul_mul_comm, two_mul]; norm_num; rw [← pow_two, ht, mul_assoc]

  have sum_sq_le_sum_mul_sum_of_sq_eq_mul (n : ℕ) (s : Finset (Fin n)) {r f g : Fin n → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
    obtain h | h := (Finset.sum_nonneg hg).eq_or_gt
    · have ht' : ∑ i ∈ s, r i = 0 := Finset.sum_eq_zero fun i hi ↦ by
        simpa [(Finset.sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
      rw [h, ht']
      simp
    · refine le_of_mul_le_mul_of_pos_left
        (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
      calc
        _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
            gcongr with i hi
            have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
                (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
              conv_rhs => rw [mul_mul_mul_comm, ← ht i hi]
              ring
            refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
              (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
            repeat rw [mul_assoc]
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring

  have h1 : (∑ i : Fin n, ((a i)^2 / (1 - a i))) * (∑ i : Fin n, (1 - a i)) ≥ (∑ i : Fin n, a i)^2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    rw [div_mul, div_self, div_one]
    linarith [ha1 i]
    intro i _
    exact div_nonneg (sq_nonneg _) (by nlinarith [ha1 i])
    intro i _
    linarith [ha1 i]
  rw [hs] at h1
  have h2 : ∑ i : Fin n, (1 - a i) = 2 := by
    rw [Finset.sum_sub_distrib]
    rw [hs]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  nlinarith


theorem cauchy_p19 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 1 / (1 + x^2) + 1 / (1 + y^2) + 1 / (1 + z^2) = 2) : x^2 + y^2 + z^2 + 3 ≥ (x + y + z)^2 := by
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


theorem cauchy_p20 (a b c : ℝ) (ha : a > 1) (hb : b > 1) (hc : c > 1) (h : (a^2 - 1) / 2 + (b^2 - 1) / 2 + (c^2 - 1) / 3 = 1) : a + b + c ≤ 7 * √3 / 3 := by
  -- first prove the helper lemma
  have le_of_sq_le_sq (la lb : ℝ) (lh : la ^ 2 ≤ lb ^ 2) (hlb : 0 ≤ lb) : la ≤ lb := le_abs_self la |>.trans <| abs_le_of_sq_le_sq lh hlb

  have h0 : a^2 / 2 + b^2 / 2 + c^2 / 3 = 7 / 3 := by linarith [h]
  have h1 : 7 * (a^2 / 2 + b^2 / 2 + c^2 / 3) ≥ (a + b + c)^2 := by
    convert_to (∑ i : Fin 3, (![√2, √2, √3] i)^2) *
            (∑ i : Fin 3, (![√(a^2 / 2), √(b^2 / 2), √(c^2 / 3)] i)^2) ≥
            (∑ i : Fin 3, ![√2, √2, √3] i * ![√(a^2 / 2), √(b^2 / 2), √(c^2 / 3)] i)^2
    simp [Fin.sum_univ_three]
    field_simp; left; norm_num
    simp [Fin.sum_univ_three]
    field_simp
    apply Finset.sum_mul_sq_le_sq_mul_sq
  rw [h0] at h1
  norm_num at h1
  apply le_of_sq_le_sq
  have : (7 * √3 / 3) ^ 2 = 49 / 3 := by
    ring; norm_num
  nlinarith
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) (by norm_num)


theorem cauchy_p21 (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (sum_eq : ∑ i, a i = ∑ i , b i): ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
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


theorem cauchy_p22 (a b c d e s : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)  (he : e > 0) (hs : s = a + b + c + d + e) : a^2 / (a^2 + b * (s - b)) + b^2 / (b^2 + c * (s - c)) + c^2 / (c^2 + d * (s - d)) + d^2 / (d^2 + e * (s - e)) + e^2 / (e^2 + a * (s - a)) ≥ 1 := by
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


theorem cauchy_p24 (x y z: ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0) (hxy : 2 * x - y^2 / x > 0) (hyz : 2 * y - z^2 / y > 0) (hzx : 2 * z - x^2 / z > 0) : x^3 / (2 * x - y^2 / x) + y^3 / (2 * y - z^2 / y) + z^3 / (2 * z - x^2 / z) ≥ x^2 + y^2 + z^2 := by
  -- prove a common version of cauchy
  have four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    calc 4 * a * b
      _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, mul_assoc, ← add_mul]; norm_num
      _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
      _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
      _ = (a + b) ^ 2 := (add_sq a b).symm
  have two_mul_le_add_of_sq_eq_mul {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
    apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
    conv_rhs => rw [← pow_two]
    convert four_mul_le_sq_add a b using 1
    rw [mul_mul_mul_comm, two_mul]; norm_num; rw [← pow_two, ht, mul_assoc]

  have sum_sq_le_sum_mul_sum_of_sq_eq_mul (n : ℕ) (s : Finset (Fin n)) {r f g : Fin n → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
    obtain h | h := (Finset.sum_nonneg hg).eq_or_gt
    · have ht' : ∑ i ∈ s, r i = 0 := Finset.sum_eq_zero fun i hi ↦ by
        simpa [(Finset.sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
      rw [h, ht']
      simp
    · refine le_of_mul_le_mul_of_pos_left
        (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
      calc
        _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
            gcongr with i hi
            have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
                (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
              conv_rhs => rw [mul_mul_mul_comm, ← ht i hi]
              ring
            refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
              (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
            repeat rw [mul_assoc]
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring

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
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    intro i _
    fin_cases i <;> field_simp [sq_nonneg] <;> simp [mul_div_right_comm, mul_assoc, sq] <;> rw [div_self] <;> ring_nf <;> linarith
    intro i _
    fin_cases i <;> simp <;> linarith
    intro i _
    fin_cases i <;> simp [sq_nonneg] <;> exact div_nonneg (pow_nonneg (by linarith) 3) (by linarith)
  rw [sq (x ^ 2 + y ^ 2 + z ^ 2)] at h1
  apply le_of_mul_le_mul_left h1
  nlinarith


theorem cauchy_p25 (n : ℕ) (x : Fin n → ℝ) (s : ℝ) (hn : n > 2) (hs : s = ∑ i, x i) (hx : ∀ i, x i < s - x i) : ∑ i, (x i)^2 / (s - 2 * x i) ≥ s / (n - 2) := by
  -- prove a common version of cauchy
  have four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
    calc 4 * a * b
      _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, mul_assoc, ← add_mul]; norm_num
      _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
      _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
      _ = (a + b) ^ 2 := (add_sq a b).symm
  have two_mul_le_add_of_sq_eq_mul {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
    apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
    conv_rhs => rw [← pow_two]
    convert four_mul_le_sq_add a b using 1
    rw [mul_mul_mul_comm, two_mul]; norm_num; rw [← pow_two, ht, mul_assoc]

  have sum_sq_le_sum_mul_sum_of_sq_eq_mul (n : ℕ) (s : Finset (Fin n)) {r f g : Fin n → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
    obtain h | h := (Finset.sum_nonneg hg).eq_or_gt
    · have ht' : ∑ i ∈ s, r i = 0 := Finset.sum_eq_zero fun i hi ↦ by
        simpa [(Finset.sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
      rw [h, ht']
      simp
    · refine le_of_mul_le_mul_of_pos_left
        (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
      calc
        _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
        _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
            gcongr with i hi
            have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
                (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
              conv_rhs => rw [mul_mul_mul_comm, ← ht i hi]
              ring
            refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
              (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
            repeat rw [mul_assoc]
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; ring

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
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
    -- 证明 ∀ i ∈ Finset.univ, x i ^ 2 = x i ^ 2 / (∑ i : Fin n, x i - 2 * x i) * (∑ i : Fin n, x i - 2 * x i)
    congr! with i
    rw [div_mul, div_self, div_one]
    have : ∑ i : Fin n, x i - 2 * x i > 0 := by linarith [hx i]
    exact ne_of_gt this
    -- 证明 ∀ i ∈ Finset.univ, 0 ≤ x i ^ 2 / (∑ i : Fin n, x i - 2 * x i)
    congr! with i
    rw [le_div_iff, zero_mul]
    exact sq_nonneg (x i)
    linarith [hx i]
    -- 证明 ∀ i ∈ Finset.univ, 0 ≤ ∑ i : Fin n, x i - 2 * x i
    congr! with i; linarith [hx i]

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
