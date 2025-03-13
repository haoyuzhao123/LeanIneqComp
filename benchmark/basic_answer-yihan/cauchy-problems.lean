import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem cauchy_n_example (n : ℕ) (a b : Fin n → ℝ) (hn : n > 0) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (sum_eq : ∑i, a i = ∑ i , b i): ∑ i,(a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
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


theorem cauchy_p3_hard1  (x y z : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) (h : 1/x + 1/y + 1/z = 2) : Real.sqrt (x + y + z) ≥ Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) := by sorry



theorem cauchy_p4_hard2  (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 1/ (1+x^2) + 1/(1+y^2) + 1/(1+z^2) = 2) : x^2+y^2+z^2+3 ≥ (x+y+z)^2 := by sorry
