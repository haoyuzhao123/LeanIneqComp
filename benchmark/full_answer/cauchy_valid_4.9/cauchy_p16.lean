import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

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
