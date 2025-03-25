import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

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
