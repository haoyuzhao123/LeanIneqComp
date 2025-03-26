import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p25 (n : ℕ) (x : Fin n → ℝ) (s : ℝ) (hn : n > 2) (hs : s = ∑ i, x i) (hx : ∀ i, x i < s - x i) : ∑ i, (x i)^2 / (s - 2 * x i) ≥ s / (n - 2) := by
  have h_sum : ∑ i : Fin n, (s - 2 * x i) > 0 := by
    apply Finset.sum_pos
    congr! with i
    nlinarith [hx i]
    have h_nonempty : Nonempty (Fin n):= by
      apply Fin.pos_iff_nonempty.mp
      omega
    apply Finset.univ_nonempty

  have h1 : (∑ i, (x i)^2 / (s - 2 * x i)) * (∑ i, (s - 2 * x i)) ≥ s^2 := by
    convert_to (∑ i, (x i / √(s - 2 * x i))^ 2) * (∑ i, (√(s - 2 * x i))^2) ≥
            (∑ i, (x i / √(s - 2 * x i)) * √(s - 2 * x i)) ^ 2
    congr! with i1 _ i2 _
    rw [div_pow, sq_sqrt]
    linarith [hx i1]
    rw [sq_sqrt]
    linarith [hx i2]
    rw [hs]
    congr! with i
    rw [div_mul, div_self, div_one]
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx i]))
    apply Finset.sum_mul_sq_le_sq_mul_sq

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
