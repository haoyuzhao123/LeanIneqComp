import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


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
