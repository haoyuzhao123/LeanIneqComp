import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem induction_p1 (n : ℕ) (h : n ≥ 4) : 2 ^ n ≥ n + 1 := by
  induction' h with k h IH
  · calc 2 ^ 4 = 16 := by norm_num
      _ ≥ 4 + 1 := by norm_num
  calc 2 ^ k.succ = 2 ^ k * 2 := Nat.pow_succ 2 k
    _ ≥ (k + 1) * 2 := by linarith
    _ = 2 * k + 2 := by ring
    _ ≥ k + 2 := by linarith

theorem induction_p2_minif2f_induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) : 1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction' h₁ with k h₁ IH
  · calc 1 + ↑(succ 0) * x = 1 + x := by simp
      _ ≤ (1 + x) ^ (succ 0 : ℕ) := by simp
  calc 1 + ↑k.succ * x = 1 + ↑k * x + x := by rw [Nat.cast_succ] ; ring
    _ ≤ 1 + ↑k * x + x + ↑k * x * x := by nlinarith [ sq_nonneg (x) ]
    _ = (1 + x) * (1 + ↑k * x) := by ring
    _ ≤ (1 + x) * (1 + x) ^ (k : ℕ) := by nlinarith
    _ = (1 + x) ^ k.succ := by rw [pow_succ]; ring

theorem induction_p3_minif2f_induction_ineq_nsqlefactn (n : ℕ) (h₀ : 4 ≤ n) : n ^ 2 ≤ n ! := by
  induction' h₀ with k g IH
  · calc 4 ^ 2 = 16 := by simp
      _ ≤ 24 := by simp
      _ = 4 ! := by simp [Nat.factorial_succ]
  have j : k ≥ 4 := by norm_cast
  calc k.succ ^ 2 = (k + 1) ^ 2 := by simp
    _ = k ^ 2 + 2 * k + 1 := by ring
    _ ≤ k ^ 2 + 2 * k + 4 := by simp
    _ ≤ k ^ 2 + 2 * k + k := by simp_all
    _ = k ^ 2 + 3 * k := by ring
    _ ≤ k ^ 2 + k ^ 2 := by nlinarith
    _ = 2 * k ^ 2 := by ring
    _ ≤ k.succ * k ^ 2 := by nlinarith
    _ ≤ k.succ * k ! := by nlinarith
    _ = k.succ ! := by apply Nat.factorial_succ

example (n : ℕ) (h₀ : 3 ≤ n) : n.succ ^ (n - 1) ≥ n ^ (n - 1) := by
  -- Apply the lemma that if `a ≤ b`, then `a^k ≤ b^k` for non-negative `k`.
  apply Nat.pow_le_pow_of_le_left
  -- Prove that `n ≤ n.succ` (since `n.succ = n + 1`).
  exact Nat.le_succ n

theorem induction_p4_minif2f_induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction' h₀ with k g IH
  · calc 3 ! = 6 := by simp [Nat.factorial_succ]
      _ < 9 := by simp
      _ = 3 ^ (3 - 1) := by simp

  have lk : k ^ (k - 1) ≤ k.succ ^ (k - 1) := by
    -- Apply the lemma that if `a ≤ b`, then `a^j ≤ b^j` for non-negative `j`.
    apply Nat.pow_le_pow_of_le_left
    -- Prove that `k ≤ k.succ` (since `k.succ = k + 1`).
    exact Nat.le_succ k

  -- Haoyu: Copied from STP and Goedel prover, purely magic, don't understand why it pass the compilation
  have lksucc : k.succ * ( k.succ ^ (k - 1) ) = k.succ ^ k := by
    induction' g with j h hk
    <;> simp_all [Nat.pow_succ]
    <;> ring

  calc k.succ ! = k.succ * k ! := by apply Nat.factorial_succ
    _ < k.succ * k ^ (k - 1) := by nlinarith
    -- Apply the lemma that if `a ≤ b`, then `a^k ≤ b^k` for non-negative `k`.
    -- Prove that `n ≤ n.succ` (since `n.succ = n + 1`).
    _ ≤ k.succ * (k.succ ^ (k - 1)) := by nlinarith
    --_ = k.succ ^ (k - 1) * k.succ := by ring
    _ = k.succ ^ k := by apply lksucc

theorem induction_p5_minif2f_induction_pord1p1on2powklt5on2 (n : ℕ) (h₀ : 0 < n) : (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := by sorry

theorem induction_p6_minif2f_induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) : (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
  induction' h₀ with m j IH
  · calc ∏ k ∈ Finset.Icc 1 (succ 0), (1 + (1 : ℝ) / ↑k ^ 3) = 1 + (1 : ℝ) / 1 ^ 3 := by norm_cast; rw [Finset.Icc_self, Finset.prod_singleton]
      _ = (2 : ℝ) := by norm_num
      _ ≤ 3 - (1 : ℝ) / (succ 0) := by norm_num

  have hsuccm: (succ m : ℝ) ^ 3 > 0 := by norm_cast; simp

  -- Haoyu: also, some magic
  have hmp: m > 0 := by cases m with
  | zero =>
    -- Case 1: `m = 0` leads to a contradiction with `j : 0 ≥ 1`
    contradiction
  | succ m' =>
    simp

  have hmnn : m ≥ 0 := by linarith

  have hmpr : (m : ℝ) > 0 := by norm_cast
  have hmsucccum : (succ m : ℝ) ^ 3 * m > 0 := by nlinarith

  -- Haoyu: also, copied from STP and Goedel
  have ineq_poly : ((succ m : ℝ) ^ 3 + (1 : ℝ)) * (3 * (m : ℝ) - 1) ≤ (3 * (succ m : ℝ) ^ 3 * (m : ℝ) - (succ m : ℝ) ^ 2 * m) := by
    norm_num at j
    simp [pow_succ]
    nlinarith [ mul_self_nonneg (m : ℝ) ]


  have ineq: (1 + (1 : ℝ) / (succ m) ^ 3) * (3 - (1 : ℝ) / m) ≤ (3 - (1 : ℝ) / (succ m)) := by
    calc (1 + (1 : ℝ) / (succ m) ^ 3) * (3 - (1 : ℝ) / m) = ((succ m : ℝ) ^ 3 + (1 : ℝ)) * (3 * (m : ℝ) - 1) / ((succ m : ℝ) ^ 3 * m) := by field_simp
      _ ≤ (3 * (succ m : ℝ) ^ 3 * (m : ℝ) - (succ m : ℝ) ^ 2 * m) / ((succ m : ℝ) ^ 3 * m) := by gcongr
      _ = (3 * succ m - 1) * (succ m : ℝ) ^ 2 * (m : ℝ) / ((succ m : ℝ) ^ 3 * m) := by ring
      _ = (3 * succ m - 1) * (succ m : ℝ) ^ 2 / (succ m : ℝ) ^ 3 := by field_simp; ring
      _ = (3 * succ m - 1) / (succ m : ℝ) := by field_simp; ring
      _ = 3 * succ m / succ m - (1 : ℝ) / (succ m) := by ring
      _ = 3 - (1 : ℝ) / (succ m) := by field_simp

  have ihp : 1 + (1 : ℝ) / (m.succ : ℝ) ^ 3 > 0 := by field_simp
  calc ∏ k ∈ Finset.Icc 1 m.succ, (1 + 1 / ↑k ^ 3) = (∏ k ∈ Finset.Icc 1 m, (1 + 1 / ↑k ^ 3)) * (1 + (1 : ℝ) / (m.succ : ℝ) ^ 3) := by apply Finset.prod_Ioc_succ_top hmnn
    _ ≤ (3 - (1 : ℝ) / m) * (1 + (1 : ℝ) / (m.succ : ℝ) ^ 3) := by nlinarith
    _ ≤ (3 - (1 : ℝ) / (succ m)) := by nlinarith

example : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (2 : ℝ) * ( Real.sqrt (2 : ℝ) - (1 : ℝ)) := by norm_num

example (j : ℕ) (h : j ≥ 2) : ∑ k in Finset.Icc 2 j.succ, (1 : ℝ) / Real.sqrt k = (∑ k in Finset.Icc 2 j, (1 : ℝ) / Real.sqrt k) + (1 : ℝ) / Real.sqrt (j.succ : ℝ) := by
  -- Split the interval 2 to j+1 into 2 to j and the singleton {j+1}
  rw [Finset.sum_Icc_succ_top]
  -- Use the property of sums over disjoint sets to split the sum
  linarith

theorem induction_p7_minif2f_algebra_sum1onsqrt2to1onsqrt10000lt198 : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- First show that 1 / √n ≤ 2(√n - √n-1)
  -- The solution is obtained by Goedel Prover, STP will also generate these answer which are not readable by human
  have sqrtlemma (m : ℕ) (h: m ≥ 1) : 1 / Real.sqrt m ≤ 2 * (Real.sqrt m - Real.sqrt (m-1)) := by
    cases m with
    | zero =>
      simp_all [Nat.succ_le_iff]
    | succ m =>
      field_simp [Real.sqrt_eq_iff_mul_self_eq]
      rw [div_le_iff₀] <;> norm_num <;>
      nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg (m + 1), sq_sqrt (by linarith : 0 ≤ (m : ℝ)),
        sq_sqrt (by linarith : 0 ≤ (m + 1 : ℝ))]

  have inductionthm (n : ℕ) (hn : n ≥ 2) : (∑ k in Finset.Icc (2 : ℕ) n, (1 : ℝ) / Real.sqrt k) ≤  2 * (Real.sqrt n - 1) := by
    induction' hn with j hj IH
    · calc ∑ k in Finset.Icc (2 : ℕ) 2, ((1 : ℝ) / Real.sqrt k) = (1 : ℝ) / Real.sqrt (2 : ℝ) := by norm_cast; rw [Finset.Icc_self, Finset.sum_singleton] ; norm_num
        _ ≤ 2 * (Real.sqrt 2 - 1) := by sorry

    have hjg2 : 2 ≤ j.succ := by sorry
    have hjg1 : j.succ ≥ 1 := by norm_num

    have IS : 2 * (√j - 1) + (1 : ℝ) / Real.sqrt (succ j : ℝ) ≤ 2 * (√j - 1) + 2 * (Real.sqrt (j+1 : ℝ) - Real.sqrt j) := by norm_cast ; simp_all ; apply sqrtlemma (j + 1)

    calc ∑ k ∈ Finset.Icc 2 j.succ, (1 : ℝ) / Real.sqrt k = (∑ k ∈ Finset.Icc 2 j, (1 : ℝ) / Real.sqrt k) + (1 : ℝ) / Real.sqrt (succ j : ℝ) := by rw [Finset.sum_Icc_succ_top hjg2]
      _ ≤ 2 * (√j - 1) + (1 : ℝ) / Real.sqrt (succ j : ℝ) := by nlinarith
      _ ≤ 2 * (√j - 1) + 2 * (Real.sqrt (j+1) - Real.sqrt j) := by norm_cast; simp_all ; nlinarith
