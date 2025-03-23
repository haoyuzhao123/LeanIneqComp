import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem jensen_p1 (x y : ℝ) (h : x > 0) (g : y > 0) : ((1:ℝ)/3 * x + (2:ℝ)/3 * y) ^ 4 ≤ (1:ℝ)/3 * x^4 + (2:ℝ)/3 * y ^ 4  := by
  let w := ![(1:ℝ)/3, (2:ℝ)/3]
  let S := ![x, y]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 2, w i = 1 := by
      simp [w]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 2, w i * S i)^4 ≤ ∑ i : Fin 2, w i * S i ^ 4 := by
    apply (convexOn_pow 4).map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  nlinarith

theorem jensen_p2 (x y : ℝ) : Real.exp ((1:ℝ)/4 * x + (3:ℝ)/4 * y) ≤ (1:ℝ)/4 * Real.exp x + (3:ℝ)/4 * Real.exp y  := by
  let w := ![(1:ℝ)/4, (3:ℝ)/4]
  let S := ![x, y]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 2, w i = 1 := by
      simp [w]
      norm_num

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.univ := by
      intros i
      fin_cases i
      all_goals
        simp [S]

  have jensen_ineq : Real.exp (∑ i : Fin 2, w i * S i) ≤ ∑ i : Fin 2, w i * Real.exp (S i) := by
    apply convexOn_exp.map_sum_le w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  nlinarith

theorem jensen_p3 (x y : ℝ) (h : x > 0) (g : y > 0): ((1:ℝ)/4 * x + (3:ℝ)/4 * y) * Real.log ((1:ℝ)/4 * x + (3:ℝ)/4 * y) ≤ (1:ℝ)/4 * x * Real.log x + (3:ℝ)/4 * y * Real.log y := by
  let w := ![(1:ℝ)/4, (3:ℝ)/4]
  let S := ![x, y]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 2, w i = 1 := by
      simp [w]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, S i ∈ Set.Ici 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 2, w i * S i) * Real.log (∑ i : Fin 2, w i * S i) ≤ ∑ i : Fin 2, w i * ((S i) * Real.log (S i)) := by
    apply Real.convexOn_mul_log.map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_two] at jensen_ineq

  nlinarith

theorem jensen_p4 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = 3) : (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y ^ 6 + (1:ℝ)/3 * z ^ 6 ≥ 1 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, 0 ≤ S i := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : (∑ i : Fin 3, w i * S i)^6 ≤ ∑ i : Fin 3, w i * S i ^ 6 := by
    apply (convexOn_pow 6).map_sum_le w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  calc (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y ^ 6 + (1:ℝ)/3 * z ^ 6 ≥ ((1:ℝ)/3 * x + (1:ℝ)/3 * y + (1:ℝ)/3 * z)^6 := by linarith
    _ = ((1:ℝ)/3 * (x + y + z))^6 := by ring
    _ = ((1:ℝ)/3 * 3)^6 := by rw [k]
    _ = 1 := by norm_num


theorem jensen_p5 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * x ^ ((1:ℝ)/3) + (3:ℝ)/8 * y ^ ((1:ℝ)/3) + (3:ℝ)/8 * z ^ ((1:ℝ)/3) ≤ ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) ^ ((1:ℝ)/3) := by
  let w := ![(1:ℝ)/4, (3:ℝ)/8, (3:ℝ)/8]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, S i ∈ Set.Ici 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : ∑ i : Fin 3, w i * (S i) ^ ((1:ℝ)/3) ≤ (∑ i : Fin 3, w i * S i) ^ ((1:ℝ)/3) := by
    apply (concaveOn_rpow (by positivity) (by norm_num)).le_map_sum w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  nlinarith


theorem jensen_p6 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * Real.log x + (3:ℝ)/8 * Real.log y + (3:ℝ)/8 * Real.log z ≤ Real.log ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) := by
  let w := ![(1:ℝ)/4, (3:ℝ)/8, (3:ℝ)/8]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_pos : ∀ i ∈ Finset.univ, S i ∈ Set.Ioi 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : ∑ i : Fin 3, w i * Real.log (S i) ≤ Real.log (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_log_Ioi.concaveOn.le_map_sum w_nonneg w_sump s_pos

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  nlinarith


theorem jensen_p7 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0): (1:ℝ)/4 * Real.sqrt x + (3:ℝ)/8 * Real.sqrt y + (3:ℝ)/8 * Real.sqrt z ≤ Real.sqrt ((1:ℝ)/4 * x + (3:ℝ)/8 * y + (3:ℝ)/8 * z) := by
  let w := ![(1:ℝ)/4, (3:ℝ)/8, (3:ℝ)/8]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]
        <;> norm_num

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have s_nonneg : ∀ i ∈ Finset.univ, S i ∈ Set.Ici 0 := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        positivity

  have jensen_ineq : ∑ i : Fin 3, w i * Real.sqrt (S i) ≤ Real.sqrt (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_sqrt.concaveOn.le_map_sum w_nonneg w_sump s_nonneg

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq

  nlinarith


theorem jensen_p8 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = π): (1:ℝ)/3 * Real.sin x + (1:ℝ)/3 * Real.sin y + (1:ℝ)/3 * Real.sin z ≤ √3 / 2 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x, y, z]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have xlepi : x ≤ π := by
    have yzp : y+z > 0 := by linarith
    linarith

  have ylepi : y ≤ π := by
    have xzp : x+z > 0 := by linarith
    linarith

  have zlepi : z ≤ π := by
    have xyp : x+y > 0 := by linarith
    linarith

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.Icc 0 π := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        apply And.intro (by linarith) (by linarith)

  have jensen_ineq : ∑ i : Fin 3, w i * Real.sin (S i) ≤ Real.sin (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_sin_Icc.concaveOn.le_map_sum w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq
  rw [← Real.sin_pi_div_three]
  have sum : 3⁻¹ * x + 3⁻¹ * y + 3⁻¹ * z = π / 3 := by linarith [k]
  rw [sum] at jensen_ineq

  nlinarith


theorem jensen_p9 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = π): (1:ℝ)/3 * Real.sin (x/2) + (1:ℝ)/3 * Real.sin (y/2) + (1:ℝ)/3 * Real.sin (z/2) ≤ 1 / 2 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x/2, y/2, z/2]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have xlepi : x ≤ π := by
    have yzp : y+z > 0 := by linarith
    linarith

  have ylepi : y ≤ π := by
    have xzp : x+z > 0 := by linarith
    linarith

  have zlepi : z ≤ π := by
    have xyp : x+y > 0 := by linarith
    linarith

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.Icc 0 π := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        apply And.intro (by linarith) (by linarith)

  have jensen_ineq : ∑ i : Fin 3, w i * Real.sin (S i) ≤ Real.sin (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_sin_Icc.concaveOn.le_map_sum w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq
  rw [← Real.sin_pi_div_six]
  have sum : 3⁻¹ * (x / 2) + 3⁻¹ * (y / 2) + 3⁻¹ * (z / 2) = π / 6 := by linarith [k]
  rw [sum] at jensen_ineq

  nlinarith


theorem jensen_p10 (x y z: ℝ) (h : x > 0) (g : y > 0) (j : z > 0) (k : x + y + z = π): (1:ℝ)/3 * Real.cos (x/2) + (1:ℝ)/3 * Real.cos (y/2) + (1:ℝ)/3 * Real.cos (z/2) ≤ √3 / 2 := by
  let w := ![(1:ℝ)/3, (1:ℝ)/3, (1:ℝ)/3]
  let S := ![x/2, y/2, z/2]

  have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intros i
      fin_cases i
      all_goals
        simp [w]

  have w_sump : ∑ i : Fin 3, w i = 1 := by
      simp [w]
      simp [Fin.sum_univ_three]
      norm_num

  have xlepi : x ≤ π := by
    have yzp : y+z > 0 := by linarith
    linarith

  have ylepi : y ≤ π := by
    have xzp : x+z > 0 := by linarith
    linarith

  have zlepi : z ≤ π := by
    have xyp : x+y > 0 := by linarith
    linarith

  have s_indomain : ∀ i ∈ Finset.univ, S i ∈ Set.Icc (-(π / 2)) (π / 2) := by
      intros i
      fin_cases i
      all_goals
        simp [S]
        apply And.intro (by linarith) (by linarith)

  have jensen_ineq : ∑ i : Fin 3, w i * Real.cos (S i) ≤ Real.cos (∑ i : Fin 3, w i * S i) := by
    apply strictConcaveOn_cos_Icc.concaveOn.le_map_sum w_nonneg w_sump s_indomain

  simp [S] at jensen_ineq
  simp [w] at jensen_ineq
  norm_num at jensen_ineq
  simp [Fin.sum_univ_three] at jensen_ineq
  rw [← Real.cos_pi_div_six]
  have sum : 3⁻¹ * (x / 2) + 3⁻¹ * (y / 2) + 3⁻¹ * (z / 2) = π / 6 := by linarith [k]
  rw [sum] at jensen_ineq

  nlinarith


theorem induction_p1 (n : ℕ) (h : n ≥ 4) : 2 ^ n ≥ n + 1 := by
  induction' h with k h IH
  · calc 2 ^ 4 = 16 := by norm_num
      _ ≥ 4 + 1 := by norm_num
  calc 2 ^ k.succ = 2 ^ k * 2 := Nat.pow_succ 2 k
    _ ≥ (k + 1) * 2 := by linarith
    _ = 2 * k + 2 := by ring
    _ ≥ k + 2 := by linarith


theorem induction_p2 (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) : 1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction' h₁ with k h₁ IH
  · calc 1 + ↑(succ 0) * x = 1 + x := by simp
      _ ≤ (1 + x) ^ (succ 0 : ℕ) := by simp
  calc 1 + ↑k.succ * x = 1 + ↑k * x + x := by rw [Nat.cast_succ] ; ring
    _ ≤ 1 + ↑k * x + x + ↑k * x * x := by nlinarith [ sq_nonneg (x) ]
    _ = (1 + x) * (1 + ↑k * x) := by ring
    _ ≤ (1 + x) * (1 + x) ^ (k : ℕ) := by nlinarith
    _ = (1 + x) ^ k.succ := by rw [pow_succ]; ring


theorem induction_p3 (n : ℕ) (h₀ : 4 ≤ n) : n ^ 2 ≤ n ! := by
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


theorem induction_p4 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction' h₀ with k g IH
  · calc 3 ! = 6 := by simp [Nat.factorial_succ]
      _ < 9 := by simp
      _ = 3 ^ (3 - 1) := by simp

  have lk : k ^ (k - 1) ≤ k.succ ^ (k - 1) := by
    -- Apply the lemma that if `a ≤ b`, then `a^j ≤ b^j` for non-negative `j`.
    apply Nat.pow_le_pow_left
    -- Prove that `k ≤ k.succ` (since `k.succ = k + 1`).
    exact Nat.le_succ k

  have lksucc : k.succ * ( k.succ ^ (k - 1) ) = k.succ ^ k := by
    induction' g with j h hk
    <;> simp_all [Nat.pow_succ]
    ring

  calc k.succ ! = k.succ * k ! := by apply Nat.factorial_succ
    _ < k.succ * k ^ (k - 1) := by nlinarith
    -- Apply the lemma that if `a ≤ b`, then `a^k ≤ b^k` for non-negative `k`.
    -- Prove that `n ≤ n.succ` (since `n.succ = n + 1`).
    _ ≤ k.succ * (k.succ ^ (k - 1)) := by nlinarith
    --_ = k.succ ^ (k - 1) * k.succ := by ring
    _ = k.succ ^ k := by apply lksucc


theorem induction_p5 (n : ℕ) (h₀ : 0 < n) : (∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3)) ≤ (3 : ℝ) - 1 / ↑n := by
  induction' h₀ with m j IH
  · calc ∏ k ∈ Finset.Icc 1 (succ 0), (1 + (1 : ℝ) / ↑k ^ 3) = 1 + (1 : ℝ) / 1 ^ 3 := by norm_cast; rw [Finset.Icc_self, Finset.prod_singleton]
      _ = (2 : ℝ) := by norm_num
      _ ≤ 3 - (1 : ℝ) / (succ 0) := by norm_num

  have hsuccm: (succ m : ℝ) ^ 3 > 0 := by norm_cast; simp

  have hmp: m > 0 := by cases m with
  | zero =>
    -- Case 1: `m = 0` leads to a contradiction with `j : 0 ≥ 1`
    contradiction
  | succ m' =>
    simp

  have hmnn : m ≥ 0 := by linarith

  have hmpr : (m : ℝ) > 0 := by norm_cast
  have hmsucccum : (succ m : ℝ) ^ 3 * m > 0 := by nlinarith

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


theorem schur_p1 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  let x := a
  let y := 1
  let z := 1 / b
  have hx : 0 < x := by positivity
  have hy : (0 : ℝ) < y := by positivity
  have hz : 0 < z := by positivity
  have h1 : a = x / y := by ring
  have h2 : b = y / z := by field_simp; ring; rw [mul_inv_cancel₀]; linarith
  have h3 : c = z / x := by
    have h31 : x = a := by linarith
    have h32 : z = 1 / b := by linarith
    rw [h31, h32]
    field_simp
    ring
    rw [mul_comm, mul_comm c b, ← mul_assoc]
    exact h

  rw [h1, h2, h3]
  field_simp

  have schur : (x - y + z) * (y - z + x) * (z - x + y) ≤ y * z * x := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_self_nonneg (x - y + z), mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]

  apply div_le_one_of_le₀ schur
  positivity


theorem schur_p2 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 + a / b + b / c + c / a ≥ a + b + c + 1 / a + 1 / b + 1 / c := by
  let x := a
  let y : ℝ := 1
  let z := a * b
  have hx : 0 < x := by positivity
  have hy : (0 : ℝ) < y := by positivity
  have hz : 0 < z := by positivity
  have pos : 0 < x * y * z := by positivity
  have h1 : a = x / y := by ring
  have h2 : b = z / x := by field_simp; ring
  have h3 : c = y / z := by
    field_simp
    ring
    rw [mul_comm c a, mul_assoc, mul_comm c b, ← mul_assoc]
    exact h

  rw [h1, h2, h3]
  -- field_simp

  have eq1 : x / y + y / z + z / x + 1 / (x / y) + 1 / (y / z) + 1 / (z / x) = (x ^ 2 * z + x * z ^ 2 + y ^ 2 * z + y * z ^ 2 + x ^ 2 * y + x * y ^ 2) / (x * y * z) := by
    field_simp [hx, hy, hz]
    ring
  have eq2 : 3 + x / y / (z / x) + z / x / (y / z) + y / z / (x / y) = (3 * x * y * z + x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) := by
    field_simp [hx, hy, hz, pow_three]
    ring

  have schur : x^2 * z + x * z^2 + y^2 * z + y * z^2 + x^2 * y + x * y^2 ≤ 3 * x * y * z + x^3 + y^3 + z^3 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_self_nonneg (x - y + z), mul_self_nonneg (y - z + x), mul_self_nonneg (z - x + y)]

  rw [← div_le_div_iff_of_pos_right pos] at schur
  nlinarith




-- theorem schur (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a * (a-b) * (a-c) + b * (b-a) * (b-c) + c * (c-a) * (c-b) ≥ 0 := by
--   nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
--     mul_self_nonneg (a - b + c), mul_self_nonneg (b - c + a), mul_self_nonneg (c - a + b)]



-- theorem schur_p3 (a b c: ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : a^2 + b^2 + c^2 + 3 ≥ 2 * (1 / a + 1 / b + 1 / c) := by
--   have schur : (a + b + c)^3 + 9 * a * b * c ≥ 4 * (a * b + b * c + c * a) * (a + b + c) := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_self_nonneg (a - b + c), mul_self_nonneg (b - c + a), mul_self_nonneg (c - a + b)]
--   have ineq1 :
