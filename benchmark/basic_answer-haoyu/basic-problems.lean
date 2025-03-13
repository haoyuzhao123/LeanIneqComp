import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem basic_p1_pow (x : ℝ) (h : x > 0 ) (H : Real.sqrt x ≤ 1) : x ≤ 1 := by
  rw [Real.sqrt_le_iff] at H
  linarith

theorem basic_p2_pow (x : ℝ) (h : x > 0 ) (H : Real.sqrt x ≤ 3) : x ≤ 9 := by
  rw [Real.sqrt_le_iff] at H
  linarith

theorem basic_p3_pow (x : ℝ) (h : x > 0 ) (H : x ^ ((3:ℝ )⁻¹) ≤ 1) : x ≤ 1 := by
  have h' : (x ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 1 ^ 3 := by gcongr
  have g : x ≤ 1 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x = (x ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [h.le]
      _ ≤ 1 ^ 3 := h'
      _ = 1 := by norm_num
  exact g

theorem basic_p4_pow (x : ℝ) (h : x > 0 ) (H : x ^ ((3:ℝ )⁻¹) ≤ 2) : x ≤ 8 := by
  have h' : (x ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 2 ^ 3 := by gcongr
  have g : x ≤ 8 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x = (x ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [h.le]
      _ ≤ 2 ^ 3 := h'
      _ = 8 := by norm_num
  exact g

theorem basic_p5_pow (x : ℝ) (h : x > 0 ) (H : x ^ ((3:ℝ )⁻¹) ≤ 3) : x ≤ 27 := by
  have h' : (x ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 3 ^ 3 := by gcongr
  have g : x ≤ 27 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x = (x ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [h.le]
      _ ≤ 3 ^ 3 := h'
      _ = 27 := by norm_num
  exact g

theorem basic_p6_pow (x : ℝ) (h : x > 0 ) (H : x ^ ((4:ℝ )⁻¹) ≤ 2) : x ≤ 16 := by
  have h' : (x ^ ((4:ℝ )⁻¹)) ^ 4 ≤ 2 ^ 4 := by gcongr
  have g : x ≤ 16 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x = (x ^ ((4:ℝ )⁻¹)) ^ 4 := by rw [← Real.rpow_natCast] ; simp [h.le]
      _ ≤ 2 ^ 4 := h'
      _ = 16 := by norm_num
  exact g

theorem basic_p7_pow (x : ℝ) (h : x > 0 ) (H : x ^ ((5:ℝ )⁻¹) ≤ 2) : x ≤ 32 := by
  have h' : (x ^ ((5:ℝ )⁻¹)) ^ 5 ≤ 2 ^ 5 := by gcongr
  have g : x ≤ 32 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x = (x ^ ((5:ℝ )⁻¹)) ^ 5 := by rw [← Real.rpow_natCast] ; simp [h.le]
      _ ≤ 2 ^ 5 := h'
      _ = 32 := by norm_num
  exact g

theorem basic_p8_pow (x : ℝ) (h : x > 0 ∧ y > 0 ) (H : (x * y) ^ ((3:ℝ )⁻¹) ≤ 2) : x * y ≤ 8 := by
  have xypos : x * y > 0 := by nlinarith
  have h' : ((x * y) ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 2 ^ 3 := by gcongr
  have g : x * y ≤ 8 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x * y = ( (x * y) ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [xypos.le]
      _ ≤ 2 ^ 3 := h'
      _ = 8 := by norm_num
  exact g

theorem basic_p9_pow (x : ℝ) (h : x > 0 ∧ y > 0 ) (H : (x * y) ^ ((3:ℝ )⁻¹) ≤ 2) : x * y ≤ 8 := by
  have xypos : x * y > 0 := by nlinarith
  have h' : ((x * y) ^ ((3:ℝ )⁻¹)) ^ 3 ≤ 2 ^ 3 := by gcongr
  have g : x * y ≤ 8 := by
    -- following line Real.rpow_natCast is the newest function
    -- however for previous version of Mathlib4, the function is Real.rpow_nat_cast
    -- Models (STP and Goedel prover) output the older version
    calc x * y = ( (x * y) ^ ((3:ℝ )⁻¹)) ^ 3 := by rw [← Real.rpow_natCast] ; simp [xypos.le]
      _ ≤ 2 ^ 3 := h'
      _ = 8 := by norm_num
  exact g

theorem basic_p10_pow (x : ℝ) (h : x > 0 ∧ y > 0 ) (H : Real.sqrt x ≤ 2) (G : Real.sqrt y ≤ 3) : x * y ≤ 36 := by
  have hx : x ≤ 4 := by
    rw [Real.sqrt_le_iff] at H
    linarith
  have hy : y ≤ 9 := by
    rw [Real.sqrt_le_iff] at G
    linarith
  nlinarith
