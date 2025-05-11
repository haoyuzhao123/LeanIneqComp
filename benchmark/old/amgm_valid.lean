import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amgm_p1 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) / 3 ≥ (x * y * z) ^ (3⁻¹: ℝ ) := by
  sorry

theorem amgm_p2 (x y: ℝ) (hx : x > 0) (hy : y > 0) : (2 * x + y) / 3 ≥ (x * x * y) ^ (3⁻¹: ℝ ) := by
  sorry

theorem amgm_p3 (x y z w: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : (x + y + z + w) / 4 ≥ (x * y * z * w) ^ (4⁻¹: ℝ ) := by
  sorry

theorem amgm_p4 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x + (1:ℝ) / 3 * y  ≥ x^((2:ℝ) / 3) * y^((1:ℝ) / 3) := by
  sorry

theorem amgm_p5 (x y: ℝ )  (h : x > 0 ∧ y> 0): (4:ℝ) / 7 * x + (3:ℝ) / 7 * y  ≥ x^((4:ℝ) / 7) * y^((3:ℝ) / 7) := by
  sorry

theorem amgm_p6 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (2:ℝ)/5 * x + (2:ℝ)/5 * y + (1:ℝ)/5 * z ≥ x ^ ((2:ℝ)/5) * y ^ ((2:ℝ)/5) * z ^ ((1:ℝ)/5) := by
  sorry

theorem amgm_p7 (x y z w: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : (1:ℝ)/3 * x + (1:ℝ)/3 * y + (1:ℝ)/6 * z + (1:ℝ)/6 * w ≥ x ^ ((1:ℝ)/3) * y ^ ((1:ℝ)/3) * z ^ ((1:ℝ)/6) * w ^ ((1:ℝ)/6) := by
  sorry

theorem amgm_p8 (x y z: ℝ ) (h₁: x+ y + z = 3) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): (x * y * z) ^ (3⁻¹: ℝ ) ≤ 1 := by
  sorry

theorem amgm_p9 (x y: ℝ ) (h₁: x+ 2 * y = 3) (h₂ : x > 0 ∧ y> 0): (x * y ^ 2) ^ (3⁻¹: ℝ ) ≤ 1 := by
  sorry

theorem amgm_p10 (x y: ℝ ) (h₁: x+ 2 * y = 3) (h₂ : x > 0 ∧ y> 0): x * y ^ 2 ≤ 1 := by
  sorry

theorem amgm_p11 (x y z: ℝ ) (h₁: x+ y + z = 3) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): x * y * z ≤ 1 := by
  sorry

theorem amgm_p12 (x y z: ℝ ) (h₁: x+ 2 * y + 2 * z = 10) (h₂ : x > 0 ∧ y> 0 ∧ z> 0): x * y ^ 2 * z ^ 2 ≤ 32 := by
  sorry

theorem amgm_p13 (x y: ℝ )  (h : x > 0 ∧ y> 0): (4:ℝ) / 5 * x ^ 5 + (1:ℝ) / 5 * y ^ 5  ≥ x^4 * y := by
  sorry

theorem amgm_p14 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x ^ 6 + (1:ℝ) / 3 * y ^ 6  ≥ x^4 * y^2 := by
  sorry

theorem amgm_p15 (x y: ℝ )  (h : x > 0 ∧ y> 0): (4:ℝ) / 7 * x ^ 7 + (3:ℝ) / 7 * y ^ 7  ≥ x^4 * y^3 := by
  sorry

theorem amgm_p16 (x y: ℝ )  (h : x > 0 ∧ y> 0): (2:ℝ) / 3 * x ^ 3 + (1:ℝ) / 3 * y ^ 3  ≥ x^2 * y := by
  sorry

theorem amgm_p17 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (1:ℝ) / 2 * x ^ 4 + (1:ℝ) / 4 * y ^ 4 + (1:ℝ) / 4 * z ^ 4 ≥ x^2 * y * z := by
  sorry

theorem amgm_p18 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0): (2:ℝ) / 5 * x ^ 5 + (2:ℝ) / 5 * y ^ 5 + (1:ℝ) / 5 * z ^ 5 ≥ x^2 * y^2 * z := by
  sorry

theorem amgm_p19 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (3:ℝ)/5 * x^5 + (1:ℝ)/5 * y^5 + (1:ℝ)/5 * z^5 ≥ x ^ 3 * y * z := by
  sorry

theorem amgm_p20 (x y z w: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : (1:ℝ)/3 * x^6 + (1:ℝ)/3 * y^6 + (1:ℝ)/6 * z^6 + (1:ℝ)/6 * w^6 ≥ x^2 * y^2 * z * w := by
  sorry

theorem amgm_p21 (x y z: ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (2:ℝ)/3 * x^2 + (1:ℝ)/6 * y^2 + (1:ℝ)/6 * z^2 ≥ x^((4:ℝ)/3) * y^((1:ℝ)/3) * z^((1:ℝ)/3) := by
  sorry


theorem amgm_p22 (x y z: ℝ )  (h : x > 0 ∧ y> 0 ∧ z> 0) (g : x * y * z = (1 : ℝ)) : (4:ℝ) / 7 * x^3 * y + (1:ℝ) / 7 * y^3 * z + (2:ℝ) / 7 * z^3 * x ≥ x := by
  sorry

theorem amgm_p23 (a b c d: ℝ)  (ap : a > 0)  (bp : b> 0) (cp : c> 0) ( dp : d> 0) (g : a * b * c * d = (1 : ℝ)) : (23:ℝ) / 51 * a^4 * b + (7:ℝ) / 51 * b^4 * c + (11:ℝ) / 51 * c^4 * d + (10:ℝ) / 51 * d^4 * a ≥ a := by
  sorry

theorem amgm_p24 (a b c : ℝ) (ap : a > 0) (bp : b> 0) (cp : c> 0) : a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a := by
  sorry

theorem amgm_p25 (a b c : ℝ) (ap : a > 0) (bp : b> 0) (cp : c> 0) : a^7 + b^7 + c^7 ≥ a^4 * b^3 + b^4 * c^3 + c^4 * a^3 := by
  sorry
