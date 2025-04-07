import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

-- 之前找的题

theorem p1_Serbia_2009 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = z * y + y * x + x * z) : 1 / (x^2 + y + 1) + 1 / (y^2 + z + 1) + 1 / (z^2 + x + 1) ≤ 1 := by sorry

theorem p2_USAMO_1978 (a b c d e : ℝ) (h : a + b + c + d + e = 8) (g : a^2 + b^2 + c^2 + d^2 + e^2 = 16) : 0 ≤ e ∧ e ≤ 16 / 5 := by sorry

theorem p3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x^2 + y^2 + z^2 = 1) : x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2) ≤ 3 * √3 / 2 := by sorry

theorem p4 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : √(a^2 + a*b + b^2) + √(b^2 + b*c + c^2) + √(c^2 + c*a + a^2) ≤ √(5 * (a^2 + b^2 + c^2) + 4 * (a*b + b*c + c*a)) := by sorry

theorem p5_JMO_2012 (a b c : ℝ) : (a^3 + 5 * b^3) / (3 * a + b) + (b^3 + 5 * c^3) / (3 * b + c) + (c^3 + 5 * a^3) / (3 * c + a) ≥ 3 / 2 * (a^2 + b^2 + c^2) := by sorry

-- 以下两题来自 https://zhuanlan.zhihu.com/p/217473917, 感觉有点困难

theorem p6 (a b c d : ℝ) (h : a * b * c * d ≥ 1) : (a * b) * (b * c) * (c * d) * (d * a) ≥ (a + 1) * (b + 1) * (c + 1) * (d + 1) := by sorry

theorem p7 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 3) : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) + 11 * a * b * c ≤ 12 := by sorry

-- 以下来自高考, 可参考 https://www.doc88.com/p-98139597004606.html

theorem p8_gaokao_19 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / a + 1 / b + 1 / c ≤ a^2 + b^2 + c^2 := by sorry

theorem p9_gaokao_19 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a * b * c = 1) : (a + b)^3 + (b + c)^3 + (c + a)^3 ≥ 24 := by sorry

theorem p10_gaokao_20 (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : a * b = 1) : 1 / (2 * a) + 1 / (2 * b) + 8 / (a + b) ≥ 4 := by sorry

theorem p11_gaokao_19 (x y : ℝ) (hx : x > 0) (hy : y > 0) (h : x + 2 * y = 5) : (x + 1) * (2 * y + 1) / √(x * y) ≥ 4 * √3 := by sorry

theorem p12_gaokao_17 (a b : ℝ) (hab : a * b > 0) : (a^4 + 4 * b^4 + 1) / (a * b) ≥ 4 := by sorry

theorem p13_gaokao_20 (x y : ℝ) (h : 5 * x^2 * y^2 + y^4 = 1) : x^2 + y^2 ≥ 4 / 5 := by sorry

theorem p14_gaokao_21 (a b : ℝ) (ha : a > 0) (hb : b > 0) : 1 / a + a / b^2 + b ≥ 2 * √2 := by sorry

theorem p15_gaokao_18 (a b : ℝ) (h : a - 3 * b + 6 = 0) : (2 : ℝ) ^ a + 1 / ((8 : ℝ) ^ b) ≥ 1 / 4 := by sorry
