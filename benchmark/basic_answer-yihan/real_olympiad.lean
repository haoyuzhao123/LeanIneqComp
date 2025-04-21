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

-- 以下来自 https://www.doc88.com/p-37216351366075.html

theorem p16 (n : ℕ) (hn : n > 0) (a b : Fin n → ℝ) : (∑ i : Fin n, (a i * b i)) + √((∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (b i)^2)) ≥ 2 / n * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by sorry

theorem p17 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 2 * a^2 / (1 + a + a * b)^2 + 2 * b^2 / (1 + b + b * c)^2 + 2 * c^2 / (1 + c + c * a)^2 + 9 / ((1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a)) ≥ 1 := by sorry

theorem p18 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (√(x^2 + y^2) + √(y^2 + 4 * z^2) + √(z^2 + 16 * x^2)) / (9 * x + 3 * y + 5 * z) ≥ √5 / 5 := by sorry

theorem p19 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (b + c) + b / (c + a) + 2 * c / (a + b) ≥ 2 := by sorry

theorem p20 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : a^2 / b + b^2 / c + c^2 / a ≥ a + b + c + 4 * (a - b)^2 / (a + b + c) := by sorry

-- 以下来自网盘

theorem p21 (x y : ℝ) (h : x^2 + y^2 ≥ 1) : 1 / 2 ≤ x^2 - x * y + y^2 := by sorry

theorem p22 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : Real.log a + Real.log b + Real.log c ≤ Real.log ((a + b) / 2) + Real.log ((b + c) / 2) + Real.log ((c + a) / 2) := by sorry

-- 以下来自小蓝书, 后缀为章-节-题号

theorem p23_amgm_2_1_4 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a > b) : √2 * a^3 + 3 / (a * b - b^2) ≥ 10 := by sorry

theorem p24_amgm_2_1_5 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : c / a + a / (b + c) + b / c ≥ 2 := by sorry

theorem p25_amgm_2_1_15 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 + c^2 = 1) : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ 3 * √3 / 2 := by sorry

theorem p26_amgm_2_2_1 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + 3 * c) / (a + 2 * b + c) + 4 * b / (a + b + 2 * c) - 8 * c / (a + b + 3 * c) ≥ -17 + 12 * √2 := by sorry

theorem p27_amgm_2_2_7 (a b c d : ℝ) : a^6 + b^6 + c^6 + d^6 - 6 * a * b * c * d ≥ -2 := by sorry

theorem p28_amgm_2_2_8 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a * b * c) : a^7 *(b * c - 1) + b^7 *(c * a - 1) + c^7 *(a * b - 1) ≥ 162 * √3 := by sorry

theorem p29_amgm_2_2_11 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) + (a + b + c) ≥ 100 := by sorry

theorem p30_amgm_2_4_1 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 + c^2 = 3) : 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) ≥ 1 := by sorry

theorem p31_amgm_2_4_3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x^2 + y^2 + z^2 = 1) : x^2 * y * z + x * y^2 * z + x * y * z^2 ≤ 1 / 3 := by sorry

theorem p32_cauchy_4_1_16 (n : ℕ) (hn : n > 0) (a b c d : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (hc : ∀ i, c i > 0) (hd : ∀ i, d i > 0) : (∑ i : Fin n, (a i) * (b i) * (c i) * (d i))^4 ≤ (∑ i : Fin n, (a i)^4) * (∑ i : Fin n, (b i)^4) * (∑ i : Fin n, (c i)^4) * (∑ i : Fin n, (d i)^4) := by sorry

theorem p33_cauchy_4_1_23 (n : ℕ) (k : ℝ) (a : Fin n → ℝ) (hn : n > 0) (hk : k > 0) (ha : ∀ i, a i > 0) (h : ∑ i : Fin n, a i = k) : ∑ i : Fin n, (a i + 1 / a i)^2 ≥ n * ((n^2 + k^2) / (n * k))^2 := by sorry

theorem p34_cauchy_4_2_8 (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : a + b = 1) : (a + 1 / a)^2 + (b + 1 / b)^2 ≥ 25 / 2 := by sorry

theorem p35_cauchy_4_2_12 (x y z : ℝ) (hx : x > -1) (hy : y > -1) (hz : z > -1) : (1 + x^2) / (1 + y + z^2) + (1 + y^2) / (1 + z + x^2) + (1 + z^2) / (1 + x + y^2) ≥ 2 := by sorry

theorem p36_cauchy_4_3_2 (n : ℕ) (hn : n ≥ 2) (a : Fin n → ℝ) (ha : ∀ i, a i > 0) (h : ∑ i : Fin n, a i = 1) : ∑ i : Fin n, (a i / (2 - a i)) ≥ n / (2 * n - 1) := by sorry

theorem p37_cauchy_4_3_5 (n : ℕ) (hn : n ≥ 2) (x : Fin n → ℝ) (hx : ∀ i, x i > 0) (h : ∑ i : Fin n, x i = 1) : ∑ i : Fin n, (x i / √(1 - x i)) ≥ 1 / √(n - 1) * ∑ i : Fin n, √(x i) := by sorry

theorem p38_cauchy_4_3_13 (x y z w : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) : x / (y + 2 * z + 3 * w) + y / (z + 2 * w + 3 * x) + z / (w + 2 * x + 3 * y) + w / (x + 2 * y + 3 * z) ≥ 2 / 3 := by sorry

theorem p39_cauchy_4_6_1 (a b c : ℝ) (h : a^2 + 2 * b^2 + 3 * c^2 = 3 / 2) : (3 : ℝ)^(-a) + (9 : ℝ)^(-b) + (27 : ℝ)^(-c) ≥ 1 := by sorry

theorem p40_cauchy_4_6_2 (x y : ℝ) (hx : x^2 ≤ 1) (hy : y^2 ≤ 1) : x * √(1 - y^2) + y * √(1 - x^2) ≤ 1 := by sorry

theorem p41_cauchy_4_6_3 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) ≥ 3 / 2 := by sorry

theorem p42_mix_1_1_2 (x y z : ℝ) (h : x * y + y * z + z * x = -1) : x^2 + 5 * y^2 + 8 * z^2 ≥ 4 := by sorry

theorem p43_mix_1_1_5 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : 1 / a^2 + 1 / b^2 + 1 / c^2 - 2 * (a^3 + b^3 + c^3) / (a * b * c) ≥ 3 := by sorry

theorem p44_mix_1_2_7 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) + 1 / (c^3 + a^3 + a * b * c) ≤ 1 / (a * b * c) := by sorry

theorem p45_mix_1_3_13 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c - 3 * (a * b * c) ^ (3⁻¹: ℝ) ≥ a + b - 2 * √(a * b) := by sorry

theorem p46_mix_1_6_25 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 1) : y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by sorry

theorem p47_mix_1_6_26 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = x * y * z) : x^2 + y^2 + z^2 - 2 * (y * z + z * x + x * y) + 9 ≥ 0 := by sorry

theorem p48_mix_1_7_28 (a b : ℝ) (ha : a > 0) (hb : b > 0) : (a + 1)^2 / b + (b + 3)^2 / a ≥ 16 := by sorry

theorem p49_mix_3_1_7 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by sorry

theorem p50_mix_3_1_9 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (y^2 - x^2) / (z + x) + (z^2 - y^2) / (x + y) + (x^2 - z^2) / (y + z) ≥ 0 := by sorry


-- 以下为替换的题，来自 Inequalities (Problems and Solutions) by Keith Ong

theorem p9_1_Pathfinder (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤ 2 * (a / b + b / c + c / a) := by sorry

theorem p21_4_folklore (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : (a + 1 / b) * (b + 1 / c) * (c + 1 / a) ≥ 1000 / 27 := by sorry

theorem p10_5_india_2002 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / b + b / c + c / a ≥ (a + c) / (b + c) + (b + a) / (c + a) + (c + b) / (a + b) := by sorry

theorem p31_8 (a b c : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : √(a - 1) + √(b - 1) + √(c - 1) ≤ √(c * (a * b + 1)) := by sorry

theorem p49_10 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d) := by sorry

theorem p50_13 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b * c * d = 1) : 1 / (5 * a^2 - 2 * a + 1) + 1 / (5 * b^2 - 2 * b + 1) + 1 / (5 * c^2 - 2 * c + 1) + 1 / (5 * d^2 - 2 * d + 1) ≥ 1 := by sorry

theorem p14_15 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / (a^2 + b^2 + a * b) + 1 / (b^2 + c^2 + b * c) + 1 / (c^2 + a^2 + c * a) ≥ 9 / (a + b + c) := by sorry

theorem p2_22_folklore (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) ≥ 2 := by sorry

theorem p8_25_german_tst2012 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 + c^2 ≥ 3) : (a + 1) * (b + 2) / ((b + 1) * (b + 5)) + (b + 1) * (c + 2) / ((c + 1) * (c + 5)) + (c + 1) * (a + 2) / ((a + 1) * (a + 5)) ≥ 3 / 2 := by sorry

theorem p44_27 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 3) : 1 / (1 + a^2 * (b + c)) + 1 / (1 + b^2 * (c + a)) + 1 / (1 + c^2 * (a + b)) ≤ 1 / (a * b * c) := by sorry

theorem p47_28 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1) : √(3 * a^2 + b^2) / (a * b) + √(3 * b^2 + c^2) / (b * c) + √(3 * c^2 + a^2) / (c * a) ≥ 6 * √3 := by sorry

theorem p13_30_APMO2004 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 * (a + b + c)^2 := by sorry

theorem p30_33 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1) : a * b * c * (a + √(a^2 + 1)) * (b + √(b^2 + 1)) * (b + √(b^2 + 1)) ≤ 1 := by sorry

theorem p34_34_romania2002 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (ha1 : a < 1) (hb1 : b < 1) (hc1 : c < 1) : √(a * b * c) + √((1 - a) * (1 - b) * (1 - c)) ≤ 1 := by sorry

theorem p38_37 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = z * y + y * x + x * z) : (x + y) / (1 + z^2) + (y + z) / (1 + x^2) + (z + x) / (1 + y^2) ≥ 27 / (2 * x * y * z) := by sorry

theorem p26_39_imo1996 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : a * b / (a^5 + b^5 + a * b) + b * c / (b^5 + c^5 + b * c) + c * a / (c^5 + a^5 + c * a) ≤ 1 := by sorry
