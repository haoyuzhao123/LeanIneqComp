import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

-- 注：以下的题目名字没改

theorem cauchy_p5_Serbia_2009 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = z * y + y * x + x * z) : 1 / (x^2 + y + 1) + 1 / (y^2 + z + 1) + 1 / (z^2 + x + 1) ≤ 1 := by sorry


-- 需要 amgm
theorem cauchy_p7 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x^2 + y^2 + z^2 = 1) : x / (1 - x^2) + y / (1 - y^2) + z / (1 - z^2) ≤ 3 * √3 / 2 := by sorry


-- 需要 Chebyshev (排序那个)
theorem cauchy_p8 (a b c d : ℝ) (h : a * b + b * c + c * d + d * a = 1) : a^3 / (b + c + d) + b^3 / (c + d + a) + c^3 / (a + b + d) + d^3 / (a + b + c) ≥ 1 / 3 := by sorry


-- 这个会不会有点太难了？
theorem cauchy_p10 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : √(a^2 + a*b + b^2) + √(b^2 + b*c + c^2) + √(c^2 + c*a + a^2) ≤ √(5 * (a^2 + b^2 + c^2) + 4 * (a*b + b*c + c*a)) := by sorry
