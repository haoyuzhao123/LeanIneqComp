import Mathlib
import Aesop

set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem cauchy_p4 (x y: ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hx1 : x ≤ 1) (hy1 : y ≤ 1) : x * √(1 - y^2) + y * √(1 - x^2) ≤ 1 := by
  -- first prove the helper lemma
  have le_of_sq_le_sq (la lb : ℝ) (lh : la ^ 2 ≤ lb ^ 2) (hlb : 0 ≤ lb) : la ≤ lb := le_abs_self la |>.trans <| abs_le_of_sq_le_sq lh hlb

  apply le_of_sq_le_sq
  convert_to (∑ i : Fin 2, ![x, √(1 - x^2)] i * ![√(1 - y^2), y] i)^2 ≤
          (∑ i : Fin 2, (![x, √(1 - x^2)] i)^2) *
          (∑ i : Fin 2, (![√(1 - y^2), y] i)^2)
  simp [Fin.sum_univ_two]
  field_simp; rw [mul_comm]
  simp [Fin.sum_univ_two]
  rw [sq_sqrt, sq_sqrt]
  ring
  nlinarith; nlinarith
  apply Finset.sum_mul_sq_le_sq_mul_sq
  norm_num
