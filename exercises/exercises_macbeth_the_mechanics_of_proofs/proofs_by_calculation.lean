import Mathlib

-- -----------------------------
-- 1.1.1
-- theorem
-- Let a and b be rational numbers.
-- Suppose that a-b = 4 and ab = 1.
-- Show that (a+b)^2 = 20.

-- proof
-- (a + b)^2  = a^2 + 2ab + b^2
--            = a^2 +2ab + b^2 +2ab - 2ab
--            = a^2 - 2ab + b^2 + 4ab
--            = (a - b)^2 + 4ab
--            = 4^2 + 4ab   [by a-b = 4 ]
--            = 16 + 4ab
--            = 16 + 4      [by ab = 1]
--            = 20

theorem theorem_1_1_1
  (a b : ℚ)
  (hyp_1 : a -b = 4)
  (hyp_2 : a*b = 1)
  : (a + b)^2 = 20 := by
  calc
    (a + b)^2 = a^2 + 2*a*b + b^2 := by exact add_pow_two a b
    _         = a^2 +2*a*b + b^2 +2*a*b - 2*a*b := by exact Eq.symm (add_sub_cancel_right (a ^ 2 + 2 * a * b + b ^ 2) (2 * a * b))
    _         = a^2 +2*a*b + b^2 - 2*a*b + 2*a*b := by simp
    _         = a^2 +2*a*b + (b^2 - 2*a*b) + 2*a*b := by ring
    _         = a^2 +2*a*b + (- 2*a*b + b^2) + 2*a*b := by ring
    _         = a^2 + (- 2*a*b + b^2) + 2*a*b + 2*a*b := by ring
    _         = a^2 + (- 2*a*b + b^2) + (2*a*b + 2*a*b) := by ring
    _         = a^2 + (- 2*a*b + b^2) + 4*a*b := by ring
    _         = (a^2 - 2*a*b + b^2) + 4*a*b := by ring
    _         = (a - b)^2 + 4*a*b := by ring
    _         = 4^2 + 4*a*b := by rw [hyp_1]
    _         = 16 + 4*a*b := by exact rfl
    _         = 16 + 4*(a*b) := by ring
    _         = 16 + 4*1 := by rw [hyp_2]
    _         = 16 + 4 := by simp
    _         = 20 := by norm_num
