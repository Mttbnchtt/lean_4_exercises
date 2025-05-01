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



theorem theorem_1_1_0
  (a b : ℚ)
  (hyp_1 : a - b = 4)
  (hyp_2 : a*b = 1)
  : (a + b)^2 = 20 := by

    suffices h2: (a + b)^2 - (a-b)^2= 20 - (a-b)^2 by sorry

    have h: (a+b)^2 - (a-b)^2 = 4*a*b := by ring_nf


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


-- -----------------------------
theorem theorem_1_1_2 (
  r s : ℝ)
  (hyp_1 : r + 2*s = -1)
  (hyp_2: s = 3)
  : r = -7 := by
  calc
    r = r + 2*s - 2*s := by exact Eq.symm (add_sub_cancel_right r (2 * s))
    _ = -1 - 2*s := by rw [hyp_1]
    _ = -1 - 2*3 := by rw [hyp_2]
    _ = -1 -6 := by ring
    _ = -7 := by ring


  -- -----------------------------
theorem theorem_1_1_3
  (a b m n : ℤ)
  (hyp_1 : b^2 = 2*a^2)
  (hyp_2 : a*m + b*n = 1)
  : (2*a*n + b*m)^2 = 2 := by
  calc
    (2*a*n + b*m)^2 = 4*a^2*n^2 + 4*a*n*b*m + b^2*m^2 := by ring
    _               = 2*2*a^2*n^2 + 4*a*n*b*m + b^2*m^2 := by ring
    _               = 2*(2*a^2)*n^2 + 4*a*n*b*m + b^2*m^2 := by ring
    _               = 2*b^2*n^2 + 4*a*n*b*m + b^2*m^2 := by rw [hyp_1]
    _               = 2*b^2*n^2 + 4*a*n*b*m + 2*a^2*m^2 := by rw [hyp_1]
    _               = 2*( b^2*n^2 + 2*a*n*b*m + a^2*m^2 ) := by ring
    _               = 2*( b*n + a*m )^2 := by ring
    _               = 2*( a*m + b*n )^2 := by ring
    _               = 2*1^2 := by rw [hyp_2]
    _               = 2*1 := by ring
    _               = 2 := by ring


  -- -----------------------------
theorem theorem_1_1_4
  (a b c d e f : ℤ)
  (hyp_1 : a*d = b*c)
  (hyp_2 : c*f = d*e)
  : d*(a*f - b*e) = 0 := by
  calc
    d*(a*f - b*e) = d*a*f - d*b*e     := by ring
    _             = (a*d)*f - d*b*e   := by ring
    _             = (b*c)*f - d*b*e   := by rw [hyp_1]
    _             = b*(c*f) - d*b*e   := by ring
    _             = b*(d*e) - d*b*e   := by rw [hyp_2]
    _             = b*d*e - d*b*e     := by ring
    _             = b*d*e - b*d*e     := by ring
    _             = 0                 := by ring


  -- -----------------------------
theorem theorem_1_3_1
  (a b : ℤ)
  (hyp_1 : a = 2*b + 5)
  (hyp_2 : b = 3)
  : a = 11 := by
  calc
    a = 2*b + 5 := by rw [hyp_1]
    _ = 2*3 + 5 := by rw [hyp_2]
    _ = 6 + 5 := by decide
    _ = 11 := by decide


-- -----------------------------
  theorem theorem_1_3_2
    (x : ℤ)
    (hyp_1 : x + 4 = 2)
    : x = -2 := by
    calc
      x = x + 4 - 4 := by exact Eq.symm (Int.add_sub_cancel x 4)
      _ = 2 - 4 := by rw [hyp_1]
      _ = -2 := by decide

-- -----------------------------
theorem theorem_1_3_3
  (a b : ℝ)
  (hyp_1 : a - 5*b = 4)
  (hyp_2 : b + 2 = 3)
  : a = 9 := by
  calc
    a = a - 5*b + 5*b := by exact Eq.symm (sub_add_cancel a (5 * b))
    _ = 4 + 5*b := by rw [hyp_1]
    _ = 4 + 5*(b + 2 - 2) := by ring
    _ = 4 + 5*(b+2) + 5*(-2) := by ring
    _ = 4 + 5*3 + 5*(-2) := by rw [hyp_2]
    _ = 4 + 15 + 5*(-2) := by ring
    _ = 19 + 5*(-2) := by ring
    _ = 19 - 10 := by ring
    _ = 9 := by ring

-- -----------------------------
theorem theorem_1_3_4
  (w : ℚ)
  (hyp_1 : 3*w + 1 = 4)
  : (w = 1) := by
  calc
    w = (3*w)/3 := by ring
    _ = (3*w + 1 - 1)/3 := by ring
    _ = (4 - 1)/3  := by rw [hyp_1]
    _ = 3/3 := by ring
    _ = 1 := by ring
