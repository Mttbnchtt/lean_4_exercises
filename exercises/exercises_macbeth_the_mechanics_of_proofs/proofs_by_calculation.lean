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

    suffices h2: (a + b)^2 - (a-b)^2 = 20 - (a-b)^2 by
      simp at h2
      exact h2

    have h: (a+b)^2 - (a-b)^2 = 4*a*b := by ring_nf
    rw [h]

    have h3: 4*a*b = 4*(a*b) := by ring
    rw [h3]
    rw [hyp_2]
    simp
    rw [hyp_1]
    ring_nf


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

-- -----------------------------
theorem theorem_1_3_5
  (x : ℤ)
  (hyp_1 : 2*x + 3 = x)
  : x = -3 := by
  calc
    x = x + x - x := by ring
    _ = x + x - x + 3 - 3 := by ring
    _ = 2*x - x + 3 - 3 := by ring
    _ = 2*x + 3 -x -3 := by ring
    _ = x - x - 3 := by rw [hyp_1]
    _ = -3 := by ring

-- -----------------------------
theorem theorem_1_3_6
  (x y : ℤ)
  (hyp_1: 2*x - y = 4)
  (hyp_2 : y - x + 1 = 2)
  : x = 5 := by
  calc
    x = x + x -x := by ring
    _ = 2*x - x := by ring
    _ = 2*x - x + y - y := by ring
    _ = 2*x - y + y - x := by ring
    _ = 4 + y - x := by rw [hyp_1]
    _ = 4 + y -x + 1 - 1 := by ring
    _ = 4 + (y -x + 1) -1 := by ring
    _ = 4 + 2 - 1 := by rw [hyp_2]
    _ = 5 := by norm_num
-- https://leanprover-community.github.io/mathlib_docs/tactic/norm_num.html

theorem theorem_1_3_6_v2
  (x y : ℤ)
  (hyp_1 : 2*x - y = 4)
  (hyp_2 : y - x + 1 = 2)
  : x = 5 := by
  linarith [hyp_1, hyp_2]
-- https://leanprover-community.github.io/mathlib_docs/tactic/linarith/frontend.html

-- -----------------------------
theorem theorem_1_3_7
  (u v : ℚ)
  (hyp_1 : u + 2*v = 4)
  (hyp_2 : u - 2*v = 6)
  : u = 5 := by
  calc
    u = (2*u) / 2 := by ring
    _ = (u + u) / 2:= by ring
    _ = (u + u + 2*v - 2*v) / 2 := by ring
    _ = (u + 2*v + u - 2*v) / 2 := by ring
    _ = (4 + u - 2*v) / 2 := by rw [hyp_1]
    _ = (4 + (u - 2*v)) / 2 := by ring
    _ = (4 + 6) / 2 := by rw [hyp_2]
    _ = 10 / 2 := by ring
    _ = 5 := by ring

-- -----------------------------
theorem theorem_1_3_8
  (x y : ℝ)
  (hyp_1 : x + y = 4)
  (hyp_2 : 5*x - 3*y = 4)
  : x = 2 := by
  calc
    x = (8*x) / 8 := by ring
    _ = (3*x + 5*x) /8 := by ring
    _ = (3*x + 5*x - 3*y + 3*y) / 8 := by ring
    _ = (3*x + 3*y + 5*x - 3*y) / 8 := by ring
    _ = ((3*x + 3*y) + (5*x - 3*y)) / 8 := by ring
    _ = (3*(x + y) + (5*x - 3*y)) / 8 := by ring
    _ = (3*4 + (5*x - 3*y)) / 8 := by rw [hyp_1]
    _ = (3*4 + 4) / 8 := by rw [hyp_2]
    _ = 2 := by ring

-- -----------------------------
theorem theorem_1_3_9
  (a b : ℚ)
  (hyp_1 : a - 3 = 2*b)
  : a^2 - a + 3 = 4*b^2 +10*b + 9 := by
  calc
    a^2 - a + 3 = a^2 - (a - 3) := by ring
    _           = a^2 - 2*b := by rw [hyp_1]
    _           = a^2 - 9 + 9 - 2*b := by ring
    _           = (a - 3) * (a + 3) + 9 - 2*b := by ring
    _           = 2*b * (a + 3) + 9 - 2*b := by rw [hyp_1]
    _           = 2*b * (a - 3 + 3 + 3) + 9 - 2*b := by ring
    _           = 2*b * (a - 3 + 6) + 9 - 2*b := by ring
    _           = 2*b * (2*b + 6) + 9 - 2*b := by rw [hyp_1]
    _           = 4*b^2 + 12*b + 9 - 2*b := by ring
    _           = 4*b^2 + 10*b + 9 := by ring

-- -----------------------------
theorem theorem_1_3_10
  (x : ℝ)
  (hyp_1 : z^2 - 2 = 0)
  : z^4 - z^3 - z^2 + 2*z +1 = 3 := by
  calc
    z^4 - z^3 - z^2 + 2*z +1  = z^4 - 4 + 4 - z^3 - z^2 + 2*z +1              := by ring
    _                         = (z^2 - 2) * (z + 2) + 4 - z^3 - z^2 + 2*z +1  := by ring
    _                         = 4 - z^3 - z^2 + 2*z + 1                       := by rw [hyp_1]
    _                         = 5 - z^3 - z^2 + 2*z                           := by ring
    _                         = 5 - z^3 + 2*z - z^2                           := by ring
    _                         = 5 - z * (z^2 -2) - z^2                        := by ring
    _                         = 5 - z^2                                       := by rw [hyp_1]
    _                         = 5 - z^2 + 2 - 2                               := by ring
    _                         = 3 - z^2 + 2                                   := by ring
    _                         = 3 - (z^2 - 2)                                 := by ring
    _                         = 3                                             := by rw [hyp_1]

-- -----------------------------
theorem theorem_1_3_11_1
  (x y : ℝ)
  (hyp_1 : x = 3)
  (hyp_2 : y = 4*x -3)
  : y = 9 := by
  calc
    y = 4*x - 3 := by rw [hyp_2]
    _ = 4*3 - 3 := by rw [hyp_1]
    _ = 9 := by ring

-- -----------------------------
  theorem theorem_1_3_11_2
    (a b : ℤ)
    (h : a - b = 0)
    : a = b := by
    calc
      a = a -b + b := by ring
      _ = 0 + b := by rw [h]
      _ = b := by ring

-- -----------------------------
  theorem theorem_1_3_11_3
    (x y : ℤ)
    (h1 : x - 3*y = 5)
    (h2 : y = 3)
    : x = 14 := by
    calc
      x = x - 3*y + 3*y := by ring
      _ = 5 + 3*y := by rw [h1]
      _ = 5 + 3*3 := by rw [h2]
      _ = 14 := by ring

-- -----------------------------
theorem theorem_1_3_11_4
  (p q : ℚ)
  (h1 : p - 2*q = 1)
  (h2 : q = -1)
  : p = -1 := by
  calc
    p = p - 2*q + 2*q := by ring
    _ = 1 + 2*q := by rw [h1]
    _ = 1 - 2 := by rw [h2]
    _ = -1 := by ring

-- -----------------------------
theorem theorem_1_3_11_5
  (x y : ℚ)
  (h1 : y + 1 = 3)
  (h2 : x + 2*y = 3)
  : x = -1 := by
  calc
    x = x + 2*y - 2*y := by ring
    _ = (x + 2*y) - 2*y := by ring
    _ = 3 - 2*y := by rw [h1]
    _ = 3 - 2*y - 2 + 2 := by ring
    _ = 3 - 2*(y + 1) + 2 := by ring
    _ = 3 - 2*3 + 2 := by rw [h2]
    _ = 3 - 6 + 2 := by ring
    _ = -1 := by ring

-- -----------------------------
theorem theorem_1_3_11_6
  (p q : ℤ)
  (h1 : p + 4*q = 1)
  (h2 : q - 1 = 2)
  : p = -11 := by
  calc
    p = p + 4*q - 4*q := by ring
    _ = 1 - 4*q := by rw [h1]
    _ = 1 - 4*q + 4 - 4 := by ring
    _ = 1 - 4*(q - 1) - 4 := by ring
    _ = 1 - 4*2 - 4 := by rw [h2]
    _ = -11 := by ring

-- -----------------------------
theorem theorem_1_3_11_7
  (a b c : ℝ)
  (h1 : a + 2*b + 3*c = 7)
  (h2 : b + 2*c = 3)
  (h3 : c = 1)
  : a = 2 := by
  calc
  a = a + 2*b - 2*b := by ring
  _ = a + 2*b - 2*b + 3*c - 3*c := by ring
  _ = a + 2*b + 3*c - 2*b - 3*c := by ring
  _ = 7 - 2*b - 3*c := by rw [h1]
  _ = 7 - 2*b - 2*c - c := by ring
  _ = 7 - b - b - 2*c - c := by ring
  _ = 7 - b - (b + 2*c) - c := by ring
  _ = 7 -b - 3 - c := by rw [h2]
  _ = 7 - 3 - b - c := by ring
  _ = 4 -b - c := by ring
  _ = 4 - b - 1 := by rw [ h3]
  _ = 3 - b := by ring
  _ = 3 - b - 2*c + 2*c := by ring
  _ = 3 - (b + 2*c) + 2*c := by ring
  _ = 3 - 3 + 2*c := by rw [h2]
  _ = 2*c := by ring
  _ = 2*1 := by rw [h3]
  _ = 2 := by ring

-- -----------------------------
theorem theorem_1_3_11_8
  (u v : ℚ)
  (h1 : 4*u + v = 3)
  (h2 : v = 2)
  : u = 1/4 := by
  calc
    u = 4*u / 4 := by ring
    _ = (4*u + v - v) / 4 := by ring
    _ = (3 - v) / 4 := by rw [h1]
    _ = (3 - 2) / 4 := by rw [h2]
    _ = 1 / 4 := by ring

-- -----------------------------
theorem theorem_1_3_11_9
  (c : ℚ)
  (h1 : 4*c + 1 = 3*c -2)
  : c = -3 := by
  calc
    c = c + 1 - 1 := by ring
    _ = 4*c + 1 - 1 - 3*c := by ring
    _ = 3*c - 2 - 1 - 3*c := by rw [h1]
    _ = - 2 - 1 := by ring
    _ = - 3 := by ring

-- -----------------------------
  theorem theorem_1_3_11_10
    (p : ℝ)
    (h1 : 5*p - 3 = 3*p + 1)
    : p = 2 := by linarith [h1]











-- •	Option + Shift + DownArrow (⌥⇧↓) to copy the line below
-- •	Option + Shift + UpArrow (⌥⇧↑) to copy the line above  ￼
