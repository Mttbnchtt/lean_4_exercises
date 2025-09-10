import Mathlib

theorem theorem_2_1
  (a b : ℝ)
  (h1 : a - 5*b = 4)
  (h2 : b + 2 = 3)
  : a = 9 := by
    have h3 : b = 1 := by linarith [h2]
    calc
       a = a - 5*b + 5*b := by ring
       _ = 4 + 5*b := by rw [h1]
       _ = 4 + 5*1 := by rw [h3]
       _ = 9 := by linarith

-- -----------------------------
theorem theorem_2_1_2
  (m n :ℤ)
  (h1 : m + 3 ≤ 2*n - 1)
  (h2 : n ≤ 5)
  : m ≤ 6 := by
  have h3: m ≤ 2*n - 4 := by
    calc m = m + 3 - 3 := by ring
         _ ≤ 2*n - 1 - 3 := by rel [h1]
         _ ≤ 2*n - 4 := by linarith
  calc
    m ≤ 2*n - 4 := by rel [h3]
    _ ≤ 2*5 - 4 := by rel [h2]
    _ = 6 := by linarith

-- -----------------------------
theorem theorem_2_1_3
  (r s :ℚ)
  (h1 : s + 3 ≥ r)
  (h2 : s + r ≤ 3)
  : r ≤ 3 := by
  have h3 : r ≤ s + 3 := by nlinarith [h1]
  have h4 : r ≤ 3 - s := by linarith [h2]
  have h5 : r + r ≤ s + 3 + 3 - s := by linarith [h3, h4]
  have h6 : 2 * r ≤ 6 := by nlinarith [h5]
  calc
    r ≤ 3 := by linarith [h6]

-- -----------------------------
theorem theorem_2_1_4
  (t : ℝ)
  (h1 : t^2 = 3*t)
  (h2 : t ≥ 1)
  : t ≥ 2 := by
  have h3 : t = 3 := by nlinarith [h1, h2]
  calc
    t = 3 := by rw [h3]
    _ ≥ 2 := by nlinarith

-- -----------------------------
theorem theorem_2_1_5
  (a b : ℝ)
  (h1 : a^2 = b^2 + 1)
  (h2 : a ≥ 0)
  : a ≥ 1 := by
  have h3 : b^2 ≥ 0 := by nlinarith
  calc
    a = √ (a^2) := by simp [h2]
    _ = √ (b^2 + 1) := by rw [h1]
    _ ≥ 1 := by simp [h3]

-- -----------------------------
  theorem theorem_2_1_6
    (x y : ℤ)
    (h1 : x + 3 ≤ 2)
    (h2 : y + 2*x ≥ 3)
    : y > 3 := by
    have h3 : x ≤ -1 := by
      calc x = x + 3 - 3 := by ring
           _ ≤ 2 - 3 := by rel [h1]
           _ ≤ -1 := by nlinarith
    have h4 : y ≥ 3 - 2*x := by nlinarith [h2]
    calc
      y ≥ 3 - 2*x := by rel [h4]
      _ ≥ 3 - 2*(-1) := by rel [h3]
      _ = 5 := by linarith
      _ > 3 := by nlinarith

-- -----------------------------
  theorem theorem_2_1_7
  (a b : ℝ)
  (h1 : -b ≤ a)
  (h2 : a ≤ b)
  : a^2 ≤ b^2 := by
  calc
    a^2 = a * a := by ring
    _   ≤ b * b := by nlinarith [h2]
    _   = b^2 := by ring

theorem theorem_2_1_7_v2
  (a b : ℝ)
  (h1 : -b ≤ a)
  (h2 : a ≤ b)
  : a^2 ≤ b^2 := by
  have h3 : 0 ≤ b + a := by nlinarith [h1]
  have h4 : 0 ≤ b - a := by nlinarith [h2]
  have h5 : (b - a) * (b + a) = b^2 - a ^2 := by ring
  have h6 : b^2 - a^2 ≥ 0 := by nlinarith [h3, h4, h5]
  nlinarith [h6]

-- -----------------------------
theorem theorem_2_1_8
  (a b : ℝ)
  (h1 : a ≤ b)
  : a^3 ≤ b^3 := by
  have h2 : 0 ≤ b - a := by nlinarith [h1]
  have h3 : 0 ≤ (b-a)^2 := by nlinarith [h2]
  have h4 : 0 ≤ (b-a)^3 := by nlinarith [h2]
  have h5 : 0 ≤ (b-a)^3 + (b-a)*(b+a)^2 := by nlinarith [h3, h4]
  have h6 : 0 ≤ (b-a)^3 + 3*(b-a)*(b+a)^2 := by nlinarith [h5]
  have h7 : 0 ≤ ( (b-a)^3 + 3*(b-a)*(b+a)^2 ) / 4 := by nlinarith [65]
  calc
    a^3 ≤ a^3 + ( ( (b-a)^3 + 3*(b-a)*(b+a)^2 ) / 4 ) := by nlinarith [h7]
    _   = b^3 := by ring

-- -----------------------------
theorem theorem_2_1_9_1
  (x : ℚ)
  (h1 : x^2 = 4)
  (h2 : x ≥ 1 )
  : x = 2 := by
  nlinarith [h1, h2]

theorem theorem_2_1_9_1_v2
  (x : ℚ)
  (h1 : x^2 = 4)
  (h2 : x > 1 )
  : x = 2 := by
  have h3 : x^2 + 2*x = 4 + 2*x := by rw [h1]
  have h4 : x^2 + 2*x = x * (x + 2) := by ring
  have h5 : 4 + 2*x = 2 * (x + 2) := by ring
  have h6 : x * (x + 2) = 2 * (x + 2) := by linarith [h3, h4, h5]
  have h7 : x + 2 > 0 := by nlinarith [h2]
  calc
    x = x * (x + 2) / (x + 2) := by field_simp [h7]
    _ = 2 * (x + 2) / (x + 2) := by rw [h5]
    _ = 2 := by field_simp

-- -----------------------------
theorem theorem_2_1_9_2
  (n : ℤ)
  (h1 : n^2 + 4 = 4*n)
  : n = 2 := by
  have h2 : n^2 - (4*n) + 4 = 0 := by linarith [h1]
  have h3 : (n - 2)^2 = 0 := by linarith [h2]
  nlinarith [h3]

-- -----------------------------
  theorem theorem_2_1_9_3
  (x y : ℚ)
  (h1 : x*y = 1)
  (h2 : x ≥ 1)
  : y ≤ 1 := by
  nlinarith

-- -----------------------------
theorem theorem_2_1_9_3
  (x y : ℚ)
  (h1 : x*y = 1)
  (h2 : x ≥ 1)
  : y ≤ 1 := by
  have h3 : 0 < x * y := by nlinarith [h1]
  have h4 : 0 < x := by nlinarith [h3]
  calc
    y = (x*y) / x := by field_simp [h4]
    _ = 1 / x := by rw [h1]
    _ ≤ 1 := by exact (div_le_one₀ h4).mpr h2


theorem theorem_2_1_9_3_v2
  (x y : ℚ)
  (h1 : x*y = 1)
  (h2 : x ≥ 1)
  : y ≤ 1 := by
  have h3 : 0 < x * y := by nlinarith [h1]
  have h4 : 0 < x := by nlinarith [h3]
  calc
    y = (x*y) / x := by field_simp [h4]
    _ = 1 / x := by rw [h1]
    _ ≤ 1 := by exact (div_le_one₀ h4).2 h2

-- -----------------------------
theorem theorem_2_2
  (x : ℚ)
  (h : 3*x = 2)
  : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = x * (3 / 3) := by linarith
    _ = (3 * x) / 3 := by field_simp
    _ = 2 / 3 := by rw [h]
    _ < 1 := by nlinarith

-- -----------------------------
theorem theorem_2_2_2
  (y : ℝ)
  : y^2 + 1 ≠ 0 := by
  have h : y^2 ≥ 0 := by nlinarith
  apply ne_of_gt
  calc
    y^2 + 1 ≥ 0 + 1 := by rel [h]
    _       = 1 := by ring
    _       > 0 := by nlinarith

-- -----------------------------
theorem theorem_2_2_3
  (a b : ℝ)
  (h1 : a^2 + b^2 = 0)
  : a^2 = 0 := by
  have h2 : a^2 ≥ 0 := by nlinarith
  have h3 : b^2 ≥ 0 := by nlinarith
  have h4 : a^2 = - b^2 := by linarith [h1]
  have h5 : a^2 = b^2 := by linarith [h1]
  have h6 : a^2 = 0 := by linarith [h1, h5]
  apply h6

-- -----------------------------
theorem theorem_2_2_3_v2
  (a b : ℝ)
  (h1 : a^2 + b^2 = 0)
  : a^2 = 0 := by
  have h2 : a^2 ≥ 0 := by nlinarith
  have h3 : a^2 ≤ 0 := by
    calc
      a^2 ≤ a^2 + b^2 := by nlinarith
      _   = 0 := by rw [h1]
  apply le_antisymm h3 h2

-- -----------------------------
  theorem theorem_2_2_4
  (m : ℤ)
  (h1 : m + 1 = 5)
  : 3*m ≠ 6 := by
  calc
    3 * m = 3 * m + 3 -3 := by ring
    _     = 3* (m + 1) - 3:= by ring
    _     = 3 * 5 - 3 := by rw [h1]
    _     = 12 := by norm_num
    _     ≠ 6 := by nlinarith

-- -----------------------------
theorem theorem_2_2_4
  (m : ℤ)
  (h1 : m + 1 = 5)
  : 3*m ≠ 6 := by
  calc
    3 * m = 3 * m + 3 -3 := by ring
    _     = 3* (m + 1) - 3:= by ring
    _     = 3 * 5 - 3 := by rw [h1]
    _     = 12 := by norm_num
  apply ne_of_gt (by norm_num)

-- -----------------------------
  theorem theorem_2_2_4_2
  (s : ℚ)
  (h1 : 3*s ≤ -6)
  (h2 : 2*s ≥ -4)
  : s = -2 := by
  apply le_antisymm
  calc
    s = 3*s /3 := by linarith
    _ ≤ -6 / 3 := by nlinarith [h1]
    _ = -2 := by linarith
  calc
    s = 2*s / 2 := by linarith
    _ ≥ -4 /2 := by nlinarith [h2]
    _ = -2 := by linarith

-- -----------------------------
theorem theorem_2_3_1
  (x y : ℝ)
  (h1: x = 1 ∨ y = -1)
  : x*y + x = y + 1 := by
  obtain hx | hy := h1
  calc
    x*y + x = 1*y + 1 := by rw [hx]
    _       = y + 1:= by ring
  calc
    x*y + x = x*(-1) + x := by rw [hy]
    _       = x - x := by ring
    _       = 0 := by linarith
    _       = 1 + (-1) := by linarith
    _       = 1 + y := by rw [hy]
    _       = y + 1 := by ring

-- -----------------------------
theorem le_or_ge_succ
  (a b : ℕ)
  : a ≤ b ∨ b + 1 ≤ a := by
  apply le_or_gt

theorem theorem_2_3_2
  (n : ℕ)
  : n^2 ≠ 2 := by
  have h := le_or_ge_succ n 1
  obtain h1 | h2 := h

  -- case 1
  apply ne_of_lt
  calc
    n^2 ≤ 1^2 := by nlinarith
    _   = 1 := by linarith
    _   < 2 := by nlinarith

  -- case 2
  apply ne_of_gt
  calc
    n^2 ≥ 2^2 := by nlinarith
    _   = 4 := by linarith
    _   > 2 := by nlinarith

-- -----------------------------
theorem theorem_2_3_3
  (x : ℝ)
  (h1 : 2*x + 1 = 5)
  : x = 1 ∨ x = 2 := by
  have h2 : x = 2 := by linarith [h1]
  exact Or.intro_right _ h2

theorem theorem_2_3_3_v2
  (x : ℝ)
  (h1 : 2*x + 1 = 5)
  : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 -1) / 2 := by ring
    _ = (5 -1) /2 := by rw [h1]
    _ = 2 := by linarith

-- -----------------------------
theorem theorem_2_3_4
  (x : ℝ)
  (h1 : x^2 - 3*x + 2 = 0)
  : x = 1 ∨ x = 2 := by
  have h2 : x^2 - 3*x +2 = (x - 1) * (x - 2) := by linarith
  have h3 : (x - 1) * (x - 2) = 0 := by rw [← h1, h2]
  have h4 : (x-1 = 0) ∨ (x-2 =0) := by
    simp at h3
    exact h3
  obtain h_left | h_right := h4
  .
    left
    exact eq_of_sub_eq_zero h_left

  .
    right

-- -----------------------------
theorem theorem_2_3_5
  (n : ℤ)
  : n^2 ≠ 2 := by
  -- CASES n < 2 ∨ 2 ≤ n
  -- FIRST CASE 2 ≤ n
  by_cases h_ge2 : 2 ≤ n
  ·
    -- Here Lean knows h_ge2 : 2 ≤ n
    nlinarith
  -- SECOND CASE n < 2
  ·
    -- Here Lean knows h_ge2 : ¬ (2 ≤ n)
    nlinarith [sq_nonneg n]
    -- sorry

-- -----------------------------
theorem theorem_2_3_6_1
  (x : ℚ)
  (h : x=4 ∨ x=-4)
  : x^2 + 1 = 17 := by
  by_cases h1 : x=4
  case pos =>
    nlinarith
  case neg =>
    have g1 : x = -4 := Or.resolve_left h h1
    have g2 : x^2 = 16 := by
      rw [g1]
      norm_num
    nlinarith [g2]

theorem theorem_2_3_6_1_v2
  (x : ℚ)
  (h : x=4 ∨ x=-4)
  : x^2 + 1 = 17 := by
  by_cases h1 : x=4
  case pos =>
    nlinarith
  case neg =>
    have g1 : x = -4 := Or.resolve_left h h1
    have g2 : x^2 = 16 := by calc
      x^2 = (-4)^2 := by rw [g1]
      _   = 16 := by norm_num
    nlinarith [g2]

theorem theorem_2_3_6_1_v3
  (x : ℚ)
  (h : x=4 ∨ x=-4)
  : x^2 + 1 = 17 := by
  by_cases h1 : x=4
  case pos =>
    nlinarith
  case neg =>
    have g1 : x = -4 := Or.resolve_left h h1
    have g2 : x^2 = 16 := by calc
      x^2 = (-4)^2 := by rw [g1]
      _   = 16 := by norm_num
    exact

-- -----------------------------
example
  {x : ℝ}
  (h : x = 1 ∨ x = 2)
  : x ^ 2 - 3 * x + 2 = 0 := by
  by_cases g : x = 1
  case pos =>
    nlinarith
  case neg =>
    have i : x = 2 := Or.resolve_left h g
    nlinarith
