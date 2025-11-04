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

-- -----------------------------
example
  {t : ℚ}
  (h : t = -2 ∨ t = 3)
  : t^2 - t - 6 = 0 := by
  by_cases g : t = -2
  case pos =>
    nlinarith
  case neg =>
    have i : t = 3 := Or.resolve_left h g
    nlinarith

-- -----------------------------
example
  {x y : ℝ}
  (h : x = 2 ∨ y = -2)
  : x*y + 2*x = 2*y + 4 := by
  by_cases h1 : x = 2
  case pos => -- x = 2
    rw [h1]
    ring
  case neg => -- ¬ x = 2
    have h2 : y = -2 := Or.resolve_left h h1 -- y = -2
    rw [h2]
    ring

example
  {x y : ℝ}
  (h : x = 2 ∨ y = -2)
  : x*y + 2*x = 2*y + 4 := by
  cases h with
  | inl hx =>
      -- case x = 2
      rw [hx]; ring
  | inr hy =>
      -- case y = -2
      rw [hy]; ring

example
  {x y : ℝ}
  (h : x = 2 ∨ y = -2)
  : x*y + 2*x = 2*y + 4 := by
  cases' h with hx hy
  -- x = 2
  rw [hx]
  ring
  -- y = -2
  rw [hy]
  ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) :
    x*y + 2*x = 2*y + 4 := by
  cases' h with hx hy
  · rw [hx]; ring
  · rw [hy]; ring

-- -----------------------------
example
  {s t : ℚ}
  (h : s = 3 - t)
  : s + t = 3 ∨ s + t = 5 := by
  have h1 : s + t = 3 := by
    calc
      s + t = 3 - t + t := by rw [h]
      _     = 3 := by ring
  exact Or.inl h1

-- -----------------------------
example
  {a b : ℚ}
  (h : a + 2 * b < 0)
  : b < a / 2 ∨ b < - a / 2 := by
  have h1 : b < - a / 2 := by
    nlinarith [h]
  exact Or.inr h1

-- -----------------------------
example
  {x y : ℝ}
  (h : y = 2 * x + 1)
  : x < y / 2 ∨ x > y / 2 := by
  -- y - 1 = 2*x
  -- (y-1) / 2 = x
  -- y/2 - 1/2 = x
  -- y/2 = x + (1/2)
  have h1 : y/2 > x := by
    calc
      y / 2 = (2*x + 1) / 2 := by rw [h]
      _     = x + 1/2 := by ring
      _     > x := by nlinarith
  have h2 : x < y/2 := by nlinarith [h1]
  exact Or.inl h2

-- -----------------------------
example
  {x : ℝ}
  (h : x ^ 2 + 2 * x - 3 = 0)
  : x = -3 ∨ x = 1 := by
  have h1 : (x+3) * (x-1) = 0 := by
    calc
      (x+3) * (x-1) = x^2 + 2*x - 3 := by ring
      _             = 0             := by rw [h]
  have h2 : x+3 = 0 ∨ x-1 = 0 := by apply mul_eq_zero.mp h1
  by_cases h3 : x+3 = 0
  case pos =>
    left
    linarith [h3]
  case neg =>
    right
    have h4: x-1 = 0 := Or.resolve_left h2 h3
    linarith [h4]


-- -----------------------------
example
  {a b : ℝ}
  (h : a ^ 2 + 2 * b ^ 2 = 3 * a * b)
  : a = b ∨ a = 2 * b := by
  have h1 : a^2 + 2*b^2 - 3*a*b = 0 := by
    calc
      a^2 + 2*b^2 - 3*a*b = 3*a*b - 3*a*b := by rw [h]
      _                   = 0 := by ring
  have h2 : a^2 + 2*b^2 - 3*a*b = (a-b) * (a-2*b) := by ring
  have h3 : (a-b) * (a-2*b) = 0 := by
    calc
      (a-b) * (a-2*b) = a^2 + 2*b^2 - 3*a*b := by rw [h2]
      _               = 0                   := by rw [h1]
  have h4 : a-b = 0 ∨ a-2*b = 0 := by apply mul_eq_zero.mp h3
  by_cases h5: a - b = 0
  case pos =>
    left
    linarith [h5]
  case neg =>
    right
    have h6 : a-2*b = 0:= Or.resolve_left h4 h5
    linarith [h6]

-- -----------------------------
example
  {t : ℝ}
  (h : t ^ 3 = t ^ 2)
  : t = 1 ∨ t = 0 := by
  have h1 : t^3 - t^2 = 0 := by
    calc
      t^3 - t^2 = t^2 - t^2 := by rw [h]
      _         = 0         := by ring
  have h2 : t^2 * (t - 1) = 0 := by
    calc
      t^2 * (t - 1) = t^3 - t^2 := by ring
      _             = 0         := by rw [h1]
  have h3 : t^2 = 0 ∨ t - 1 = 0 := by apply mul_eq_zero.mp h2
  have h4 : t = 0 ∨ t -1 =0 := by apply Or.imp_left sq_eq_zero_iff.mp h3
  cases h4 with
  | inl h4_l => right; exact h4_l
  | inr h4_r => left; linarith

-- -----------------------------
example
{n : ℕ}
: n ^ 2 ≠ 7 := by
-- CASE 1: n < 2 ∨ n ≥ 2
by_cases h : n < 2

-- CASE 1 left: n < 2. Therefore: n = 0 ∨ n = 1.
-- Reason by cases again.For n = 0, use calc. For n = 1, use calc.
case pos =>
  have hp_fact : n ≤ 1 := by apply Nat.lt_succ_iff.mp h
  have hp : n=0 ∨ n=1 := by apply Nat.le_one_iff_eq_zero_or_eq_one.mp hp_fact
  cases hp with
  | inl hp_0 =>
    calc
      n^2 = 0^2 := by rw [hp_0]
      _   = 0   := by norm_num
      _   ≠ 7   := by norm_num
  | inr hp_1 =>
    calc
      n^2 = 1^2 := by rw [hp_1]
      _   = 1   := by norm_num
      _   ≠ 7   := by norm_num

-- CASE 1 right: 2 ≤ n. Therefore: 2 = n ∨ 2 < n
-- For 2 = n, use calc.
-- For 2 < n, reason by cases again: 3 = n ∨ 3 < n. See below.
case neg =>
  have hn1 : 2 ≤ n := by apply not_lt.mp h
  have hn2 : 2 = n ∨ 2 < n := by apply eq_or_lt_of_le hn1
  cases hn2 with
  | inl hn_Eq =>
    -- simp [hn_Eq]
    -- norm_num
    calc
      n^2 = 2^2 := by rw [hn_Eq]
      _   = 4   := by norm_num
      _   ≠ 7   := by norm_num
  | inr hn_Lt =>
  -- From 2 < n, derive 3 ≤ n. Then use calc.
    have hn_Lt1 : 3 ≤ n := by apply Nat.succ_le_of_lt hn_Lt
    have hn_Lt2 : 9 ≤ n^2 := by
      calc
          9 = 3^2 := by norm_num
          _ ≤ n^2 := by rel [hn_Lt1]
    have hn_Lt3 : 7 < 9 := by decide
    have hn_Lt4 : 7 < n^2 := by apply lt_of_lt_of_le hn_Lt3 hn_Lt2
    have hn_Lt5 : n^2 ≠ 7 := by apply ne_of_gt hn_Lt4
    exact hn_Lt5

-- -----------------------------
-- NOT FINISHED
import Mathlib

example
  {x : ℤ}
  : 2 * x ≠ 3 := by

  by_cases h : x < 0

  -- x < 0
  case pos =>
    -- show that  2*x < 0
    have h1 : (0 :ℤ) < 2 := by norm_num
    have h2 : 2*x < 0 := by apply mul_neg_of_pos_of_neg h1 h
    -- show that 2*x < 3
    have h3 : 2*x < 3 := by
      calc
        2*x < 0 := by rel [h2]
        _   < 3 := by norm_num
    -- show that 2*x ≠ 3
    have h4 : 2*x ≠ 3 := by apply ne_of_lt h3
    exact h4

  -- ¬ (x < 0)
  case neg =>
    have g : 0 ≤ x := by apply not_lt.mp h
    have g1 : 0 = x ∨ 0 < x := by apply eq_or_lt_of_le g
    cases g1 with
    -- x = 0
    | inl g1_eq =>
      calc
        2*x = 2*0 := by rw [g1_eq]
        _   = 0 := by norm_num
        _   ≠ 3 := by norm_num
    -- x > 0
    | inr g1_gt =>
      by_cases g1_gt_cases : x < 3
      case pos =>
        have g1_gt_cases_p1 : x = 1 ∨ x = 2 := by sorry
      case neg =>
        have g1_gt_cases_n1 : 3 ≤ x :=by apply not_lt.mp g1_gt_cases
        have g1_gt_cases_n2 : 3 = x ∨ 3 < x :=by apply eq_or_lt_of_le g1_gt_cases_n1
        by_cases g1_gt_cases_n2_cases : x = 3
        case pos =>
          calc
            2*x = 2*3 := by rw[g1_gt_cases_n2_cases]
            _   = 6   := by linarith
            _   ≠ 3   := by linarith
        case neg =>
          have g1_gt_cases_n2_cases_n1 : ¬ (x ≤ 3) := by sorry
          have g1_gt_cases_n2_cases_n2 : 3 < x := by apply not_le.mp g1_gt_cases_n2_cases_n1
          have g1_gt_cases_n2_cases_n3 : 2*x > 6 := by
            calc
              2*x > 2*3 := by rel[g1_gt_cases_n2_cases_n2]
              _   = 6   := by linarith
          have g1_gt_cases_n2_cases_n4 : 2*x ≠ 3 := by sorry

-- 2*x is an even integer and 3 is an odd integer
-- and, therefore, 2*x \neq 3
example
  {x : ℤ}
  : 2 * x ≠ 3 := by
  by_contra g
  have h : Even (2 : ℤ ) := by norm_num
  have h0 : Even (2 : ℤ ) ∨ Even x := by
    left
    exact h
  have h1 : Even (2*x) := by apply Int.even_mul.mpr h0
  have h2: Odd (3) := by norm_num
  rewrite [g] at h1
  contradiction


-- solution suggested on Zulip by user
example
  {x : ℤ}
  : 2 * x ≠ 3 := by grind

-- solution suggested on Zulip by user
example {x : ℤ} : 2 * x ≠ 3 := by
  intro g
  replace g := congr_arg Even g
  norm_num at g

-- solution suggested on Zulip by user
example {x : ℤ} : 2 * x ≠ 3 := by
  apply ne_of_apply_ne Even
  norm_num

-- solution suggested on Zulip by user
example {x : ℤ} : 2 * x ≠ 3 := by
  by_contra g
  have h1 : Even (2 * x) := by
    rw [Int.even_mul]
    left
    norm_num
  have h2 : Odd 3 := by
    norm_num
  rw [g] at h1
  contradiction

-- solution suggested on Zulip by user
example {x : ℤ} : 2 * x ≠ 3 := by
  by_contra g
  have h1 : Even (2 * x) := by
    rw [Int.even_mul]
    left
    norm_num
  have h2 : Odd 3 := by
    norm_num
  rw [g, ← Int.not_odd_iff_even] at h1
  contradiction

-- solution suggested on Zulip by user
-- no mention of Odd
example {x : ℤ} : 2 * x ≠ 3 := by
  by_contra g
  have h1 : Even (2 * x) := by
    rw [Int.even_mul]
    left
    norm_num
  have h2 : ¬ Even 3 := by
    norm_num
  rw [g] at h1
  contradiction

-- -----------------------------
example
  {t : ℤ}
  : 5 * t ≠ 18 := by
  grind

example
  {t : ℤ}
  : 5 * t ≠ 18 := by
  by_cases h : t > 4

  -- Here Lean knows that t > 4
  case pos =>
    linarith

  -- Here Lean knows that ¬ (t > 4)
  case neg =>
    have g1 : t ≤ 4 := by apply Int.le_of_not_gt h
    have g2 : t < 4 ∨ t = 4 := by apply Int.le_iff_lt_or_eq.mp g1
    cases g2 with

    -- Here Lean know that t = 4
    | inr g2_right =>
        calc
          5 * t = 5 * 4 := by rw [g2_right]
          _     = 20    := by linarith
          _     ≠ 18    := by linarith

    -- Here Lean know that t < 4
    | inl g2_left =>
      have g3 : t ≤ 3 := by nlinarith
      have g4 : 5 * t < 18 := by
        calc
          5 * t ≤ 5 * 3 := by rel [g3]
          _     = 15    := by linarith
          _     < 18    := by nlinarith
      have g5 : 5 * t ≠ 18 := by linarith [g4]
      exact g5

-- -----------------------------
example
  {m : ℕ}
  : m ^ 2 + 4 * m ≠ 46 := by
  -- Assume, for contradiction, that m² + 4m = 46
  intro h

  -- Compute remainder of 46 modulo 4: 46 % 4 = 2
  have h1 : 46 % 4 = 2 := by norm_num

  -- Show that (m² + 4m) % 4 can only be 0 or 1
  have h2 : (m^2 + 4*m) % 4 = 0 ∨ (m^2 + 4*m) % 4 = 1 := by
    -- Split into two cases: m is even or odd
    by_cases g : Even m

    case pos =>
      -- Case 1: m is even
      left
      -- Extract k such that m = 2k
      rcases g with ⟨k, hk⟩
      -- Express m² + 4m in terms of k and factor
      have gp_1 : m^2 + 4*m = 4*(k^2 + 2*k) := by
        calc
          m^2 + 4*m = (k+k)^2 + 4*(k+k) := by rw [hk]
          _         = (2*k)^2 + 4*(2*k) := by ring
          _         = 4*k^2 + 4*(2*k)   := by ring
          _         = 4*(k^2 + 2*k)     := by ring
      -- Conclude divisibility by 4, so remainder is 0
      have gp_2 : (m^2 + 4*m) % 4 = 0 := by
        rw [gp_1]
        omega
      exact gp_2

    case neg =>
      -- Case 2: m is not even, hence odd
      right
      have gn_1 : Odd m := by apply Nat.not_even_iff_odd.mp g
      -- Extract k such that m = 2k + 1
      rcases gn_1 with ⟨k, hk⟩
      -- Express m² + 4m in terms of k
      have gn_2 : (m^2 + 4*m) = 4*(k^2 + 3*k + 1) + 1 := by
        calc
          m^2 + 4*m = (2*k+1)^2 + 4*(2*k+1)     := by rw [hk]
          _         = 4*k^2 + 4*k + 1 + 8*k + 4 := by ring
          _         = 4*k^2 + 12*k + 4 + 1      := by ring
          _         = 4*(k^2 + 3*k + 1) + 1     := by ring
      -- So remainder is 1
      have gn_3 : (m^2 + 4*m) % 4 = 1 := by
        rw [gn_2]
        omega
      exact gn_3

  -- Now substitute h (m² + 4m = 46) into h2
  rw [h] at h2

  -- Contradiction: left side remainder must be 2 (from h1), but h2 says 0 or 1
  contradiction

-- -----------------------------
-- PROOFS WITH AND
-- -----------------------------
example
  (x y : ℤ)
  (h : 2*x - y = 4 ∧ y - x + 1 = 2)
  : x = 5 := by
  linarith [h]

example
  (x y : ℤ)
  (h : 2*x - y = 4 ∧ y - x + 1 = 2)
  : x = 5 := by
  obtain ⟨ h1, h2 ⟩ := h
  calc
    x = 2*x - y - 1 + y - x + 1 := by ring
    _ = (2*x - y) - 1 + (y - x + 1) := by ring
    _ = (4) -1 + (y - x + 1) := by rw [h1]
    _ = (4) -1 + (2) := by rw [h2]
    _ = 5 := by linarith

-- -----------------------------
example
  (p :ℚ)
  (h : p^2 ≤ 8)
  : p ≥ -5 := by nlinarith

-- ----------------------------- d
example
  (p : ℚ)
  (h : p^2 ≤ 8)
  : p ≥ -5 := by
  have g : (0 : ℝ) ≤ √8 := by norm_num
  have g0 : (p^2 : ℝ) ≤ (√8 : ℝ )^2 := by
    calc
      (p^2 : ℝ) ≤ (8 : ℝ) := by exact_mod_cast h
      _   = (√8)^2 := by norm_num
  have g1 : -√8 ≤ p ∧  p ≤ √8 := by apply abs_le_of_sq_le_sq' g0 g
  have g2 : -√8 ≤ p := by apply g1.left
  have g3 : (0 : ℝ) ≤ 5 ∧ (8 : ℝ) ≤ 5^2 := by norm_num
  have g4 : √8 ≤ 5 := by apply Real.sqrt_le_iff.mpr g3
  have g5 : -5 ≤ -√8 := neg_le_neg_iff.mpr g4
  have g6 : (p : ℝ) ≥ -5 := by
    calc
      p ≥ -√8 := by rel [g2]
      _ ≥ -5 := by apply g5
  exact_mod_cast g6

example : √8 ≤ 5 := by
  have g : (0 : ℝ) ≤ 5 ∧ (8 : ℝ) ≤ 5^2 := by norm_num
  apply Real.sqrt_le_iff.mpr g


-- -----------------------------
example
  {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 ∧ b = 1 := by
  have g1 : b = 1 := by linarith [h2]
  have g2 : a = 9 := by
    calc
      a = a - 5*b + 5*b := by ring
      _ = 4 + 5*b       := by rw [h1]
      _ = 4 + 5*1       := by rw [g1]
      _ = 9             := by linarith
  exact ⟨g2, g1⟩

example
  {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 ∧ b = 1 := by
  have g1 : b = 1 := by linarith [h2]
  constructor
  · calc
      a = a - 5*b + 5*b := by ring
      _ = 4 + 5*b       := by rw [h1]
      _ = 4 + 5*1       := by rw [g1]
      _ = 9             := by linarith
  · apply g1

-- -----------------------------
example
  (a b : ℝ)
  (h : a^2 + b^2 = 0)
  : a=0 ∧ b=0 := by
  have g1 : a^2 = - b^2 := by nlinarith [h]
  have g2 : a^2 ≥ 0 := by nlinarith
  have g3 : -b^2 ≤ 0 := by nlinarith
  have g4 : a^2 = 0 := by nlinarith [g1, g2, g3]
  have g5 : a = 0 := by nlinarith [g4]
  have g6 : b = 0 := by nlinarith [g1, g4]
  constructor
  . apply g5
  . apply g6

example
  (a b : ℝ)
  (h : a^2 + b^2 = 0)
  : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by nlinarith
  have hb : b = 0 := by nlinarith
  exact ⟨ha, hb⟩

-- -----------------------------
example
 (a b : ℚ)
 (h : a ≤ 1 ∧ a + b ≤ 3)
 : 2*a + b ≤ 4 := by
 obtain ⟨ h1, h2 ⟩ := h
 calc
  2*a + b = a + a +b    := by ring
  _       ≤ 1 + a + b   := by rel[h1]
  _       = 1 + (a + b) := by ring
  _       ≤ 1 + 3       := by rel[h2]
  _       = 4           := by nlinarith

-- -----------------------------
example
  (r s : ℝ)
  (h : r + s ≤ 1 ∧ r - s ≤ 5)
  : 2*r ≤ 6 := by
  obtain ⟨ h1, h2 ⟩ := h
  calc
    2*r = r + s + r - s := by ring
    _   ≤ 1 + r - s     := by rel[h1]
    _   = 1 + (r - s)   := by ring
    _   ≤ 1 + 5         := by rel[h2]
    _   = 6             := by nlinarith

-- -----------------------------
example
  (m n : ℤ)
  (h : n ≤ 8 ∧ m + 5 ≤ n)
  : m ≤ 3 := by
  obtain ⟨ h1, h2 ⟩ := h
  calc
    m = m + 5 - 5 := by ring
    _ ≤ n - 5     := by rel[h2]
    _ ≤ 8 - 5     := by rel[h1]
    _ = 3         := by nlinarith

-- -----------------------------
example
  {p : ℤ}
  (h : p + 2 ≥ 9)
  : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have g1 : p^2 ≥ 49 := by nlinarith
  have g2 : 7 ≤ p := by nlinarith
  exact ⟨ g1, g2 ⟩

-- -----------------------------
  example
  {a : ℚ}
  (h : a - 1 ≥ 5)
  : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have g1 : a ≥ 6 := by nlinarith
  have g2 : 3*a ≥ 10 := by nlinarith
  exact ⟨ g1, g2 ⟩

-- -----------------------------
example
  {x y : ℚ}
  (h : x + y = 5 ∧ x + 2 * y = 7)
  : x = 3 ∧ y = 2 := by
  obtain ⟨g1, g2 ⟩ := h
  have g3 : x = 5 - y := by linarith [g1]
  have g4 : y = 2 := by linarith [g2, g3]
  have g5 : x = 3 := by linarith [g3, g4]
  exact ⟨ g5, g4 ⟩

-- -----------------------------
example
  {a b : ℝ}
  (h1 : a * b = a)
  (h2 : a * b = b)
  : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have eq_a_b : a = b := by
    calc
      a = a*b := by rw [h1]
      _ = b   := by rw [h2]
  by_cases g : a > 0
  case pos =>
    right
    have pos_0 : a = 1 := by nlinarith
    have pos_1 : b = 1:= by
      calc
        b = a := by rw [eq_a_b]
        _ = 1 := by rw [pos_0]
    have pos_2 : a = 1 ∧ b = 1 := by
      constructor
      . exact pos_0
      . exact pos_1
    exact pos_2
  case neg =>
    left
    have neg_0 : a ≤ 0 := by nlinarith [g]
    have neg_1 : a = 0 := by nlinarith
    have neg_2 : b = 0 := by
      calc
        b = a := by rw [eq_a_b]
        _ = 0 := by rw [neg_1]
    have neg_3 : a = 0 ∧ b = 0 := by
      constructor
      . exact neg_1
      . exact neg_2
    exact neg_3


-- -----------------------------
-- PROOFS WITH EXISTS
-- -----------------------------
example
  {a : ℚ}
  (h : ∃ b : ℚ, a = b ^ 2 + 1)
  : a > 0 := by
  obtain ⟨b, hb⟩ := h
  have g1 : b^2 ≥ 0 := by nlinarith
  have g2 : a > 0 := by
    calc
      a = b^2 + 1 := by rw [hb]
      _ > 0       := by nlinarith [g1]
  exact g2

-- -----------------------------
example
  (t : ℝ)
  (h : ∃ a : ℝ, a*t < 0)
  : t ≠ 0 := by
  by_contra g
  obtain ⟨ a, ha ⟩ := h
  have g_contra_1 : a*t = 0 := by
    calc
      a*t = a*0 := by rw [g]
      _   = 0   := by linarith
  have g_contra_2 : ¬ (a*t < 0) := by nlinarith [g_contra_1]
  contradiction

example
  (t : ℝ)
  (h : ∃ a : ℝ, a*t < 0)
  : t ≠ 0 := by
  by_contra g
  obtain ⟨ a, ha ⟩ := h
  have g_contra_1 : a*t = 0 := by
    rw [g]
    linarith
  have g_contra_2 : ¬ (a*t < 0) := by nlinarith [g_contra_1]
  contradiction

-- -----------------------------
example
  : ∃ n : ℤ, (12*n = 84) := by
  use 7
  linarith

-- -----------------------------
example
  (x : ℝ)
  : ∃ y : ℝ, (y > x) := by
  use x + 1
  nlinarith

-- -----------------------------
example
  : ∃ m n : ℤ, m^2 - n^2 = 12 := by
  use 4
  use 2
  nlinarith

-- -----------------------------
example
  : ∃ m n : ℤ, m^2 - n^2 = 11 := by
  use 6
  use 5
  nlinarith

-- -----------------------------
example 
  (a : ℤ)
  : ∃ m n : ℤ, m^2 - n^2 = 2*a + 1 := by
  use a + 1
  use a
  nlinarith
  
-- -----------------------------

  example
  (p q : ℝ)
  (h : p < q)
  : ∃ x : ℝ, (p < x) ∧  (x < q) := by
  use (p+q)/2
  constructor
  . nlinarith
  . nlinarith