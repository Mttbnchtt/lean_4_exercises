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
