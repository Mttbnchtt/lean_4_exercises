import Mathlib


example
  {n : ℕ}
  (hn : ∀ m, n ∣ m)
  : n = 1 := by
  have g0 : n ∣ 1 := by apply hn
  have g1 : 0 < 1 := by grind
  apply Nat.le_antisymm
  · apply Nat.le_of_dvd g1 g0
  · apply Nat.pos_of_dvd_of_pos g0 g1

theorem div_1
  {n : ℕ}
  (hn : ∀ m, n ∣ m)
  : n = 1 := by
  -- “If n divides everything, then n=1”
  -- ∀n (∀m (n ∣ m) → n =1)
  -- ∀n (¬ ∀m (n∣ m) ∨ n=1)
  -- ∀n (∃m (¬ (n∣ m)) ∨ n=1) [not prenex because Q_1 ... Q_k φ]
  -- ∀n∃m (¬ (n∣ m) ∨ n=1)  [prenex normal form]
  -- the opponent gives me an n
  -- I need either to find an m such that ¬ n∣ m or to show that n=1
  -- equivalently: I need to find an m such that either ¬ n∣ m or n=1
  have g0 : n ∣ 1 := by apply hn
  have g1 : 0 < 1 := by grind
  apply Nat.le_antisymm
  · apply Nat.le_of_dvd g1 g0 -- n ≤ 1
  · apply Nat.pos_of_dvd_of_pos g0 g1 -- 0 < n (Lean infers 1≤ n)

theorem div_2
  {n : ℕ}
  : ∃m, (¬ (n∣ m)) ∨ n=1 := by
  -- “For every n, either n=1, or there is some m that n does not divide”
  sorry


theorem div_iff
  {n : ℕ} :
  ((∀ m : ℕ, n ∣ m) → n = 1) ↔ ((∃ m : ℕ, (¬ (n ∣ m))) ∨ n = 1) := by
  constructor

  -- case 1: ((∀ m : ℕ, n ∣ m) → n = 1) → (∃ m : ℕ, (¬ (n ∣ m)) ∨ n = 1))
  -- assume: (∀ m : ℕ, n ∣ m) → n = 1)
  -- show: ∃ m : ℕ, (¬ (n ∣ m)) ∨ n = 1)
  -- proof:
  -- ¬ (∀ m : N, n ∣ m) ∨ n = 1 [by A→B ↔ ¬A∨B]
  -- (∃ m : ℕ, ¬ (n ∣ m)) ∨ n = 1 [by ¬∀ φ ↔ ∃ ¬ φ]
  case mp =>
    intro h     -- assume: (∀ m : ℕ, n ∣ m) → n = 1
    have h': (¬ (∀ m : ℕ, n ∣ m)) ∨ n = 1 := by
      exact imp_iff_not_or.mp h
    have h'': ((∃ m : ℕ, (¬ (n ∣ m))) ∨ n = 1) := by

      -- case split on a disjunction:
      -- if h' was proved by the left side of ∨, call that proof h_not_all
      -- if h' was proved by the right side of ∨, call that proof h1
      -- S, Lean creates two branches
      -- rcases h' with h_not_all ∣ h1 -- case split on a disjunction
      cases h' with
      | inl h_not_all =>
        left
        push Not at h_not_all
        exact h_not_all
      | inr h1 =>
        right
        exact h1
      exact h''

  -- case 2: (∃ m : ℕ, (¬ (n ∣ m)) ∨ n = 1)) → ((∀ m : ℕ, n ∣ m) → n = 1)
  -- assume: (∃ m : ℕ, (¬ (n ∣ m)) ∨ n = 1))
  -- show: ((∀ m : ℕ, n ∣ m) → n = 1)
  -- proof:
  -- (¬ ∃ m : ℕ, (¬ (n ∣ m)) → n = 1)) [by definition of →]
  -- (∀ m : ℕ, (n ∣ m) → n = 1)) [by definition of ¬∃¬]
  case mpr =>
    intro h   -- assume: (∃ m : ℕ, (¬ (n ∣ m))) ∨ n = 1
    have h': (¬(∃ m : ℕ, (¬ (n ∣ m)))) → n = 1 := by
      exact or_iff_not_imp_left.mp h
    have h'': (∀ m : ℕ, (n ∣ m)) → n = 1 := by
      push Not at h'
      exact h'
    exact h''


example
  {a b : ℝ}
  (h : ∀ x, x ≥ a ∨ x ≤ b)
  : a ≤ b := by
  by_cases h1 : (a+b)/2 ≥ a

  -- case 1: (a+b)/2 ≥ a
  -- by contradiction: suppose that a > b
  -- therefore, (a+b)/2 < 2a/a = a
  -- ⟂
  case pos =>
    by_contra
    have g1 : (a+b)/2 < a := by
      nlinarith
    grind

  -- case 2: (a+b)/2 < a
  -- therefore, by h, (a+b)/2 ≤ b
  -- by contradiction: suppose that a > b
  -- (a+b)/2 < 2b/2 = b < a
  -- ⟂
  case neg =>
    have g2 : (a+b) / 2 ≤ b := by
      grind
    by_contra
    have g3 : b < a:= by
      apply (Std.not_le).mp this
    have g4 : a < a := by
      grind
    grind


theorem maximal_element
  (a b : ℝ)
  (ha1 : a^2 ≤ 2)
  (ha2 : ∀x, x^2 ≤ 2 → x ≤ a)
  (hb1 : b^2 ≤ 2)
  (hb2 : ∀x, x^2 ≤ 2 → x ≤ b)
  : a = b := by
  -- since b^2 ≤ 2, then b ≤ a
  have g1: b ≤ a := by
    apply ha2
    apply hb1

  -- since a^2, then a ≤ b
  have g2 : a ≤ b := by
    apply hb2
    apply ha1

  -- therefore, a = b
  grind


example
  : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  have h1 : 0 ≤ (x-1)^2 := by nlinarith
  have h2 : -1 ≤ x^2 - 2*x := by grind
  exact h2


theorem circle_line_lower_bound
  : ∀ k : ℝ, ∃ c : ℝ, ∀ x y, ( (x^2 + y^2 ≤ k^2) → (x + y ≥ c) ) := by
  -- 1. Distinguish two cases: k ≠ 0 and k = 0.
  -- 2. CASE 1. Assume first that k ≠ 0.
  -- 3. x^2 + y^2 ≤ k^2 describes the closed disc centered at the origin with radius |k|.
  -- 4. For each real number c, the equation x + y = c describes a straight line of slope -1. These lines are all parallel.
  -- 5. We seek the greatest real number c such that every point (x, y) in the disc satisfies x + y ≥ c.
  -- 6. As the line x + y = c is moved toward the third quadrant, the last such line meeting the disc is tangent to the boundary circle x^2 + y^2 = k^2.
  -- 7. Let (A, B) be the point of tangency. Since the tangent line is perpendicular to the radius joining the origin to (A, B), and since the unique line through the origin perpendicular to x + y = c is y = x, the point (A, B) lies on y = x. Therefore A = B.
  -- 8. Because this is the minimizing tangency point, it lies in the third quadrant, so A = B < 0.
  -- 9. Since (A, B) lies on the circle, A^2 + B^2 = k^2. Using A = B, we obtain 2A^2 = k^2. So A = -|k| / √2.
  -- 10. Therefore
  --     c = A + B
  --       = -2|k| / √2
  --       = -√2 * |k|
  --       = -√(2 * k^2).
  -- 11. CASE 2. Assume k = 0. The disc consists only of the point (0, 0), and the greatest lower bound is c = 0, which agrees with the same formula.
  -- 12. CONCLUSION: the sharp bound is: x^2 + y^2 ≤ k^2  →  x + y ≥ -√(2 * k^2).
  intro k
  use -√(2*k^2)
  intro x y h
  have h1: 0 ≤ (x-y)^2 := by
    nlinarith
  have h2 : (x-y)^2 = 2*(x^2+y^2) - (x+y)^2 := by
    nlinarith
  have h3 : (x+y)^2 ≤ 2*(x^2 + y^2) := by
    nlinarith [h2]
  have h4 : (x+y)^2 ≤ 2*k^2 := by
    nlinarith [h3]
  have h5 : -√(2*k^2) ≤ x + y := by
    exact Real.neg_sqrt_le_of_sq_le h4
  exact h5


example
  {a b : ℝ}
  (ha1 : a ^ 2 ≤ 2)
  (hb1 : b ^ 2 ≤ 2)
  (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
  (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b)
  : a = b := by
  -- show: a ≤ b
  -- by hb2
  have g1 : a ≤ b := by
    specialize hb2 a
    apply hb2 ha1
    -- exact hb2 ha1 (possible alternative)

  -- show: b ≤ a
  -- by hb1
  have g2 : b ≤ a := by
    specialize ha2 b
    apply ha2 hb1

  -- therefore a = b
  nlinarith

example
  : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -2
  intro x
  nlinarith
