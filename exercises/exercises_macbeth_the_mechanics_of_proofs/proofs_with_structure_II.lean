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


example
  : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have g1 : (x+y)^2 ≤ 3^2 := by
    calc
      (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by nlinarith
      _       = 2*(x^2 + y^2)     := by linarith
      _       ≤ 2*4               := by rel [h]
      _       ≤ 3^2               := by linarith
  have g2 : (0 : ℝ) ≤ 3 := by
    nlinarith
  have g3 : -3 ≤ (x+y) ∧ (x+y) ≤ 3 := by
    apply abs_le_of_sq_le_sq' g1 g2
  obtain ⟨conj1, conj2⟩ := g3
  exact conj1

example
  {p : ℚ}
  (hp : p ^ 2 ≤ 8)
  : p ≥ -5 := by
  nlinarith

example
  {p : ℚ}
  (hp : p ^ 2 ≤ 8)
  : p ≥ -5 := by
  have g1 : (0 : ℚ) ≤ 3^2 := by
    nlinarith
  have g2 : p^2 ≤ 3^2 := by
    nlinarith
  have g3 : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq' g2 g1
  calc
    p ≥ -3 := by nlinarith [g3]
    _ ≥ -5 := by nlinarith


example
  {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 ∧ b = 1 := by
  have g1 : b = 1 := by
    linarith [h2]
  constructor
  case right =>
    exact g1
  case left =>
    calc
      a = a - 5*b + 5*b := by ring
      _ = 4 + 5*b       := by rw [h1]
      _ = 4 + 5*1       := by rw [g1]
      _ = 9             := by ring


example
  {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 ∧ b = 1 := by
  have g1 : b = 1 := by
    calc
      b = b + 2 - 2 := by ring
      _ = 3 - 2     := by rw [h2]
      _ = 1         := by ring
  constructor
  case right =>
    exact g1
  case left =>
    calc
      a = a - 5*b + 5*b := by ring
      _ = 4 + 5*b       := by rw [h1]
      _ = 4 + 5*1       := by rw [g1]
      _ = 9             := by ring


example
  {a b : ℝ}
  (h1 : a ^ 2 + b ^ 2 = 0)
  : a = 0 ∧ b = 0 := by
  constructor
  case left =>
    nlinarith
  case right =>
    nlinarith


example
  {a b : ℚ}
  (H : a ≤ 1 ∧ a + b ≤ 3)
  : 2 * a + b ≤ 4 := by
  rcases H with ⟨ha, hb⟩
  calc
    2*a + b ≤ a + a + b    := by nlinarith
    _       = a + (a + b)  := by ring
    _       ≤ 1 + (a + b)  := by rel [ha]
    _       ≤ 1 + 3        := by rel [hb]
    _       = 4            := by ring


example
  {r s : ℝ}
  (H : r + s ≤ 1 ∧ r - s ≤ 5)
  : 2 * r ≤ 6 := by
  rcases H with ⟨h1, h2⟩
  calc
    2*r = r + r         := by ring
    _   = r + r + s -s  := by ring
    _   = (r+s) + (r-s) := by ring
    _   ≤ 1 + 5         := by rel [h1, h2]
    _   = 6             := by ring



example
  {m n : ℤ}
  (H : n ≤ 8 ∧ m + 5 ≤ n)
  : m ≤ 3 := by
  rcases H with ⟨h1, h2⟩
  calc
    m = m+ 5 -5 := by ring
    _ ≤ n - 5 := by rel [h2]
    _ ≤ 8-5 := by rel [h1]
    _ = 3 := by ring


example
  {p : ℤ}
  (hp : p + 2 ≥ 9)
  : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have g1 : p ≥ 7 := by nlinarith [hp]
  constructor
  case left =>
    calc
      p^2 = p*p := by ring
      _   ≥ 7*7 := by rel [g1]
      _   = 49  := by ring
  case right =>
    exact g1


  example
    {a : ℚ}
    (h : a - 1 ≥ 5)
    : a ≥ 6 ∧ 3 * a ≥ 10 := by
    have g1 : a ≥ 6 := by nlinarith [h]
    constructor
    case left =>
      exact g1
    case right =>
      nlinarith [g1]


example
  {a b : ℝ}
  (h1 : a * b = a)
  (h2 : a * b = b)
  : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  grind

example
  {a b : ℝ}
  (h1 : a * b = a)
  (h2 : a * b = b)
  : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  -- a*b - a = a*(b-1) = 0 [from h1]
  -- a*b -b = b*(a-1) = 0 [from h2]
  -- therefore either a=0 or b=1
  -- therefore either b=0 or a=1
  -- therefore (a=0 ∨ b=1)∧ (b=0 ∨ a=1)
  -- therefore ((a=0 ∨ b=1)∧ b=0) ∨  ((a=0∨ b=1)∧ a=1)
  -- therefore (a=0∧ b=1) ∨ (b=1∧ b=0) ∨ (a=0∧ a=1) ∨ (b=1∧ a=1)
  -- therefore (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1)
  have g1 : a*(b-1) = 0 := by
    grind -- from h1
  have g2 : a = 0 ∨ b = 1 := by
    grind -- from g1
  have g3 : b*(a-1) = 0 := by
    grind -- from h2
  have g4 : b = 0 ∨ a = 1 := by
    grind -- from g3
  have g5 : (a = 0 ∨ b = 1) ∧ (b = 0 ∨ a = 1) := by
    exact ⟨g2, g4⟩
    -- alternatives (each is enough to prove g5):
    -- aesop
    -- grind
    -- tauto
    -- itauto
  -- have g6 : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  --   aesop
  -- grind
  have g6 : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
    -- g2 : a = 0 ∨ b = 1
    -- g4 : b = 0 ∨ a = 1
    -- Split both disjunctions into four cases.
    cases g2 with
    -- Case: a = 0
    | inl ha0 =>
        cases g4 with
        -- Subcase: b = 0
        | inl hb0 =>
            apply Or.inl
            exact ⟨ha0, hb0⟩
        -- Subcase: a = 1, contradicting a = 0
        | inr ha1 =>
            rw [ha0] at ha1
            norm_num at ha1
    -- Case: b = 1
    | inr hb1 =>
        cases g4 with
        -- Subcase: b = 0, contradicting b = 1
        | inl hb0 =>
            rw [hb1] at hb0
            norm_num at hb0
        -- Subcase: a = 1
        | inr ha1 =>
            apply Or.inr
            exact ⟨ha1, hb1⟩
  exact g6


example
  {a b : ℝ}
  (h1 : a * b = a)
  (h2 : a * b = b)
  : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by

  -- From h1, obtain: a * (b - 1) = 0.
  -- Therefore either a = 0 or b - 1 = 0.
  cases mul_eq_zero.mp (show a * (b - 1) = 0 by nlinarith [h1]) with

  -- Case: a = 0
  | inl ha0 =>
      apply Or.inl

      -- From h2 and a = 0, obtain b = 0.
      exact ⟨ha0, by simpa [ha0] using h2.symm⟩

  -- Case: b - 1 = 0
  | inr hb1 =>
      apply Or.inr

      -- From b - 1 = 0, obtain b = 1.
      -- Substituting b = 1 into h2 gives a = 1.
      exact ⟨
        by simpa [sub_eq_zero.mp hb1] using h2,
        sub_eq_zero.mp hb1
      ⟩

  -- strategy by contradiction
  -- suppose ¬ ((a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1))
  -- therefore ¬ ((a = 0 ∧ b = 0)) and ¬ (a = 1 ∧ b = 1)
  -- therefore (a≠ 0 ∨ b≠ 0) and (a≠ 1 ∨ b≠ 1).
  -- therefore we have four alternative cases:
  -- 1. a≠0 and a≠ 1
  -- 2. a≠ 0 and b≠ 1
  -- 3. b≠ 0 and a≠ 1
  -- 4. b≠ 0 and b≠ 1.


example
  {a : ℝ}
  (h : ∀ x, a ≤ x ^ 2 - 2 * x)
  : a ≤ -1 := by
  specialize h 1
  nlinarith
