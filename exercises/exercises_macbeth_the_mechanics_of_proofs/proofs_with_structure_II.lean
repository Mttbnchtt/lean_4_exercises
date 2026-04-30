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
