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
