example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  linarith

example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  simp

example
  (n : ℕ)
  (h : Odd n)
  : Odd (3*n + 2) := by
  dsimp [Odd]
  rcases h with ⟨ k', hk'⟩
  use ( 3*k' + 2 )
  linarith


example
  (n : ℤ)
  (h : Odd n)
  : Odd (3*n + 2) := by
  dsimp [Odd]
  rcases h with ⟨ k', hk'⟩
  use ( 3*k' + 2 )
  linarith


example
  (n : ℤ)
  (hn : Odd n)
  : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example
  {n : ℤ}
  (hn : Odd n)
  : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  rcases hn with ⟨ k, hk ⟩
  use (7*k + 1)
  calc
    7*n - 4 = 7*(2*k + 1) - 4  := by rw [hk]
    _       = 14*k + 3        := by linarith
    _       = 2*(7*k + 1) + 1 := by linarith

example
  {n : ℤ}
  (hn : Odd n)
  : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  rcases hn with ⟨ k, hk ⟩
  use (7*k + 1)
  linarith
