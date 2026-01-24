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

example
  {x y : ℤ}
  (hx : Odd x)
  (hy : Odd y)
  : Odd (x + y + 1) := by
  dsimp [Odd] at *
  rcases hx with ⟨ x', hxk ⟩
  rcases hy with ⟨ y', hyk ⟩
  use x' + y' + 1
  nlinarith

example
  {x y : ℤ}
  (hx : Odd x)
  (hy : Odd y)
  : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  rcases hx with ⟨ x', hx' ⟩
  rcases hy with ⟨ y', hy' ⟩
  use (2*x'*y' + x' + y' + 2*y' + 1)
  grind


example
  {m : ℤ}
  (hm : Odd m)
  : Even (3*m - 5) := by
  dsimp [Odd] at hm
  dsimp [Even]
  rcases hm with ⟨ k, hk ⟩
  use (3*k -1)
  nlinarith

example
  {n : ℤ}
  (hn : Even n)
  : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at hn
  dsimp [Odd] at *
  rcases hn with ⟨ k, hk ⟩
  rw [hk]
  use 2*k^2 + 2*k - 3
  nlinarith

example
  (n : ℤ)
  : Even (n ^ 2 + n + 4) := by
  -- CASES: Even(n) ∨ Odd(n)
  rcases Int.even_or_odd n with ⟨ k, hk ⟩ | ⟨ k, hk ⟩
  -- CASE 1: Even(n)
  -- suppose that n = 2k
  -- (2k)^2 + 2k + 4 = 4k^2 + 2k + 4
  -- = 4k^2 + 2k + 4 = 2 (2k^2 + k + 2)
  · dsimp [Even] at *
    rw[hk]
    use (2*k^2 + k + 2)
    grind

  -- CASE 2: ¬Even(n), i.e. Odd(n)
  -- suppose that n = 2k + 1
  -- (2k+1)^2 + 2k + 1 + 4 =
  -- = 4k^2 + 4k + 1 + 2k + 1 + 4 =
  -- = 4k^2 +6k + 6 = 2(2k^2 + 3k + 3)
  · dsimp [Even] at *
    rw[hk]
    use (2*k^2 + 3*k + 3)
    grind
