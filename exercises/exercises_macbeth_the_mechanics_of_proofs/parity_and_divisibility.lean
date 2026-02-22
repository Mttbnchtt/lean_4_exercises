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

example
  : Odd (-9 : ℤ) := by
  dsimp [Odd] at *
  use -5
  nlinarith

example
  : Even (26 : ℤ) := by
  dsimp [Even] at *
  use 13
  nlinarith

example
  {m n : ℤ}
  (hm : Odd m)
  (hn : Even n)
  : Odd (n + m) := by
  dsimp [Odd] at *
  dsimp [Even] at *
  rcases hm with ⟨ k, hk ⟩
  rcases hn with ⟨ k', hk' ⟩
  use k + k'
  nlinarith

example
  {p q : ℤ}
  (hp : Odd p)
  (hq : Even q)
  : Odd (p - q - 4) := by
  dsimp [Odd] at *
  dsimp [Even] at *
  rcases hp with ⟨ k, hk ⟩
  rcases hq with ⟨ k', hk' ⟩
  use k - k' -2
  nlinarith

example
  {a b : ℤ}
  (ha : Even a)
  (hb : Odd b)
  : Even (3 * a + b - 3) := by
  dsimp [Even, Odd] at *
  rcases ha with ⟨ k, hk ⟩
  rcases hb with ⟨ k', hk' ⟩
  use 3*k + k' -1
  nlinarith

example
  {r s : ℤ}
  (hr : Odd r)
  (hs : Odd s)
  : Even (3 * r - 5 * s) := by
  dsimp [Even, Odd] at *
  rcases hr with ⟨ k, hk ⟩
  rcases hs with ⟨ k', hk' ⟩
  use 3*k - 5*k' -1
  nlinarith

example
  {x : ℤ}
  (hx : Odd x)
  : Odd (x ^ 3) := by
  dsimp [Odd] at *
  rcases hx with ⟨ k, hk ⟩
  rw [hk]
  use 4*k^3 + 6*k^2 + 3*k
  nlinarith
  -- grind

example
  {n : ℤ}
  (hn : Odd n)
  : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Even, Odd] at *
  rcases hn with ⟨ k, hk ⟩
  use 2*k^2 - k
  nlinarith

example
  {a : ℤ}
  (ha : Odd a)
  : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  rcases ha with ⟨ z, hz ⟩
  -- (2z+1)^2 + 2(2z+1) -4 =
  -- 4z +4z + 1 + 4k + 2 -4
  use 2*z^2 + 4*z -1
  nlinarith


example
  {p : ℤ}
  (hp : Odd p)
  : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  rcases hp with ⟨ z, hz ⟩
  -- (2z + 1)^2 + 3(2z+1) - 5 =
  -- 4z^2 +4z +1 + 6z +3 -5 =
  -- 4z^2 + 10z -1
  -- 2(2z^2 + 5z -1) + 1
  use 2*z^2 + 5*z - 1
  grind

example
  {x y : ℤ}
  (hx : Odd x)
  (hy : Odd y)
  : Odd (x * y) := by
  dsimp [Odd] at *
  rcases hx with ⟨ z, hz ⟩
  rcases hy with ⟨ w, hw ⟩
  -- (2z+1)(2w+1) =
  -- 4zw +2z +2w +1
  use 2*z*w + z + w
  grind

example
  (n : ℤ)
  : Odd (3 * n ^ 2 + 3 * n - 1) := by
  dsimp [Odd] at *
  rcases Int.even_or_odd n with hk | hk
  -- CASE 1: n is even
  ·
    rcases hk with ⟨ z, hz ⟩
    use 6*z^2 + 3*z - 1
    grind
  -- CASE 2: n is odd
  ·
    rcases hk with ⟨ z, hz ⟩
    use 6*z^2 + 9*z + 2
    grind

example
  (n : ℤ)
  : ∃ m ≥ n, Odd m := by
  rcases Int.even_or_odd n with hk | hk
  · rcases hk with ⟨ z, hz ⟩
    use n + 1
    grind
  · rcases hk with ⟨ z, hz ⟩
    use n
    grind


example
  (a b c : ℤ)
  : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  -- Suppose Even(a):
  --  if Even(b), then Even(a-b);
  --  otherwise: if Even(c), then Even(a+c);
  --    otherwise Even (b-c)
  -- Otherwise:
  --  if Odd(b), then Even(a-b);
  --  otherwise: if Odd(c), then Even(a+c)
  --    otherwise: Even(b-c)
  rcases Int.even_or_odd a with ha | ha
  · rcases Int.even_or_odd b with hb | hb
    · grind
    · grind
  · grind

example
  (a b c : ℤ)
  : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  -- INFORMAL PROOF:
  -- Suppose Even(a):
  --  if Even(b), then Even(a-b);
  --  otherwise: if Even(c), then Even(a+c);
  --    otherwise Even (b-c)
  -- Otherwise:
  --  if Odd(b), then Even(a-b);
  --  otherwise: if Odd(c), then Even(a+c)
  --    otherwise: Even(b-c)

  rcases Int.even_or_odd a with ha | ha
    -- case 1: ha: Even(a)
  · rcases Int.even_or_odd b with hb | hb
      -- case 1.1: hb: Even(b)
    · exact Or.inl (ha.sub hb)
      -- case 1.2: hb: Odd(b)
    · rcases Int.even_or_odd c with hc | hc
        -- case 1.2.1: hc: Even(c)
      · exact Or.inr (Or.inl (ha.add hc))
        -- case 1.2.2: hc: Odd(c)
      · exact Or.inr (Or.inr (hb.sub_odd hc))
    -- case 2: ha: Odd(a)
  · rcases Int.even_or_odd b with hb | hb
      -- case 2.1: hb: Even(b)
    · rcases Int.even_or_odd c with hc | hc
        -- case 2.1.1: hc: Even(c)
      · exact Or.inr (Or.inr (hb.sub hc))
        -- case 2.1.2: hc: Odd(c)
      · exact Or.inr (Or.inl (ha.add_odd hc))
      -- case 2.2: hb: Odd(b)
    · exact Or.inl (ha.sub_odd hb)


example
  : (11 : ℕ) ∣ 88 := by
  dsimp[(·  ∣ · )]
  use 8

example
  : (11 : ℕ) ∣ 88 := by
  use 8

example
  : (-2 : ℤ) ∣ 6 := by
  use -3
  nlinarith


example
  {a b : ℤ}
  (hab : a ∣ b)
  : a ∣ b ^ 2 + 2 * b := by
  rcases hab with ⟨k, hk⟩
  use a*k^2 + 2*k
  calc
    b^2 +2*b = (a*k)^2 + 2*(a*k) := by rw [hk]
    _        = a*(a*k^2 + 2*k) := by nlinarith


example
  {a b : ℤ}
  (hab : a ∣ b)
  : a ∣ b ^ 2 + 2 * b := by
  dsimp [(· ∣ · )]
  rcases hab with ⟨k, hk⟩
  use a*k^2 + 2*k
  grind

example
  {a b c : ℕ}
  (hab : a ∣ b)
  (hbc : b ^ 2 ∣ c)
  : a ^ 2 ∣ c := by
  dsimp [· ∣ · ] at *
  rcases hab with ⟨ k, hk ⟩
  rcases hbc with ⟨ k', hk' ⟩
  use k^2*k'
  grind

example
  {x y z : ℕ}
  (h : x * y ∣ z)
  : x ∣ z := by
  dsimp [· ∣ ·] at *
  rcases h with ⟨ k, hk ⟩
  use y*k
  nlinarith

example
  : ¬(5 : ℤ) ∣ 12 := by
  grind


  : ¬(5 : ℤ) ∣ 12 := by
  -- h : ¬5 ∣ 12 ↔ ∃ k, 5*k < 12 ∧ 12 < 5*(k+1)
  have h :=
    Int.not_dvd_iff_lt_mul_succ
      (n := (5 : ℤ))
      (m := (12 : ℤ))
      (by norm_num)
  apply h.mpr
  use 2
  constructor
  · nlinarith
  · nlinarith


example
  {a b : ℕ}
  (hb : 0 < b)
  (hab : a ∣ b)
  : a ≤ b := by
  dsimp [· ∣ ·] at *
  rcases hab with ⟨ k, hk ⟩
  rw [hk]
  have h : 0 < (k : ℕ) := by grind
  nlinarith

example
  {a b : ℕ}
  (hb : 0 < b)
  (hab : a ∣ b)
  : a ≤ b := by
  rcases hab with ⟨ k, hk ⟩
  have h : 0 < (k : ℕ) := by grind
  nlinarith

example
  (t : ℤ)
  : t ∣ 0 := by
  dsimp [· ∣ · ] at *
  use 0
  nlinarith

example
  : ¬(3 : ℤ) ∣ -10 := by
  grind

example
  : ¬(3 : ℤ) ∣ -10 := by
  -- h : ¬(3 ∣ 12) ↔ ∃ k, 3*k < -10 ∧ -10 < 3*(k+1)
  have h :=
    Int.not_dvd_iff_lt_mul_succ
      (n := (3 : ℤ))
      (m := (-10 : ℤ))
      (by norm_num)
  apply h.mpr
  use -4
  constructor
  · nlinarith
  · nlinarith

example
  {x y : ℤ}
  (h : x ∣ y)
  : x ∣ 3 * y - 4 * y ^ 2 := by
  rcases h with ⟨ k, hk ⟩
  use 3*k - 4*x*k^2
  grind


example
  {a b : ℤ}
  (hab : a ∣ b)
  : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rcases hab with ⟨ k, hk ⟩
  -- b(2b^2 - b + 3)
  use k*(2*b^2 - b + 3)
  ring_nf


example
  {a b : ℤ}
  (hab : a ∣ b)
  : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  have hbc : a ∣ b * (2*b^2 - b + 3) := dvd_mul_of_dvd_left hab (2*b^2 - b + 3)
  have p :  b * (2*b^2 - b + 3) = 2 * b ^ 3 - b ^ 2 + 3 * b:= by ring_nf
  rewrite [<- p]
  exact hbc


example
  {k l m : ℤ}
  (h1 : k ∣ l)
  (h2 : l ^ 3 ∣ m)
  : k ^ 3 ∣ m := by
  rcases h1 with ⟨ p, hp ⟩
  rcases h2 with ⟨ q, hq ⟩
  use q * p^3
  grind


example
  {p q r : ℤ}
  (hpq : p ^ 3 ∣ q)
  (hqr : q ^ 2 ∣ r)
  : p ^ 6 ∣ r := by
  rcases hpq with ⟨ x, hx ⟩
  rcases hqr with ⟨ y, hy ⟩
  use x^2*y
  grind

example
  : ∃ n : ℕ, 0 < n ∧ 9 ∣ (2 ^ n) - 1 := by
  use 6
  grind


example
  : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  grind


example
  : 11 ≡ 3 [ZMOD 4] := by
  -- show that 4 ∣ (11 - 3)
  -- i.e. find an integer k such that 4k = 8
  use 2
  grind


example
  : -5 ≡ 1 [ZMOD 3] := by
  -- find an integer k such that 3k = -6
  use -2
  grind
