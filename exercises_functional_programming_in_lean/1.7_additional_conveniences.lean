def drop : Nat → List α → List α
  | 0, xs => xs
  | _, [] => []
  | n+1, x :: xs => drop n xs

#eval drop 2 [1, 2, 3, 4, 5]  -- [3, 4, 5]s

-- test
