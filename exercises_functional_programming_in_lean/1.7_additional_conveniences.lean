def drop : Nat → List α → List α
| 0, xs => xs
| _, [] => []
| n+1, x :: xs => drop n xs
