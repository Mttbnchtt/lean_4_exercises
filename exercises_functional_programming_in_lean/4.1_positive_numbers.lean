structure PositiveNumbers where
  successor ::           -- the named constructor
  predecessor : Nat      -- stores n  so that the actual value is n+1

def PositiveNumbers.add (x y : PositiveNumbers) : PositiveNumbers :=
  successor (x.predecessor + y.predecessor + 1)

#eval PositiveNumbers.add (PositiveNumbers.successor 1) (PositiveNumbers.successor 2)
