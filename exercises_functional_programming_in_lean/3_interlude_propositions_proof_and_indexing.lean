def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog : String := (woodlandCritters[0]?).getD "unknown"

#eval hedgehog  -- Outputs: "hedgehog"

theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  simp

  -- The proof is trivial, but we can use the tactic `decide` to automatically prove it.
  -- decide
  -- The `decide` tactic will automatically prove the goal if it can be decided by a simple computation.
  -- In this case, it can be decided because `1 + 1` is equal to `2`.

eval onePlusOneIsTwo  -- Outputs: true
