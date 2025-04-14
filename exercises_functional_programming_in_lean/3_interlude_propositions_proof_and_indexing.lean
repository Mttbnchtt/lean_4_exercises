def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog : String := (woodlandCritters[0]?).getD "unknown"

#eval hedgehog  -- Outputs: "hedgehog"

theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide

-- simp: This tactic simplifies expressions by applying a collection of rewrite rules known as simp lemmas. It’s particularly effective for simplifying algebraic expressions, unfolding definitions, and applying known equalities. ￼
-- decide: This tactic attempts to automatically prove goals that are decidable propositions. It’s especially useful for goals that can be resolved through computation, such as basic arithmetic equalities or inequalities.

#check onePlusOneIsTwo  -- Outputs: true
