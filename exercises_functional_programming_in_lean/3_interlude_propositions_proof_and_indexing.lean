def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog : String := (woodlandCritters[0]?).getD "unknown"

#eval hedgehog  -- Outputs: "hedgehog"

theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide

-- simp: This tactic simplifies expressions by applying a collection of rewrite rules known as simp lemmas. It’s particularly effective for simplifying algebraic expressions, unfolding definitions, and applying known equalities. ￼
-- decide: This tactic attempts to automatically prove goals that are decidable propositions. It’s especially useful for goals that can be resolved through computation, such as basic arithmetic equalities or inequalities.

#check onePlusOneIsTwo  -- Outputs: true

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  constructor
  decide
  decide
  -- The constructor tactic is used to prove conjunctions (∧) and disjunctions (∨).
  -- In this case, it splits the goal into two subgoals: one for each part of the conjunction.
  -- The decide tactic is then used to prove each subgoal.
  -- The first subgoal is to prove that 1 + 1 = 2, and the second subgoal is to prove that "Str".append "ing" = "String".
  -- The decide tactic can handle both of these goals, as they are decidable propositions.

#check addAndAppend  -- Outputs: true
