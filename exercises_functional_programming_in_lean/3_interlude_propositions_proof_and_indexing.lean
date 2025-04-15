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
  -- The constructor tactic is used to prove conjunctions (∧).
  -- In this case, it splits the goal into two subgoals: one for each part of the conjunction.
  -- The decide tactic is then used to prove each subgoal.
  -- The first subgoal is to prove that 1 + 1 = 2, and the second subgoal is to prove that "Str".append "ing" = "String".
  -- The decide tactic can handle both of these goals, as they are decidable propositions.

#check addAndAppend  -- Outputs: true

-- tactis style proof
theorem andImpliesOr : (A ∧ B) → (A ∨ B) := by
  intro h
  exact Or.inl h.left
  -- The intro tactic is used to introduce hypotheses into the context.
  -- In this case, it introduces the hypothesis h, which is of type A ∧ B.
  -- The goal is to prove that A ∨ B holds under this hypothesis.
  -- The exact tactic is used to provide a specific proof term that matches the goal.
  -- In this case, it provides the left part of the disjunction A ∨ B.
  -- The Or.inl constructor is used to construct the left part of the disjunction.
  -- The left part of the disjunction is A, which is obtained from the hypothesis h.

#check andImpliesOr  -- Outputs: true

-- term style proof
theorem andImplesOr_v2 : (A ∧ B) → (A ∨ B) :=
  fun h => Or.inl h.left
  -- This is a more concise version of the previous theorem.
  -- It uses a lambda function to directly construct the proof term for A ∨ B.
  -- The lambda function takes the hypothesis h and immediately returns Or.inl h.left.
  -- This is a common pattern in functional programming, where functions are often defined in a more concise manner.
  -- The lambda function is a first-class citizen in Lean, allowing for more flexible and concise proofs.

#check andImplesOr_v2  -- Outputs: true

-- patter-matching style proof
theorem andImplesOr_v3 : (A ∧ B) → (A ∨ B) :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a

  #check andImplesOr_v3  -- Outputs: true

  --
