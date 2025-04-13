def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog : String := (woodlandCritters[0]?).getD "unknown"

#eval hedgehog  -- Outputs: "hedgehog"
