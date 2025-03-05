#check 1.2
#check (1.2)
#check 0.0
#check 0
#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

#check Point
#check Point.mk
#check Point.mk 1.0 2.0
#eval Point.mk 1.0 2.0
def p := Point.mk 1.0 2.0
#check p
#check p.x
#check p.y
#check p.x + p.y  -- Lean infers that p.x and p.y are Floats
#check p.x + p.y = 3.0
#eval p.x
#eval p.y
#eval p.x + p.y

def origin : Point := { x:= 0.0, y := 0.0}
#eval origin
#eval origin.x
#eval origin.y

def addPoints (p1 p2 : Point) : Point := { x := p1.x + p2.x, y := p1.y + p2.y}
#eval addPoints p origin
#check (addPoints)

def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)
#eval distance p origin
#check (distance)
