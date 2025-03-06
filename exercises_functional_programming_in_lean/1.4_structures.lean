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
#check (Point.mk)
#check Point.mk 1.0 2.0
#eval Point.mk 1.0 2.0
def p := Point.mk 1.0 2.0
#check p
#check p.x
#check p.y
#check p.x + p.y  -- Lean infers that p.x and p.y are Floats
#check p.x + p.y = 3.0
#eval p.x
#eval Point.x p
#eval p.y
#eval p.x + p.y
#check Point.x
#check (Point.x)

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
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0}
#eval distance { x := 1, y := 2 } { x := 5, y := -1}
#eval distance ({ x := 1.0, y := 2.0 } : Point) ({ x := 5.0, y := -1.0} : Point)

def zeroX (p : Point) : Point := { x := 0.0, y := p.y}
#eval zeroX p
#eval zeroX ({ x := 5.0, y := 2.0 } : Point)

def zeroX' (p : Point) : Point := { p with x := 0.0}
#eval zeroX' p
#eval p

#eval "A".append "B"
#eval "A" ++ "B"
#eval "A".length
#eval "A".length + "B".length
#eval String.append "A" "B"

def Point.modifyBoth
