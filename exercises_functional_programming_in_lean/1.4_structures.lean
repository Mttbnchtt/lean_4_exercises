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

def Point.modifyBoth (f : Float -> Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
#eval Point.modifyBoth Float.floor origin
#eval Point.modifyBoth Float.floor p

def scale (p : Point) : Point :=
  Point.modifyBoth (λ x => x * 2) p

#eval scale origin
#eval scale p
#eval p.modifyBoth Float.floor

def Point.scale (p : Point) : Point :=
  Point.modifyBoth (λ x => x * 2) p
#eval p.scale
#eval Point.scale p


-- Exercise 1.4.1
structure RectangularPrism where
  width : Float
  height : Float
  depth : Float
deriving Repr

-- Exercise 1.4.2
def volume (p : RectangularPrism) : Float :=
  p.width * p.height * p.depth

-- Exercise 1.4.3
structure Segment where
  start_point : Point
  end_point : Point
deriving Repr

def length (s : Segment) : Float :=
  distance s.start_point s.end_point

def s : Segment := {
    start_point := { x := 1.0, y := 2.0 },
    end_point := { x := 5.0, y := -1.0 }
  }
#eval length s

-- Exercise 1.4.4
-- RectangularPrism, RectangularPrism.mk, RectangularPrism.widt, RectangularPrism.height, RectangularPrism.depth

-- Exercise 1.4.5
-- Hamster, Hamster.mk, Hamster.name, Hamster.fluffy
-- Book, Book.mk, Book.title, Book.author, Book.price
