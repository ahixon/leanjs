structure Point where
  x : Float
  y : Float

def origin : Point :=
  { x := 0, y := 0 }

def translate (p : Point) (dx : Float) (dy : Float) : Point :=
  { x := p.x + dx, y := p.y + dy }

def distance (p : Point) : Float :=
  p.x * p.x + p.y * p.y

structure Color where
  r : Float
  g : Float
  b : Float
