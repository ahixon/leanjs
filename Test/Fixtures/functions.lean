def identity x := x

def compose f g x := f (g x)

def apply (f : Float → Float) (x : Float) : Float :=
  f x

def makeAdder (n : Float) : Float → Float :=
  fun x => x + n

def twice f x := f (f x)
