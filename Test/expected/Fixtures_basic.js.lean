def x :=
  IO.mkRef (1 + 2)

def y :=
  IO.mkRef "hello"

def z :=
  true

def add a b :=
  return a + b

def i :=
  IO.mkRef 0

def arr :=
  IO.mkRef #[1, 2, 3]

def obj :=
  IO.mkRef { a := 1, b := "two", c := true }

def result :=
  IO.mkRef (add x.get y.get)

def ternary :=
  IO.mkRef (if x.get > 0 then "positive" else "non-positive")
[exit 0]
