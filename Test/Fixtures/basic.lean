def add (x : Float) (y : Float) : Float :=
  x + y

def greet (name : String) : String :=
  "Hello, " ++ name ++ "!"

def pi : Float := 3.14159

def isPositive (n : Float) : Bool :=
  n > 0

def max (a : Float) (b : Float) : Float :=
  if a > b then a else b

def factorial (n : Float) : Float :=
  if n <= 1 then 1 else n * factorial (n - 1)
