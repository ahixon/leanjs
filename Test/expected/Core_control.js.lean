def sign x :=
  return "zero"

def fact n :=
  return if n <= 1 then 1 else n * f (n - 1)

def noReturn x :=
  x + 1

def result :=
  #[sign 5, sign (-2), sign 0, fact 5, noReturn 1 == ()]
[exit 0]
