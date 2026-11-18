def add a b :=
  a + b

def square x :=
  x * x

def sumOfSquares a b :=
  let s := add (square a) (square b)
  return s

def result :=
  #[sumOfSquares 3 4, add "a" "b", typeof add, !true, 7 % 3]
[exit 0]
