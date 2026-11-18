def makeAdder n :=
  fun x => x + n

def add5 :=
  makeAdder 5

def apply f x :=
  return f x

def twice f :=
  fun x => f (f x)

def result :=
  { a := apply add5 10, b := makeAdder "x" "y", c := twice add5 0 }
[exit 0]
