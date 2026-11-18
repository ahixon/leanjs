def makeCounter :=
  do
    let count ← IO.mkRef 0
    return { increment := fun => do
      count.set (count.get.get + 1)
      count.get.get
, decrement := fun => do
      count.set (count.get.get - 1)
      count.get.get
, getCount := fun => do
      count.get.get
 }


def counter :=
  makeCounter

def compose f g :=
  return fun x => return f (g x)

def add1 x :=
  x + 1

def mul2 x :=
  x * 2

def add1ThenMul2 :=
  compose mul2 add1

def items :=
  IO.mkRef #[1, 2, 3, 4, 5]

def i :=
  IO.mkRef 0
[exit 0]
