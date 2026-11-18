def Person name age :=
  do
    self.name.set name
    name
    self.age.set age
    age


def p :=
  IO.mkRef (Person "Alice" 30)

def obj :=
  IO.mkRef { value := fun => return self._value, value := fun v => do
    self._value.set v
    v
 }

def nested :=
  IO.mkRef { a := { b := { c := 1 } } }

def c :=
  IO.mkRef nested.a.b.c

def arr :=
  IO.mkRef #[#[1, 2], #[3, 4]]

def first :=
  IO.mkRef arr[0]![1]!

def x :=
  IO.mkRef (if typeof p == "object" then "yes" else "no")

def y :=
  IO.mkRef ()

def z :=
  IO.mkRef (!true)

def w :=
  IO.mkRef (~~~255)

def key :=
  ()
[exit 0]
