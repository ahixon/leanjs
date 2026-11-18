def add a b :=
  a + b

def inc x :=
  add x 1

def compose f g :=
  fun x => f (g x)

def double x :=
  x * 2

def clamp lo hi x :=
  if x < lo then lo else if x > hi then hi else x

def neg :=
  -3

def guard x :=
  x > 0 && 100 / x

def orDefault s :=
  s || "default"

def lazy :=
  false && missing 1

def point :=
  { x := inc 41, y := compose double inc 4 }

def result :=
  #[point, add (inc 1) 2, clamp 0 10 neg, clamp 0 10 99, guard 4, guard neg, orDefault "", orDefault "given", lazy, #[true, !true], { n := -0.500000, s := "hi " + "there" }]
[exit 0]
