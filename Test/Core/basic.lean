def double (x : Float) : Float := x * 2

def greet (name : String) : String := "Hello, " ++ name

def max2 (a : Float) (b : Float) : Float := if a > b then a else b

def compose (f : Float → Float) (g : Float → Float) (x : Float) : Float := f (g x)

def result := #[double 21, max2 3 7, compose double double 5]
