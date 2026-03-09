def countdown (n : Float) := do
  let mut i := n
  while i > 0 do
    i := i - 1
  return i

def sumArray (arr : Array Float) := do
  let mut total := 0
  for x in arr do
    total := total + x
  return total

def safeDivide (a : Float) (b : Float) := do
  if b == 0 then
    throw "division by zero"
  return a / b

def tryCatch_ := do
  try
    let result := safeDivide 10 0
    return result
  catch e =>
    return 0
