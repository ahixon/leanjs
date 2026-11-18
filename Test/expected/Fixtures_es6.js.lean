def greeting :=
  "" ++ "Hello, " ++ name ++ "!"

def multi :=
  "" ++ "line1\\nline2"

def __tmp0 :=
  #[1, 2, 3]

def __tmp1 :=
  point

def helper x :=
  return x + 1

def fetchData url :=
  let response := let result ← fetch url
  return response

def range n :=
  do
    let i ← IO.mkRef 0
    while i.get.get < n do
      i.get.get
      i.set (i.get.get + 1)

[exit 0]
