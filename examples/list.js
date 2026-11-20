function list(n) {
  let s = "";
  for (let i = 0; i < n; i = i + 1) {
    s = s + i + ",";
  }
  return s;
}
list(4);
