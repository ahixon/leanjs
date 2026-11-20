function add(a, b) {
  return a + b;
}
function sumAdd(n) {
  let s = 0;
  for (let i = 0; i < n; i = i + 1) {
    s = add(s, i);
  }
  return s;
}
sumAdd(10);
