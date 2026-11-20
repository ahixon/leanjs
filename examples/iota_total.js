function total(a) {
  let s = 0;
  for (let i = 0; i < a.length; i = i + 1) {
    s = s + a[i];
  }
  return s;
}
function iota(n) {
  let a = [];
  for (let i = 0; i < n; i = i + 1) {
    a[i] = i;
  }
  return a;
}
let b = iota(5);
total(b);
