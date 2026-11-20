function total(a) {
  let s = 0;
  for (let i = 0; i < a.length; i = i + 1) {
    s = s + a[i];
  }
  return s;
}
function double(a) {
  for (let i = 0; i < a.length; i = i + 1) {
    a[i] = a[i] + a[i];
  }
}
let b = [3, 4, 5];
double(b);
total(b);
