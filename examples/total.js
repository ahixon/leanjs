function total(a) {
  let s = 0;
  for (let i = 0; i < a.length; i = i + 1) {
    s = s + a[i];
  }
  return s;
}
total([3, 4, 5]);
