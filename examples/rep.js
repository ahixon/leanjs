function rep(n) {
  let s = "";
  for (let i = 0; i < n; i = i + 1) {
    s = s + "ab";
  }
  return s;
}
rep(5).length;
