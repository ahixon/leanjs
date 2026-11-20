function check(x) {
  if (x < 0) {
    throw x;
  }
  return x;
}
let r = 0;
try {
  r = check(0 - 7);
} catch (e) {
  r = 0 - e;
}
r;
