function sign(x) {
  if (x > 0) {
    return "positive";
  } else if (x < 0) {
    return "negative";
  }
  return "zero";
}
const fact = function f(n) {
  return n <= 1 ? 1 : n * f(n - 1);
};
function noReturn(x) {
  x + 1;
}
const result = [sign(5), sign(-2), sign(0), fact(5), noReturn(1) === undefined];
