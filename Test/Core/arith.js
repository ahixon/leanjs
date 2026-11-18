const add = (a, b) => a + b;
const square = (x) => x * x;
function sumOfSquares(a, b) {
  const s = add(square(a), square(b));
  return s;
}
const result = [sumOfSquares(3, 4), add("a", "b"), typeof add, !true, 7 % 3];
