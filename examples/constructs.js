function describe(x) {
  switch (typeof x) {
    case "number": return "n:" + x;
    case "string": return "s:" + x;
    default: return "other";
  }
}
function safeDiv(a, b) {
  try {
    if (b === 0) throw new RangeError("div by zero");
    return a / b;
  } catch (e) {
    return e.message;
  } finally {
    calls = calls + 1;
  }
}
var calls = 0;
const point = { x: 1, y: 2, ["z" + 1]: 3, norm() { return this.x * this.x + this.y * this.y; } };
const xs = [1, 2, , ...[3, 4]];
let sum = 0;
for (let i = 0; i < xs.length; i++) { if (i === 2) continue; sum += xs[i]; }
print(describe(sum), describe("hi"), describe(null));
print(safeDiv(6, 3), safeDiv(1, 0), calls);
print(point.norm(), point.z1, xs.length);
