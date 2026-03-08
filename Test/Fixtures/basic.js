var x = 1 + 2;
let y = "hello";
const z = true;

function add(a, b) {
  return a + b;
}

if (x > 2) {
  y = "world";
} else {
  y = "foo";
}

for (var i = 0; i < 10; i++) {
  x = x + i;
}

while (x > 0) {
  x--;
}

var arr = [1, 2, 3];
var obj = { a: 1, b: "two", c: true };

var result = add(x, y);
console.log(result);

var ternary = x > 0 ? "positive" : "non-positive";

try {
  throw "error";
} catch (e) {
  console.log(e);
} finally {
  console.log("done");
}

switch (x) {
  case 0:
    console.log("zero");
    break;
  case 1:
    console.log("one");
    break;
  default:
    console.log("other");
}
