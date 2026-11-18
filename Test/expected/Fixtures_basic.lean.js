[unverified] outside the verified core (unsupported: recursive definition `factorial`); using the legacy translator
function add(x, y) {
  x + y;
}
function greet(name) {
  "Hello, " + name + "!";
}
function pi() {
  3.141590;
}
function isPositive(n) {
  n > 0;
}
function max(a, b) {
  if (a > b) {
    a;
  } else {
    b;
  }
}
function factorial(n) {
  if (n <= 1) {
    1;
  } else {
    n * factorial(n - 1);
  }
}

[exit 0]
