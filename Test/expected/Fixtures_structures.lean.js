[unverified] outside the verified core (unsupported: only `def` declarations); using the legacy translator
class Point {
  constructor(x, y) {
    this.x = x;
    this.y = y;
  }
}
function origin() {
  { x: 0, y: 0 };
}
function translate(p, dx, dy) {
  { x: p.x + dx, y: p.y + dy };
}
function distance(p) {
  p.x * p.x + p.y * p.y;
}
class Color {
  constructor(r, g, b) {
    this.r = r;
    this.g = g;
    this.b = b;
  }
}

[exit 0]
