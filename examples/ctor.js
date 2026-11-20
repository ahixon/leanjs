function inc() {
  this.n = this.n + 1;
  return this.n;
}
function Counter() {
  this.n = 0;
}
Counter.prototype.inc = inc;
let c = new Counter();
c.inc();
c.inc();
