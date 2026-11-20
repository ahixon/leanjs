function inc() {
  this.n = this.n + 1;
  return this.n;
}
let o = { n: 0, inc: inc };
o.inc();
o.inc();
