function inc() {
  this.n = this.n + 1;
  return this.n;
}
let p = { inc: inc };
let o = { __proto__: p, n: 0 };
o.inc();
o.inc();
