function make() {
  let n = 0;
  return function () {
    n = n + 1;
    return n;
  };
}
let c = make();
c();
c();
