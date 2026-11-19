// A small program: classes, closures, generators, destructuring, async.
class Counter {
  #n = 0;
  inc(by = 1) { this.#n += by; return this; }
  get value() { return this.#n; }
}
function* fib() { let [a, b] = [0, 1]; for (;;) { yield a; [a, b] = [b, a + b]; } }
const firstTen = [];
for (const x of fib()) { if (firstTen.length === 10) break; firstTen.push(x); }
const c = new Counter().inc().inc(41);
print(`fib: ${firstTen.join(" ")}`);
print(`counter: ${c.value}`);
print(`json: ${JSON.stringify({ sum: firstTen.reduce((s, x) => s + x, 0), s: "é\u{1F600}" })}`);
(async () => { const v = await Promise.resolve(7); print(`async: ${v * 6}`); })();
