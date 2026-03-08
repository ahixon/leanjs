const makeCounter = () => {
  let count = 0;
  return {
    increment: () => ++count,
    decrement: () => --count,
    getCount: () => count
  };
};

const counter = makeCounter();
counter.increment();
counter.increment();
console.log(counter.getCount());

function compose(f, g) {
  return function(x) {
    return f(g(x));
  };
}

const add1 = x => x + 1;
const mul2 = x => x * 2;
const add1ThenMul2 = compose(mul2, add1);
console.log(add1ThenMul2(3));

var items = [1, 2, 3, 4, 5];
for (var i = 0; i < items.length; i++) {
  console.log(items[i]);
}
