[verified] translated by the verified core translator
const double = x => x * 2;
const greet = name => "Hello, " + name;
const max2 = a => b => {
  if (a > b) {
    return a;
  } else {
    return b;
  }
};
const compose = f => g => x => f(g(x));
const result = [double(21), max2(3)(7), compose(double)(double)(5)];

[exit 0]
