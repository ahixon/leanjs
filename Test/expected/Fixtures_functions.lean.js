[verified] translated by the verified core translator
const identity = x => x;
const compose = f => g => x => f(g(x));
const apply = f => x => f(x);
const makeAdder = n => x => x + n;
const twice = f => x => f(f(x));

[exit 0]
