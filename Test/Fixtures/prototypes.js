function Person(name, age) {
  this.name = name;
  this.age = age;
}

Person.prototype.greet = function() {
  return "Hi, I'm " + this.name;
};

var p = new Person("Alice", 30);
console.log(p.greet());

var obj = {
  get value() {
    return this._value;
  },
  set value(v) {
    this._value = v;
  }
};

obj.value = 42;
console.log(obj.value);

var nested = {
  a: {
    b: {
      c: 1
    }
  }
};

var c = nested.a.b.c;
var arr = [[1, 2], [3, 4]];
var first = arr[0][1];

var x = typeof p === "object" ? "yes" : "no";
var y = void 0;
var z = !true;
var w = ~0xFF;

do {
  x = x + "!";
} while (x.length < 5);

for (var key in obj) {
  console.log(key);
}
