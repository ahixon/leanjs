function add(a, b) {
  return a + b;
}
function max(a, b) {
  if (a > b) return a;
  return b;
}
let total = 0;
for (let i = 0; i < 5; i++) total = add(total, i);
print(max(total, 7));
