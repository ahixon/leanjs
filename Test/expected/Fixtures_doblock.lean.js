[unverified] outside the verified core (unsupported: recursive definition `tryCatch_`); using the legacy translator
function countdown(n) {
  let i = n;
  while (i > 0) {
    i = i - 1;
  }
  return i;
}
function sumArray(arr) {
  let total = 0;
  const x = undefined;
  return total;
}
function safeDivide(a, b) {
  if (b === 0) {
    throw "division by zero";
  }
  return a / b;
}
function tryCatch_() {
  try {
    const result = safeDivide(10, 0);
    return result;
  } catch (e) {
    return 0;
  }
}

[exit 0]
