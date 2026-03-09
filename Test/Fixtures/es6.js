const greeting = `Hello, ${name}!`;
const multi = `line1\nline2`;
const [a, b, c] = [1, 2, 3];
const {x, y} = point;
import {foo} from "./utils";
export function helper(x) { return x + 1; }
async function fetchData(url) {
  const response = await fetch(url);
  return response;
}
function* range(n) {
  let i = 0;
  while (i < n) { yield i; i = i + 1; }
}
