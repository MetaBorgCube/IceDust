
export const EMPTY_ARRAY = [];

let uniqueId = 0;
export function generateUniqueId(){ //simple number generator
  return "" + uniqueId++;
}
