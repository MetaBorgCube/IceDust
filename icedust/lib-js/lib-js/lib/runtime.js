var EMPTY_ARRAY = [];

var uniqueId = 0;
function generateUniqueId(){ //simple number generator
  return "" + uniqueId++;
}



module.exports = {
  EMPTY_ARRAY: EMPTY_ARRAY,
  generateUniqueId: generateUniqueId
};
