function sum(collection){
  var total = 0;
  for(var i = 0 ; i < collection.length ; i++){
    total += collection[i];
  }
  return total;
}

function min(collection){
  var minimum = null;
  for(var i = 0 ; i < collection.length ; i++){
    if(minimum == null || collection[i] < minimum){
      minimum = collection[i];
    }
  }
  return minimum;
}

function max(collection){
  var minimum = null;
  for(var i = 0 ; i < collection.length ; i++){
    if(minimum == null || collection[i] > minimum){
      minimum = collection[i];
    }
  }
  return minimum;
}

function avg(collection){
  if(collection.length == 0){
    return null;
  }
  return sum(collection) / collection.length;
}

function concat(c1, c2){
  return c1.concat(c2);
}

function count(collection){
  return collection.length;
}

function conj(collection){
  for(var i = 0 ; i < collection.length ; i++){
    if(collection[i] == false){
      return false;
    }
  }
  return true;
}

function disj(collection){
  for(var i = 0 ; i < collection.length ; i++){
    if(collection[i] == true){
      return true;
    }
  }
  return collection.isEmpty();
}


function dateToString(d) {
	var year = d.getFullYear();
	var month = d.getMonth() + 1;
	var dayOfMonth = d.getDate();
	var hours = d.getHours();
	var minutes = d.getMinutes();
	var seconds = d.getSeconds();
	var result = year + '-' + padZero(month) + '-' + padZero(dayOfMonth) + ' ' + padZero(hours) + ':' + padZero(minutes) + ':' + padZero(seconds);
	return result
}

function padZero(n) {
	return (n < 10 ? '0' : '') + n
}

module.exports = {
  sum: sum,
  min: min,
  max: max,
  avg: avg,
  concat: concat,
  count: count,
  conj: conj,
  disj: disj,
  dateToString: dateToString
};