export function sum(collection){
  return collection.reduce((sum, x) => sum + x, 0)
}

export function min(collection){
  let minimum = null;
  for(let x of collection){
    if(minimum == null || x < minimum){
      minimum = x;
    }
  }
    return minimum;
}

export function max(collection){
  let minimum = null;
  for(let x of collection){
    if(minimum == null || x > minimum){
      minimum = x;
    }
  }
  return minimum;
}

export function avg(collection){
  if(collection.length == 0){
    return null;
  }
  return sum(collection) / collection.length;
}

export function concat(c1, c2){
  return c1.concat(c2);
}

export function count(collection){
  return collection.length;
}

export function conj(collection){
  for(let x of collection){
    if(x == false){
      return false;
    }
  }
  return true;
}

export function disj(collection){
  for(let x of collection){
    if(x == true){
      return true;
    }
  }
  return collection.isEmpty();
}