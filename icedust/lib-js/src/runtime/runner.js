var loadModule = require('./loadModule');
var _ = require('lodash');
var runtime = require('./pixiedust/runtime');
// var native = require('././index');

function runner(program){
  var module = loadModule(program);
  // if(module.Component !== undefined){
  //   _.assign(module.Component, native);
  // }
  var state = module.emptyState;
  var init = module.init(state);
  var store = runtime.makeStore(module.reducer, init.state);
  var execute = module.execute(store, init.ids);
  for(var i = 0 ; i < execute.length ; i++){
    console.log(valueToString(execute[i].value));
  }
}

function valueToString(value){
  if(_.isArray(value)){
    return '[' + _.toString(value) + ']';
  } else if(_.isPlainObject(value)){
    return JSON.stringify(value);
  } else{
    return '' + value;
  }
}

module.exports = runner;