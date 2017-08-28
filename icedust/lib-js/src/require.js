function requireFor(global, scope){
  function require(name){
    var chosenScope = isRelative(name) ? scope : global;
    var module = resolve(name, chosenScope);
    return module().exports;
  }
  return require;
}

function resolve(name, scope){
  var split = name.split('/');
  var current = scope;
  for(var i = 0 ; i < split.length - 1 ; i++){
    var part = split[i];
    switch(part){
      case '.':
        break;
      case '..':
        current = current.parent;
        break;
      default:
        if(current.children.hasOwnProperty(part)){
          current = current.children[part];
        } else{
          throw new Error('require: could not resolve ' + name);
        }
    }
  }
  var entryName = split[split.length - 1];
  var entry = current.entries[entryName];
  if(entry === undefined){
    throw new Error('require: ' + entryName + ' is not defined in ' + current.path)
  }
  return current.entries[split[split.length - 1]];
}

function lazyModule(module, scope){
  var value;
  return function(){
    if(value === undefined){
      var m = {exports: {}};
      module(scope.require, m);
      value = m;
    }
    return value;
  }
}

function isRelative(path){
  return path.match(/^\./) !== null;
}

function makeRoot(){
  var root = {
    children: {},
    entries: {},
    parent: null,
    path: ''
  };
  root.require = requireFor(root, root);
  return root;
}

function makeScope(name, global, parent){
  var scope = {
    children: {},
    entries: {},
    parent: parent,
    path: (parent.path === global.path ? '' : '/') + name
  };
  scope.require = requireFor(global, scope);
  if(parent !== null && parent !== undefined){
    parent.children[name] = scope;
  }
  return scope;
}

function lazyConst(value){
  var module = { exports: value };
  return function(){
    return module;
  }
}

function eagerlyLoadModules(root){
  function doEager(current){
    var result = {};
    Object.keys(current.entries).forEach(function(entry){
      result[entry] = current.require('./' + entry);
    });
    Object.keys(current.children).forEach(function(child){
      result[child] = doEager(current.children[child])
    });
    return result;
  }
  return doEager(root);
}

module.exports = {
  makeRoot: makeRoot,
  makeScope: makeScope,
  lazyModule: lazyModule,
  lazyConst: lazyConst,
  eagerlyLoadModules: eagerlyLoadModules
};